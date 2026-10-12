import AdaptiveOrthogonalRigidity.OneCoordinateFiber

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- A deterministic split of original coordinates; neither factors nor their
parameters depend on the sampled values. -/
def splitAssignmentEquiv {ι κ ν : Type*} (e : (ι ⊕ κ) ≃ ν) :
    ((ι → Bool) × (κ → Bool)) ≃ (ν → Bool) where
  toFun x := fun k => Sum.elim x.1 x.2 (e.symm k)
  invFun x := (fun i => x (e (Sum.inl i)), fun j => x (e (Sum.inr j)))
  left_inv x := by ext k <;> simp
  right_inv x := by
    funext k
    have h := e.apply_symm_apply k
    cases he : e.symm k <;> simp_all

theorem cubeWeight_splitAssignment {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]
    (p : ν → unitInterval) (e : (ι ⊕ κ) ≃ ν) (x : ι → Bool) (r : κ → Bool) :
    cubeWeight p (splitAssignmentEquiv e (x, r)) =
      cubeWeight (fun i => p (e (Sum.inl i))) x *
      cubeWeight (fun j => p (e (Sum.inr j))) r := by
  unfold cubeWeight
  rw [← e.prod_comp (fun k => bitWeight (p k : ℝ) (splitAssignmentEquiv e (x, r) k))]
  simp [Fintype.prod_sum_type, splitAssignmentEquiv]

/-- Finite conditional summation on an arbitrary predetermined coordinate split.
The bound is proved for every conditioning value, under the unchanged left law. -/
theorem cube_event_le_of_split_bound {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]
    (p : ν → unitInterval) (e : (ι ⊕ κ) ≃ ν) (E : Set (ν → Bool)) (C : ℝ)
    (hbound : ∀ r : κ → Bool,
      (cubeMeasure (fun i => p (e (Sum.inl i)))).real
        {x | splitAssignmentEquiv e (x, r) ∈ E} ≤ C) :
    (cubeMeasure p).real E ≤ C := by
  rw [cubeMeasure_real_eq_sum]
  rw [← (splitAssignmentEquiv e).sum_comp (fun x => if x ∈ E then cubeWeight p x else 0)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [cubeWeight_splitAssignment]
  let pl := fun i => p (e (Sum.inl i))
  let pr := fun j => p (e (Sum.inr j))
  calc
    _ = ∑ r : κ → Bool, cubeWeight pr r *
        (cubeMeasure pl).real {x | splitAssignmentEquiv e (x, r) ∈ E} := by
      apply Finset.sum_congr rfl
      intro r _
      rw [cubeMeasure_real_eq_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp only [Set.mem_ofPred_eq]
      split_ifs <;> ring
    _ ≤ ∑ r : κ → Bool, cubeWeight pr r * C := by
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_left (hbound r) (cubeWeight_nonneg pr r)
    _ = C := by rw [← Finset.sum_mul, cubeWeight_sum]; ring

def columnIndexEquiv {ι κ : Type*} [DecidableEq κ] (j : κ) :
    (ι ⊕ (ι × RemainingCoordinates j)) ≃ (ι × κ) where
  toFun x := match x with
    | Sum.inl i => (i, j)
    | Sum.inr q => (q.1, q.2.val)
  invFun q := if h : q.2 = j then Sum.inl q.1 else Sum.inr (q.1, ⟨q.2, h⟩)
  left_inv x := by
    cases x with
    | inl i => simp
    | inr q => simp [q.2.property]
  right_inv q := by
    rcases q with ⟨i, k⟩
    dsimp
    split_ifs <;> simp_all

theorem splitAssignment_selected_column {ι κ : Type*} [DecidableEq κ] (j : κ)
    (x : ι → Bool) (r : ι × RemainingCoordinates j → Bool) :
    (fun i => splitAssignmentEquiv (columnIndexEquiv j) (x, r) (i, j)) = x := by
  funext i
  simp [splitAssignmentEquiv, columnIndexEquiv]

theorem splitAssignment_other_column {ι κ : Type*} [DecidableEq κ] (j : κ)
    (x : ι → Bool) (r : ι × RemainingCoordinates j → Bool) (k : RemainingCoordinates j) :
    (fun i => splitAssignmentEquiv (columnIndexEquiv j) (x, r) (i, k.val)) =
      fun i => r (i, k) := by
  funext i
  simp [splitAssignmentEquiv, columnIndexEquiv, k.property]

theorem split_column_sum {ι κ T : Type*} [Fintype κ] [DecidableEq κ] [AddCommMonoid T]
    (j : κ) (x : ι → Bool) (r : ι × RemainingCoordinates j → Bool) (f : (ι → Bool) → T) :
    (∑ k : κ, f (fun i => splitAssignmentEquiv (columnIndexEquiv j) (x, r) (i, k))) =
      f x + ∑ k : RemainingCoordinates j, f (fun i => r (i, k)) := by
  rw [← (singleIndexEquiv j).sum_comp
    (fun k => f (fun i => splitAssignmentEquiv (columnIndexEquiv j) (x, r) (i, k)))]
  simp [Fintype.sum_sum_type, singleIndexEquiv,
    splitAssignment_selected_column, splitAssignment_other_column]

/-- Convolution cannot increase a uniform atom bound, proved directly in the
original heterogeneous rectangular bit law by fixing all other columns. -/
theorem cube_column_sum_atom_le {ι κ T : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [AddCommGroup T]
    (p : ι × κ → unitInterval) (j : κ) (f : (ι → Bool) → T) (C : ℝ)
    (hbound : ∀ z, (cubeMeasure (fun i => p (i, j))).real {x | f x = z} ≤ C)
    (z : T) :
    (cubeMeasure p).real {X | ∑ k, f (fun i => X (i, k)) = z} ≤ C := by
  apply cube_event_le_of_split_bound p (columnIndexEquiv j) _ C
  intro r
  change (cubeMeasure (fun i => p (i, j))).real
    {x | (∑ k, f (fun i => splitAssignmentEquiv (columnIndexEquiv j) (x, r) (i, k))) = z} ≤ C
  simpa only [split_column_sum, ← eq_sub_iff_add_eq] using
      hbound (z - ∑ k : RemainingCoordinates j, f (fun i => r (i, k)))

end AdaptiveOrthogonalRigidity
