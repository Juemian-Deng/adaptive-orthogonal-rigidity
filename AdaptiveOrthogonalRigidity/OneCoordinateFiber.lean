import AdaptiveOrthogonalRigidity.TwoCoordinateFiber

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

abbrev RemainingCoordinates {ι : Type*} (i : ι) := {k : ι // k ≠ i}

def patchOne {ι : Type*} [DecidableEq ι] (i : ι)
    (r : RemainingCoordinates i → Bool) (a : Bool) (k : ι) : Bool :=
  if hi : k = i then a else r ⟨k, hi⟩

def singleAssignmentEquiv {ι : Type*} [DecidableEq ι] (i : ι) :
    ((RemainingCoordinates i → Bool) × Bool) ≃ (ι → Bool) where
  toFun x := patchOne i x.1 x.2
  invFun x := (fun k => x k.val, x i)
  left_inv x := by
    rcases x with ⟨r, a⟩
    apply Prod.ext
    · funext k; simp [patchOne, k.property]
    · simp [patchOne]
  right_inv x := by
    funext k
    by_cases hi : k = i <;> simp [patchOne, hi]

def singleIndexEquiv {ι : Type*} [DecidableEq ι] (i : ι) :
    (Unit ⊕ RemainingCoordinates i) ≃ ι where
  toFun x := match x with
    | Sum.inl _ => i
    | Sum.inr k => k.val
  invFun k := if hi : k = i then Sum.inl () else Sum.inr ⟨k, hi⟩
  left_inv x := by
    cases x with
    | inl u => cases u; simp
    | inr k => simp [k.property]
  right_inv k := by
    dsimp
    split_ifs <;> simp_all

theorem cubeWeight_singleAssignment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → unitInterval) (i : ι)
    (r : RemainingCoordinates i → Bool) (a : Bool) :
    cubeWeight p (singleAssignmentEquiv i (r, a)) =
      bitWeight (p i : ℝ) a * cubeWeight (fun k : RemainingCoordinates i => p k.val) r := by
  unfold cubeWeight
  rw [← (singleIndexEquiv i).prod_comp
    (fun k => bitWeight (p k : ℝ) (singleAssignmentEquiv i (r, a) k))]
  rw [Fintype.prod_sum_type]
  simp [singleIndexEquiv, singleAssignmentEquiv, patchOne]
  left
  apply Finset.prod_congr rfl
  intro k _
  simp [k.property]

theorem one_bit_atom_le {T : Type*} {α p : ℝ} (hα : 0 ≤ α)
    (hp : α ≤ p ∧ p ≤ 1 - α) (f : Bool → T) (z : T)
    (hmissing : ∃ a, f a ≠ z) :
    (∑ a, if f a = z then bitWeight p a else 0) ≤ 1 - α := by
  obtain ⟨a, ha⟩ := hmissing
  have hw (b : Bool) : 0 ≤ bitWeight p b := hα.trans (bitWeight_lower hp b)
  have hsum : ∑ b, bitWeight p b = 1 := by simp [bitWeight]
  have h := finite_atom_le_of_missing (bitWeight p) f z a hw hsum ha
  linarith [bitWeight_lower hp a]

/-- The original heterogeneous product law, disintegrated at one prescribed bit. -/
theorem cube_atom_le_of_single_missing {ι T : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → unitInterval) (i : ι) {α : ℝ} (hα : 0 ≤ α)
    (hi : α ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ 1 - α)
    (f : (ι → Bool) → T) (z : T)
    (hmissing : ∀ r : RemainingCoordinates i → Bool,
      ∃ a : Bool, f (singleAssignmentEquiv i (r, a)) ≠ z) :
    (cubeMeasure p).real {x | f x = z} ≤ 1 - α := by
  rw [cubeMeasure_real_eq_sum]
  simp only [Set.mem_ofPred_eq]
  rw [← (singleAssignmentEquiv i).sum_comp
    (fun x => if f x = z then cubeWeight p x else 0)]
  rw [Fintype.sum_prod_type]
  simp only [cubeWeight_singleAssignment]
  let pr := fun k : RemainingCoordinates i => p k.val
  calc
    _ = ∑ r : RemainingCoordinates i → Bool, cubeWeight pr r *
        ∑ a : Bool, if f (singleAssignmentEquiv i (r, a)) = z
          then bitWeight (p i : ℝ) a else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> ring
    _ ≤ ∑ r : RemainingCoordinates i → Bool, cubeWeight pr r * (1 - α) := by
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_left
        (one_bit_atom_le hα hi (fun a => f (singleAssignmentEquiv i (r, a)))
          z (hmissing r)) (cubeWeight_nonneg pr r)
    _ = 1 - α := by rw [← Finset.sum_mul, cubeWeight_sum]; ring

end AdaptiveOrthogonalRigidity
