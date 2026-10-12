import AdaptiveOrthogonalRigidity.FiniteProbability

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

abbrev OtherCoordinates {ι : Type*} (i j : ι) := {k : ι // k ≠ i ∧ k ≠ j}

def patchTwo {ι : Type*} [DecidableEq ι] (i j : ι)
    (r : OtherCoordinates i j → Bool) (a b : Bool) (k : ι) : Bool :=
  if hi : k = i then a else if hj : k = j then b else r ⟨k, hi, hj⟩

def pairAssignmentEquiv {ι : Type*} [DecidableEq ι] (i j : ι) (hij : i ≠ j) :
    ((OtherCoordinates i j → Bool) × (Bool × Bool)) ≃ (ι → Bool) where
  toFun x := patchTwo i j x.1 x.2.1 x.2.2
  invFun x := (fun k => x k.val, (x i, x j))
  left_inv x := by
    rcases x with ⟨r, a, b⟩
    apply Prod.ext
    · funext k
      simp [patchTwo, k.property.1, k.property.2]
    · apply Prod.ext <;> simp [patchTwo, Ne.symm hij]
  right_inv x := by
    funext k
    by_cases hi : k = i
    · subst k
      simp [patchTwo]
    · by_cases hj : k = j
      · subst k
        simp [patchTwo, hi]
      · simp [patchTwo, hi, hj]

def selectedIndexEquiv {ι : Type*} [DecidableEq ι] (i j : ι) (hij : i ≠ j) :
    (Bool ⊕ OtherCoordinates i j) ≃ ι where
  toFun x := match x with
    | Sum.inl true => i
    | Sum.inl false => j
    | Sum.inr k => k.val
  invFun k := if hi : k = i then Sum.inl true
    else if hj : k = j then Sum.inl false else Sum.inr ⟨k, hi, hj⟩
  left_inv x := by
    cases x with
    | inl b => cases b <;> simp [Ne.symm hij]
    | inr k => simp [k.property.1, k.property.2]
  right_inv k := by
    dsimp
    split_ifs <;> simp_all

theorem cubeWeight_pairAssignment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → unitInterval) (i j : ι) (hij : i ≠ j)
    (r : OtherCoordinates i j → Bool) (ab : Bool × Bool) :
    cubeWeight p (pairAssignmentEquiv i j hij (r, ab)) =
      cornerWeight (p i : ℝ) (p j : ℝ) ab *
        cubeWeight (fun k : OtherCoordinates i j => p k.val) r := by
  unfold cubeWeight
  rw [← (selectedIndexEquiv i j hij).prod_comp
    (fun k => bitWeight (p k : ℝ) (pairAssignmentEquiv i j hij (r, ab) k))]
  rw [Fintype.prod_sum_type, Fintype.prod_bool]
  simp [selectedIndexEquiv, pairAssignmentEquiv, patchTwo,
    Ne.symm hij, cornerWeight]
  left
  apply Finset.prod_congr rfl
  intro k _
  simp [k.property.1, k.property.2]

theorem cubeWeight_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → unitInterval) (x : ι → Bool) : 0 ≤ cubeWeight p x := by
  rw [← cubeMeasure_real_singleton]
  exact measureReal_nonneg

/-- Original product-law fiber bound at any two prescribed distinct coordinates.
The function can depend arbitrarily on all coordinates; the two-bit face
condition is tested separately at every assignment of the other coordinates. -/
theorem cube_atom_le_of_pair_missing {ι T : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → unitInterval) (i j : ι) (hij : i ≠ j) {α : ℝ} (hα : 0 ≤ α)
    (hi : α ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ 1 - α)
    (hj : α ≤ (p j : ℝ) ∧ (p j : ℝ) ≤ 1 - α)
    (f : (ι → Bool) → T) (z : T)
    (hmissing : ∀ r : OtherCoordinates i j → Bool,
      ∃ ab : Bool × Bool, f (pairAssignmentEquiv i j hij (r, ab)) ≠ z) :
    (cubeMeasure p).real {x | f x = z} ≤ 1 - α ^ 2 := by
  rw [cubeMeasure_real_eq_sum]
  simp only [Set.mem_ofPred_eq]
  rw [← (pairAssignmentEquiv i j hij).sum_comp
    (fun x => if f x = z then cubeWeight p x else 0)]
  rw [Fintype.sum_prod_type]
  simp only [cubeWeight_pairAssignment]
  let pr := fun k : OtherCoordinates i j => p k.val
  calc
    _ = ∑ r : OtherCoordinates i j → Bool, cubeWeight pr r *
        ∑ ab : Bool × Bool,
          if f (pairAssignmentEquiv i j hij (r, ab)) = z
          then cornerWeight (p i : ℝ) (p j : ℝ) ab else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ab _
      split_ifs <;> ring
    _ ≤ ∑ r : OtherCoordinates i j → Bool, cubeWeight pr r * (1 - α ^ 2) := by
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_left
        (two_bit_atom_le hα hi hj (fun ab => f (pairAssignmentEquiv i j hij (r, ab)))
          z (hmissing r)) (cubeWeight_nonneg pr r)
    _ = 1 - α ^ 2 := by rw [← Finset.sum_mul, cubeWeight_sum]; ring

/-- Predicate-valued version, allowing residue classes or any other event. -/
theorem cube_event_le_of_pair_missing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → unitInterval) (i j : ι) (hij : i ≠ j) {α : ℝ} (hα : 0 ≤ α)
    (hi : α ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ 1 - α)
    (hj : α ≤ (p j : ℝ) ∧ (p j : ℝ) ≤ 1 - α) (E : Set (ι → Bool))
    (hmissing : ∀ r : OtherCoordinates i j → Bool,
      ∃ ab : Bool × Bool, pairAssignmentEquiv i j hij (r, ab) ∉ E) :
    (cubeMeasure p).real E ≤ 1 - α ^ 2 := by
  have h := cube_atom_le_of_pair_missing p i j hij hα hi hj
    (fun x => decide (x ∈ E)) true (by
      intro r
      obtain ⟨ab, hab⟩ := hmissing r
      exact ⟨ab, by simpa using hab⟩)
  simpa using h

end AdaptiveOrthogonalRigidity
