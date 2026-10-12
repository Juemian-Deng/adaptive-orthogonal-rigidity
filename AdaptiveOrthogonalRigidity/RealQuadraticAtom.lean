import AdaptiveOrthogonalRigidity.QuadraticAlgebra
import AdaptiveOrthogonalRigidity.NoncoordinateComponents

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Congruence modulo one, with a real representative of the residue class. -/
def ModOneEq (x z : ℝ) : Prop := ∃ k : ℤ, x - z = k

theorem unit_noncoordinate_two_nonzero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ)
    (hnorm : ∑ i, u i ^ 2 = 1) (hnon : ¬ IsSignedCoordinate u) :
    ∃ i j, i ≠ j ∧ u i ≠ 0 ∧ u j ≠ 0 := by
  have hex : ∃ i, u i ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hnorm
  obtain ⟨i, hi⟩ := hex
  by_contra h
  push Not at h
  have hz : ∀ j, j ≠ i → u j = 0 := by
    intro j hji
    exact h i j (Ne.symm hji) hi
  have hs : u i ^ 2 = 1 := by
    rw [← hnorm]
    symm
    apply Finset.sum_eq_single i
    · intro j _ hji; simp [hz j hji]
    · simp
  apply hnon
  refine ⟨i, ?_, hz⟩
  rcases mul_self_eq_one_iff.mp (by nlinarith : u i * u i = 1) with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem unit_pair_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (hnorm : ∑ i, u i ^ 2 = 1) (i j : ι) (hij : i ≠ j) :
    u i ^ 2 + u j ^ 2 ≤ 1 := by
  have hsub : ({i, j} : Finset ι) ⊆ Finset.univ := Finset.subset_univ _
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => sq_nonneg (u k))
  simpa [Finset.sum_pair hij, hnorm] using h

theorem unit_pair_exhausts {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (hnorm : ∑ i, u i ^ 2 = 1) (i j : ι) (hij : i ≠ j)
    (hpair : u i ^ 2 + u j ^ 2 = 1) (k : ι) (hki : k ≠ i) (hkj : k ≠ j) :
    u k = 0 := by
  have hsub : ({i, j, k} : Finset ι) ⊆ Finset.univ := Finset.subset_univ _
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ => sq_nonneg (u l))
  have hle : u i ^ 2 + u j ^ 2 + u k ^ 2 ≤ 1 := by
    simpa [Finset.sum_insert, hij, Ne.symm hki, Ne.symm hkj, hnorm, add_assoc] using h
  nlinarith [sq_nonneg (u k)]

/-- Four squared values cannot all have the same residue. The extremal
|2ab|=1 case uses the unit-vector exhaustion condition to force t=0. -/
theorem four_squares_missing_mod_one (t a b z : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ^ 2 + b ^ 2 ≤ 1) (ht : a ^ 2 + b ^ 2 = 1 → t = 0) :
    ∃ ab : Bool × Bool,
      ¬ ModOneEq ((t + a * bitValue ab.1 + b * bitValue ab.2) ^ 2) z := by
  by_contra h
  push Not at h
  obtain ⟨k00, h00⟩ := h (false, false)
  obtain ⟨k10, h10⟩ := h (true, false)
  obtain ⟨k01, h01⟩ := h (false, true)
  obtain ⟨k11, h11⟩ := h (true, true)
  simp only [bitValue, Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero, mul_one] at h00 h10 h01 h11
  let m : ℤ := k11 - k10 - k01 + k00
  have hm : (m : ℝ) = 2 * a * b := by
    dsimp [m]
    push_cast
    nlinarith [square_mixed_difference t a b]
  have hml : (-1 : ℝ) ≤ (m : ℝ) := by nlinarith [sq_nonneg (a + b)]
  have hmu : (m : ℝ) ≤ 1 := by nlinarith [sq_nonneg (a - b)]
  have hml' : (-1 : ℤ) ≤ m := by exact_mod_cast hml
  have hmu' : m ≤ (1 : ℤ) := by exact_mod_cast hmu
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0] at hm
    norm_num at hm
    exact hm.elim ha hb
  have hmabs : m = -1 ∨ m = 1 := by omega
  have hpair : a ^ 2 + b ^ 2 = 1 := by
    rcases hmabs with hm1 | hm1 <;> rw [hm1] at hm <;>
      norm_num at hm <;> nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  have hsqa : a ^ 2 = 1 / 2 := by
    rcases hmabs with hm1 | hm1 <;> rw [hm1] at hm <;> norm_num at hm
    · have heq : a = -b := by nlinarith [sq_nonneg (a + b)]
      nlinarith
    · have heq : a = b := by nlinarith [sq_nonneg (a - b)]
      nlinarith
  have ht0 := ht hpair
  have hk : ((k10 - k00 : ℤ) : ℝ) = 1 / 2 := by
    push_cast
    rw [ht0] at h00 h10
    norm_num at h00 h10
    linarith
  have hkpos : (0 : ℤ) < k10 - k00 := by exact_mod_cast (show (0 : ℝ) < (k10 - k00 : ℤ) by rw [hk]; norm_num)
  have hklt : k10 - k00 < (1 : ℤ) := by exact_mod_cast (show ((k10 - k00 : ℤ) : ℝ) < 1 by rw [hk]; norm_num)
  omega

def squaredProjection {ι : Type*} [Fintype ι] (u : ι → ℝ) (x : ι → Bool) : ℝ :=
  (u ⬝ᵥ boolVector x) ^ 2

/-- The full real-unit-vector atom bound modulo one. The witness is arbitrary
real and is excluded only when it is a signed coordinate vector. -/
theorem real_unit_quadratic_atom {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ℝ} (hα : 0 ≤ α)
    (p : ι → unitInterval)
    (hp : ∀ i, α ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ 1 - α)
    (u : ι → ℝ) (hnorm : ∑ i, u i ^ 2 = 1)
    (hnon : ¬ IsSignedCoordinate u) (z : ℝ) :
    (cubeMeasure p).real {x | ModOneEq (squaredProjection u x) z} ≤ 1 - α ^ 2 := by
  obtain ⟨i, j, hij, hi, hj⟩ := unit_noncoordinate_two_nonzero u hnorm hnon
  apply cube_event_le_of_pair_missing p i j hij hα (hp i) (hp j)
  intro r
  let t := u ⬝ᵥ boolVector (patchTwo i j r false false)
  have ht (hpair : u i ^ 2 + u j ^ 2 = 1) : t = 0 := by
    unfold t dotProduct
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k = i
    · subst k; simp [boolVector, patchTwo, bitValue]
    · by_cases hkj : k = j
      · subst k; simp [boolVector, patchTwo, bitValue, hki]
      · rw [unit_pair_exhausts u hnorm i j hij hpair k hki hkj]
        exact zero_mul _
  obtain ⟨ab, hab⟩ := four_squares_missing_mod_one t (u i) (u j) z hi hj
    (unit_pair_sq_le u hnorm i j hij) ht
  refine ⟨ab, ?_⟩
  change ¬ ModOneEq (squaredProjection u (patchTwo i j r ab.1 ab.2)) z
  unfold squaredProjection
  rw [boolVector_patchTwo i j hij r ab.1 ab.2]
  simpa [dotProduct_add, dotProduct_single, t] using hab

end AdaptiveOrthogonalRigidity
