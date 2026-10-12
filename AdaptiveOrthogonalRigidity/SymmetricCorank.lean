import AdaptiveOrthogonalRigidity.MarkedCorankProbability

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Symmetric Bernoulli corank bound over any field, with arbitrary deterministic
diagonal, under the original heterogeneous unordered-edge product law. -/
theorem symmetric_corank_bound {K : Type*} [Field K] (n t : ℕ) (diag : Fin n → K)
    {α : ℝ} (hα : 0 ≤ α) (hαhalf : α ≤ 1 / 2)
    (p : EdgeParameters n) (hp : Admissible α p) :
    eventProbability p {ω | t ≤ fieldGraphCorank K n diag ω} ≤
      (2 : ℝ) ^ n * (beta α) ^ (((t : ℝ) ^ 2 - 1) / 4) := by
  let a := t / 2
  let m := t - t / 2
  let J := (Finset.range n).powersetCard m
  let D : ℝ := (1 - α) ^ (a * m)
  have hβ : 0 < 1 - α := by linarith
  have hD : 0 ≤ D := pow_nonneg hβ.le _
  have hsub : {ω | t ≤ fieldGraphCorank K n diag ω} ⊆
      ⋃ S : J, markedCorankEvent K n diag a S.val := by
    intro ω hω
    obtain ⟨S, hS, hcard, hsteps⟩ := corank_path_selected_steps (fieldCorankPath K n diag ω) n t
      (fieldCorankPath_zero n diag ω) (fieldCorankPath_growth n diag ω)
      (by rw [fieldCorankPath_top]; exact hω)
    refine Set.mem_iUnion.mpr ⟨⟨S, Finset.mem_powersetCard.mpr ⟨hS, hcard⟩⟩, ?_⟩
    exact (markedCorankEvent_iff n diag ω a S).mpr (fun i hi _ => hsteps i hi)
  have hS (S : J) : eventProbability p (markedCorankEvent K n diag a S.val) ≤ D := by
    have hs := Finset.mem_powersetCard.mp S.property
    have h := markedCorankEvent_probability n diag a S.val hα (by linarith) p hp
    simpa only [Finset.inter_eq_left.mpr hs.1, hs.2] using h
  have hcount : (Fintype.card J : ℝ) ≤ (2 : ℝ) ^ n := by
    have h : J.card ≤ 2 ^ n := by
      simpa only [J, Finset.card_powersetCard, Finset.card_range] using Nat.choose_le_two_pow n m
    simpa only [Fintype.card_coe, Nat.cast_pow, Nat.cast_ofNat] using
      (show (J.card : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) by exact_mod_cast h)
  have hexp : D ≤ (beta α) ^ (((t : ℝ) ^ 2 - 1) / 4) := by
    rw [show D = (1 - α) ^ ((a * m : ℕ) : ℝ) by rw [Real.rpow_natCast]]
    exact Real.rpow_le_rpow_of_exponent_ge hβ (by linarith) (corank_half_product_bound t)
  calc
    _ ≤ eventProbability p (⋃ S : J, markedCorankEvent K n diag a S.val) := measureReal_mono hsub
    _ ≤ ∑ S : J, eventProbability p (markedCorankEvent K n diag a S.val) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _S : J, D := Finset.sum_le_sum (fun S _ => hS S)
    _ = (Fintype.card J : ℝ) * D := by simp
    _ ≤ (2 : ℝ) ^ n * D := mul_le_mul_of_nonneg_right hcount hD
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)

end AdaptiveOrthogonalRigidity
