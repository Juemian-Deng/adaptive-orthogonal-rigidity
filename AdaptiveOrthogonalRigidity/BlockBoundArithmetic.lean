import AdaptiveOrthogonalRigidity.BoundArithmetic

open scoped BigOperators

namespace AdaptiveOrthogonalRigidity

theorem leftBlockCount_le {q : ℕ} (hq : 1 ≤ q) : leftBlockCount q ≤ q := by
  unfold leftBlockCount
  split_ifs <;> omega

theorem twice_leftBlockCount_le {M q : ℕ} (hM : 2 ≤ M) (hq : 1 ≤ q) (hqM : q ≤ M) :
    2 * leftBlockCount q ≤ M := by
  unfold leftBlockCount
  split_ifs <;> omega

theorem training_card_real_lower {n b M q : ℕ} (hb : 2 ≤ b) (hn : 2 * b ≤ n)
    (hnM : n ≤ b * M) (hq : 1 ≤ q) (hqM : q ≤ M) :
    (n : ℝ) / (4 * b) - 1 ≤ ((M - leftBlockCount q) / 2 : ℕ) := by
  have hM : 2 ≤ M := by nlinarith
  have hL := twice_leftBlockCount_le hM hq hqM
  have hcount : M ≤ 2 * (M - leftBlockCount q) := by omega
  have hround : M - leftBlockCount q ≤ 2 * ((M - leftBlockCount q) / 2) + 1 := by omega
  have hnum : n ≤ b * (4 * ((M - leftBlockCount q) / 2) + 2) := by nlinarith
  have hr : (n : ℝ) ≤ (b : ℝ) * (4 * (((M - leftBlockCount q) / 2 : ℕ) : ℝ) + 2) := by
    exact_mod_cast hnum
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * b)).mpr
  nlinarith

theorem symmetricDimension_mono {s b : ℕ} (hs : s ≤ b) : symmetricDimension s ≤ symmetricDimension b := by
  exact Nat.div_le_div_right (Nat.mul_le_mul hs (Nat.add_le_add_right hs 1))

/-- The exact fractional, potentially negative epsilon exponent dominates both
training and testing terms; natural subtraction is not used in that exponent. -/
theorem training_bound_le_blockEpsilon {α : ℝ} (hα : 0 < α) (hαhalf : α ≤ 1 / 2)
    {n b s l t : ℕ} (hb : 2 ≤ b) (hs : s ≤ b) (hlt : l ≤ t)
    (hl : (n : ℝ) / (4 * b) - 1 ≤ (l : ℝ)) :
    (3 : ℝ) ^ symmetricDimension s * (gamma α) ^ l +
        (b + 1 : ℝ) ^ symmetricDimension s * (gamma α) ^ t ≤ blockEpsilon α n b := by
  have hg0 := gamma_pos hα hαhalf
  have hg1 := (gamma_lt_one hα).le
  have hpowL : (gamma α) ^ l ≤ (gamma α) ^ ((n : ℝ) / (4 * b) - 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hg0 hg1 hl
  have hpowT : (gamma α) ^ t ≤ (gamma α) ^ ((n : ℝ) / (4 * b) - 1) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_ge hg0 hg1
    exact hl.trans (by exact_mod_cast hlt)
  have hbase : (3 : ℝ) ≤ b + 1 := by exact_mod_cast (show 3 ≤ b + 1 by omega)
  have hb1 : (1 : ℝ) ≤ b + 1 := by have := Nat.cast_nonneg (α := ℝ) b; linarith
  have hcoef : (b + 1 : ℝ) ^ symmetricDimension s ≤ (b + 1 : ℝ) ^ symmetricDimension b :=
    pow_le_pow_right₀ hb1 (symmetricDimension_mono hs)
  have hcoef3 := (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hbase (symmetricDimension s)).trans hcoef
  have hcpos : 0 ≤ (b + 1 : ℝ) ^ symmetricDimension b := by positivity
  have h1 := mul_le_mul hcoef3 hpowL (pow_nonneg hg0.le _) hcpos
  have h2 := mul_le_mul hcoef hpowT (pow_nonneg hg0.le _) hcpos
  unfold blockEpsilon
  linarith

end AdaptiveOrthogonalRigidity
