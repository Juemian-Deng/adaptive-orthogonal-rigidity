import AdaptiveOrthogonalRigidity.BoundArithmetic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact exponential arithmetic for the compatible-displacement cover. -/

namespace AdaptiveOrthogonalRigidity

/-- The real logarithmic rate is positive throughout the admissible alpha range. -/
theorem coverRate_pos {α : ℝ} (hα : 0 < α) (hhalf : α ≤ 1 / 2) : 0 < coverRate α := by
  unfold coverRate
  rw [one_div, Real.log_inv]
  exact neg_pos.mpr (Real.log_neg (beta_pos hα hhalf) (beta_lt_one hα))

theorem coverRate_eq_neg_log_beta (α : ℝ) : coverRate α = -Real.log (beta α) := by
  simp only [coverRate, one_div, Real.log_inv]

/-- The extracted relative-rank and support inequalities retain all four
manuscript consequences, including the real lambda-squared threshold. -/
theorem cover_parameter_consequences {lam : ℝ} {m j s : ℕ}
    (hlam : 1 ≤ lam) (hm : 0 < m) (hj : 0 < j)
    (hratio : lam * j ≤ m) (hsupport : m ^ 2 ≤ j * s) :
    lam ≤ m ∧ lam * m ≤ s ∧ lam ^ 2 ≤ s ∧ j ≤ m ∧
      lam * (2 * j * s / m : ℕ) ≤ 2 * s := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hlam0 : 0 < lam := lt_of_lt_of_le (by norm_num) hlam
  have hs : (m : ℝ) ^ 2 ≤ (j : ℝ) * s := by exact_mod_cast hsupport
  have hlamm : lam ≤ m := (by nlinarith [mul_le_mul_of_nonneg_left hj1 hlam0.le] : lam ≤ lam * j).trans hratio
  have hjm : j ≤ m := by
    have : (j : ℝ) ≤ m := (by nlinarith : (j : ℝ) ≤ lam * j).trans hratio
    exact_mod_cast this
  have hms : lam * m ≤ s := by
    apply (mul_le_mul_iff_left₀ hj').mp
    calc
      lam * m * j = (lam * j) * m := by ring
      _ ≤ (m : ℝ) * m := mul_le_mul_of_nonneg_right hratio hm'.le
      _ ≤ (j : ℝ) * s := by nlinarith
      _ = (s : ℝ) * j := by ring
  have hss : lam ^ 2 ≤ s := by nlinarith [mul_le_mul_of_nonneg_left hlamm hlam0.le]
  refine ⟨hlamm, hms, hss, hjm, ?_⟩
  have hq : ((2 * j * s / m : ℕ) : ℝ) * m ≤ 2 * (j : ℝ) * s := by
    exact_mod_cast Nat.div_mul_le_self (2 * j * s) m
  apply (mul_le_mul_iff_left₀ hm').mp
  calc
    lam * (2 * j * s / m : ℕ) * m = lam * ((2 * j * s / m : ℕ) * (m : ℝ)) := by ring
    _ ≤ lam * (2 * (j : ℝ) * s) := mul_le_mul_of_nonneg_left hq hlam0.le
    _ = 2 * (lam * j) * s := by ring
    _ ≤ 2 * (m : ℝ) * s := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio (by norm_num)) (by positivity)
    _ = (2 * (s : ℝ)) * m := by ring

/-- The exact logarithm of the number of endpoint and skeleton codes. -/
noncomputable def coverCodeLog (n m j s : ℕ) : ℝ :=
  (2 * m : ℕ) * Real.log n + (2 * j : ℕ) * Real.log m +
    (2 * j * s / m : ℕ) * Real.log (1 + 4 * (m : ℝ) * j)

theorem coverCodeLog_le {α lam : ℝ} {n m j s : ℕ}
    (hα : 0 < α) (hhalf : α ≤ 1 / 2) (hn : 2 ≤ n)
    (hlam : max 1 (2 * coverEntropy n / coverRate α) ≤ lam)
    (hm : 0 < m) (hmn : m ≤ n) (hj : 0 < j) (hjn : j ≤ n)
    (hratio : lam * j ≤ m) (hsupport : m ^ 2 ≤ j * s) :
    coverCodeLog n m j s ≤ coverRate α * s / 2 := by
  have hlam1 : 1 ≤ lam := (le_max_left _ _).trans hlam
  have hlam0 : 0 < lam := lt_of_lt_of_le (by norm_num) hlam1
  have hc : 0 < coverRate α := coverRate_pos hα hhalf
  obtain ⟨_, hms, _, hjm, hqs⟩ := cover_parameter_consequences hlam1 hm hj hratio hsupport
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hjn' : (j : ℝ) ≤ n := by exact_mod_cast hjn
  have hjm' : (j : ℝ) ≤ m := by exact_mod_cast hjm
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hAl : 0 ≤ Real.log (1 + 4 * (n : ℝ) ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg (n : ℝ)])
  have hmlog := Real.log_le_log hm0 hmn'
  have hbase : 1 + 4 * (m : ℝ) * j ≤ 1 + 4 * (n : ℝ) ^ 2 := by
    have := mul_le_mul hmn' hjn' (by positivity : (0 : ℝ) ≤ j) (by positivity : (0 : ℝ) ≤ n)
    nlinarith
  have hAlog := Real.log_le_log (by positivity : (0 : ℝ) < 1 + 4 * (m : ℝ) * j) hbase
  have hlog : coverCodeLog n m j s ≤
      (2 * (m : ℝ) + 2 * j) * Real.log n +
        (2 * j * s / m : ℕ) * Real.log (1 + 4 * (n : ℝ) ^ 2) := by
    unfold coverCodeLog
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hmlog (by positivity : (0 : ℝ) ≤ 2 * j),
      mul_le_mul_of_nonneg_left hAlog (by positivity : (0 : ℝ) ≤ (2 * j * s / m : ℕ))]
  have hcoeff : lam * (2 * (m : ℝ) + 2 * j) ≤ 4 * s := by
    have hh := mul_le_mul_of_nonneg_left hjm' hlam0.le
    nlinarith
  have hent : lam * coverCodeLog n m j s ≤ coverEntropy n * s := by
    have h₁ := mul_le_mul_of_nonneg_left hlog hlam0.le
    have h₂ := mul_le_mul_of_nonneg_right hcoeff hnlog
    have h₃ := mul_le_mul_of_nonneg_right hqs hAl
    unfold coverEntropy
    nlinarith
  have hH : 2 * coverEntropy n ≤ lam * coverRate α :=
    (div_le_iff₀ hc).mp ((le_max_right _ _).trans hlam)
  apply (mul_le_mul_iff_right₀ hlam0).mp
  have hh := mul_le_mul_of_nonneg_right hH (show (0 : ℝ) ≤ s by positivity)
  nlinarith

/-- Candidate entropy and original-edge compatibility leave the claimed half-rate. -/
theorem cover_count_times_compatibility_le {α lam : ℝ} {n m j s : ℕ}
    (hα : 0 < α) (hhalf : α ≤ 1 / 2) (hn : 2 ≤ n)
    (hlam : max 1 (2 * coverEntropy n / coverRate α) ≤ lam)
    (hm : 0 < m) (hmn : m ≤ n) (hj : 0 < j) (hjn : j ≤ n)
    (hratio : lam * j ≤ m) (hsupport : m ^ 2 ≤ j * s) :
    ((n ^ (2 * m) * (m ^ (2 * j) * (1 + 4 * m * j) ^ (2 * j * s / m)) : ℕ) : ℝ) *
      (beta α) ^ s ≤ Real.exp (-coverRate α * lam ^ 2 / 2) := by
  have hb := beta_pos hα hhalf
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog := coverCodeLog_le hα hhalf hn hlam hm hmn hj hjn hratio hsupport
  have hs := (cover_parameter_consequences ((le_max_left _ _).trans hlam) hm hj hratio hsupport).2.2.1
  have hc := coverRate_pos hα hhalf
  have hid : ((n ^ (2 * m) * (m ^ (2 * j) * (1 + 4 * m * j) ^ (2 * j * s / m)) : ℕ) : ℝ) *
      (beta α) ^ s = Real.exp (coverCodeLog n m j s - coverRate α * s) := by
    rw [coverRate_eq_neg_log_beta]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    rw [show coverCodeLog n m j s - -Real.log (beta α) * s =
      (2 * m : ℕ) * Real.log n + (2 * j : ℕ) * Real.log m +
      (2 * j * s / m : ℕ) * Real.log (1 + 4 * (m : ℝ) * j) + (s : ℝ) * Real.log (beta α) by
        unfold coverCodeLog; ring]
    simp only [Real.exp_add, Real.exp_nat_mul, Real.exp_log hn0, Real.exp_log hm0,
      Real.exp_log (by positivity : (0 : ℝ) < 1 + 4 * (m : ℝ) * j), Real.exp_log hb]
    ring
  rw [hid]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hs hc.le]

end AdaptiveOrthogonalRigidity
