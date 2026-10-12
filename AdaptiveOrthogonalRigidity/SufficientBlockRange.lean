import AdaptiveOrthogonalRigidity.AsymptoticBlockTheorem

open Filter Asymptotics

namespace AdaptiveOrthogonalRigidity

theorem blockEntropy_le_cubic_log {n b : ℕ} (hn : 2 ≤ n) (hb : 2 ≤ b)
    (hbn : b ≤ n) : blockEntropy n b ≤ 3 * (b : ℝ) ^ 3 * Real.log n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbn' : (b : ℝ) ≤ n := by exact_mod_cast hbn
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hlog : Real.log ((b : ℝ) + 1) ≤ 2 * Real.log n := by
    have h1 := Real.log_le_log (by positivity : (0 : ℝ) < b + 1)
      (show (b : ℝ) + 1 ≤ 2 * n by linarith)
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn'
    rw [Real.log_mul (by norm_num) (by positivity)] at h1
    linarith
  have hc : (b : ℝ) ^ 2 ≤ (b : ℝ) ^ 3 := by
    have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ b by linarith) (sq_nonneg (b : ℝ))
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left hlog (pow_nonneg (show (0 : ℝ) ≤ b by positivity) 3)
  have h2 := mul_le_mul_of_nonneg_right hc hl
  unfold blockEntropy
  nlinarith

/-- The convenient cube-root/log range implies the stated block entropy
condition, without any monotonicity or divergence assumption on `b`. -/
theorem sufficient_block_range (b : ℕ → ℕ) (hb : ∀ n, 2 ≤ b n)
    (hsmall : IsLittleO atTop (fun n => (b n : ℝ))
      (fun n => ((n : ℝ) / Real.log n) ^ (1 / 3 : ℝ))) :
    IsLittleO atTop
      (fun n => (b n : ℝ) ^ 3 * Real.log ((b n : ℝ) + 1) +
        (b n : ℝ) ^ 2 * Real.log n) (fun n => (n : ℝ)) := by
  let x : ℕ → ℝ := fun n => ((n : ℝ) / Real.log n) ^ (1 / 3 : ℝ)
  have hratio : Tendsto (fun n => (b n : ℝ) / x n) atTop (nhds 0) :=
    hsmall.tendsto_div_nhds_zero
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  have hevent : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 ≤ Real.log (n : ℝ) ∧ b n ≤ n := by
    filter_upwards [eventually_ge_atTop 2, hlog,
      hratio.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with n hn hln hr
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hl0 : 0 < Real.log (n : ℝ) := by linarith
    have hx0 : 0 < x n := Real.rpow_pos_of_pos (div_pos hn0 hl0) _
    have hbx : (b n : ℝ) ≤ x n := by
      have h := (div_lt_iff₀ hx0).mp hr
      linarith
    have hxn : x n ≤ n := by
      calc
        _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (div_nonneg hn0.le hl0.le)
          ((div_le_iff₀ hl0).mpr (by nlinarith)) (by norm_num)
        _ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = _ := Real.rpow_one _
    exact ⟨hn, hln, by exact_mod_cast hbx.trans hxn⟩
  have hbound : ∀ᶠ n : ℕ in atTop,
      blockEntropy n (b n) / n ≤ 3 * ((b n : ℝ) / x n) ^ 3 := by
    filter_upwards [hevent] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hl0 : 0 < Real.log (n : ℝ) := by linarith [hn.2.1]
    have hx : (x n) ^ 3 = (n : ℝ) / Real.log n := by
      rw [← Real.rpow_mul_natCast (div_nonneg hn0.le hl0.le)]
      norm_num
    have hid : ((b n : ℝ) / x n) ^ 3 = (b n : ℝ) ^ 3 * Real.log n / n := by
      rw [div_pow, hx]
      field_simp
    rw [hid]
    have h := div_le_div_of_nonneg_right (blockEntropy_le_cubic_log hn.1 (hb n) hn.2.2) hn0.le
    exact h.trans_eq (by ring)
  have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ blockEntropy n (b n) / n := by
    filter_upwards [hevent] with n hn
    exact div_nonneg ((show (0 : ℝ) ≤ b n by positivity).trans
      (blockEntropy_ge_size (by omega) (hb n))) (by positivity)
  have hzero : Tendsto (fun n => 3 * ((b n : ℝ) / x n) ^ 3) atTop (nhds 0) := by
    simpa using (hratio.pow 3).const_mul 3
  apply (isLittleO_iff_tendsto' ?_).mpr (squeeze_zero' hnonneg hbound hzero)
  filter_upwards [eventually_ge_atTop 1] with n hn hz
  have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact False.elim (ne_of_gt this hz)

end AdaptiveOrthogonalRigidity
