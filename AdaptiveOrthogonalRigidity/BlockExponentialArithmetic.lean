import AdaptiveOrthogonalRigidity.GeometricBlockBound

namespace AdaptiveOrthogonalRigidity

noncomputable def blockEntropy (n b : ℕ) : ℝ :=
  (b : ℝ) ^ 3 * Real.log ((b : ℝ) + 1) + (b : ℝ) ^ 2 * Real.log n

noncomputable def blockDecay (α : ℝ) : ℝ := -Real.log (gamma α)

noncomputable def blockLogError (α : ℝ) (n b : ℕ) : ℝ :=
  Real.log ((b : ℝ) - 1) + b * Real.log n + Real.log 2 / 3 +
    (symmetricDimension b : ℝ) / 3 * Real.log ((b : ℝ) + 1) +
    blockDecay α / 3 + Real.log 2

theorem gamma_pos_lt_one {α : ℝ} (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    0 < gamma α ∧ gamma α < 1 := by unfold gamma; constructor <;> nlinarith

theorem blockDecay_pos {α : ℝ} (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    0 < blockDecay α := by
  exact neg_pos.mpr (Real.log_neg (gamma_pos_lt_one hα hαhalf).1 (gamma_pos_lt_one hα hαhalf).2)

theorem blockEpsilon_pos {α : ℝ} (hα : 0 < α) (hαhalf : α ≤ 1 / 2) (n b : ℕ) :
    0 < blockEpsilon α n b := by
  unfold blockEpsilon
  exact mul_pos (by positivity) (Real.rpow_pos_of_pos (gamma_pos_lt_one hα hαhalf).1 _)

theorem blockCandidateCount_pos {n b : ℕ} (hn : 1 ≤ n) (hb : 2 ≤ b) :
    0 < blockCandidateCount n b := lt_of_lt_of_le (by norm_num) (blockCandidateCount_one_le hn hb)

theorem blockY_pos {α : ℝ} {n b : ℕ} (hα : 0 < α) (hαhalf : α ≤ 1 / 2)
    (hn : 1 ≤ n) (hb : 2 ≤ b) : 0 < blockY α n b :=
  mul_pos (blockCandidateCount_pos hn hb) (Real.rpow_pos_of_pos (blockEpsilon_pos hα hαhalf n b) _)

theorem blockY_log_identity {α : ℝ} {n b : ℕ} (hα : 0 < α) (hαhalf : α ≤ 1 / 2)
    (hn : 1 ≤ n) (hb : 2 ≤ b) :
    Real.log (blockY α n b) =
      -(blockDecay α / 12) * n / b + blockLogError α n b - Real.log 2 := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  rw [blockY, Real.log_mul (ne_of_gt (blockCandidateCount_pos hn hb))
    (ne_of_gt (Real.rpow_pos_of_pos (blockEpsilon_pos hα hαhalf n b) _)),
    Real.log_rpow (blockEpsilon_pos hα hαhalf n b), blockCandidateCount,
    Real.log_mul (ne_of_gt hb1) (ne_of_gt (pow_pos hn0 b)), Real.log_pow]
  have he : Real.log (blockEpsilon α n b) = Real.log 2 +
      (symmetricDimension b : ℝ) * Real.log ((b : ℝ) + 1) +
      ((n : ℝ) / (4 * b) - 1) * Real.log (gamma α) := by
    unfold blockEpsilon
    rw [Real.log_mul (by positivity) (ne_of_gt (Real.rpow_pos_of_pos (gamma_pos_lt_one hα hαhalf).1 _)),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      Real.log_rpow (gamma_pos_lt_one hα hαhalf).1]
  rw [he]
  unfold blockLogError blockDecay
  field_simp
  ring

theorem log_succ_half_le {b : ℕ} (hb : 2 ≤ b) :
    (1 / 2 : ℝ) ≤ Real.log ((b : ℝ) + 1) := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hi : ((b : ℝ) + 1)⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (by linarith : (2 : ℝ) ≤ b + 1)
  exact (by linarith : (1 / 2 : ℝ) ≤ 1 - ((b : ℝ) + 1)⁻¹).trans
    (Real.one_sub_inv_le_log_of_pos (by positivity))

theorem symmetricDimension_le_sq {b : ℕ} (hb : 1 ≤ b) : symmetricDimension b ≤ b ^ 2 := by
  unfold symmetricDimension
  apply Nat.div_le_of_le_mul
  nlinarith

/-- A deliberately loose positive majorant which works also for bounded or
oscillating block-size sequences. -/
theorem blockLogError_le {α : ℝ} {n b : ℕ} (hα : 0 < α) (hαhalf : α ≤ 1 / 2)
    (hn : 1 ≤ n) (hb : 2 ≤ b) :
    (b : ℝ) * blockLogError α n b ≤ (blockDecay α + 5) * blockEntropy n b := by
  let T : ℝ := (b : ℝ) ^ 2 * Real.log ((b : ℝ) + 1) + b * Real.log n
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlb := log_succ_half_le hb
  have hT : 1 ≤ T := by dsimp [T]; nlinarith [sq_nonneg ((b : ℝ) - 2)]
  have hc : 0 ≤ blockDecay α := (blockDecay_pos hα hαhalf).le
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog : Real.log ((b : ℝ) - 1) ≤ T := by
    have h := Real.log_le_log (by linarith : (0 : ℝ) < b - 1)
      (by linarith : (b : ℝ) - 1 ≤ b + 1)
    dsimp [T]
    nlinarith [mul_nonneg hb0 hln, mul_nonneg
      (show 0 ≤ (b : ℝ) ^ 2 - 1 by nlinarith) (show 0 ≤ Real.log ((b : ℝ) + 1) by linarith)]
  have hdim : (symmetricDimension b : ℝ) ≤ (b : ℝ) ^ 2 := by
    exact_mod_cast symmetricDimension_le_sq (show 1 ≤ b by omega)
  have hdim0 : (0 : ℝ) ≤ symmetricDimension b := by positivity
  have hE : blockLogError α n b ≤ (blockDecay α + 5) * T := by
    unfold blockLogError
    have h1 : (b : ℝ) * Real.log n ≤ T := by
      dsimp [T]
      nlinarith [mul_nonneg (sq_nonneg (b : ℝ)) (show 0 ≤ Real.log ((b : ℝ) + 1) by linarith)]
    have h2 : (symmetricDimension b : ℝ) / 3 * Real.log ((b : ℝ) + 1) ≤ T := by
      dsimp [T]
      nlinarith [mul_nonneg hb0 hln, mul_nonneg (sub_nonneg.mpr hdim) (show 0 ≤ Real.log ((b : ℝ) + 1) by linarith)]
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hT)]
  have hmult := mul_le_mul_of_nonneg_left hE hb0
  simpa only [blockEntropy, T] using hmult.trans_eq (by ring)

noncomputable def blockRateError (α : ℝ) (n b : ℕ) : ℝ :=
  (blockDecay α + 5) * blockEntropy n b / n

theorem blockEntropy_ge_size {n b : ℕ} (hn : 1 ≤ n) (hb : 2 ≤ b) :
    (b : ℝ) ≤ blockEntropy n b := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlb := log_succ_half_le hb
  have hpow : (b : ℝ) ≤ (b : ℝ) ^ 3 / 2 := by
    have hs : (2 : ℝ) ≤ (b : ℝ) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ b by positivity)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hlb (pow_nonneg (show (0 : ℝ) ≤ b by positivity) 3)
  unfold blockEntropy
  nlinarith [mul_nonneg (sq_nonneg (b : ℝ)) hln]

theorem small_error_block_exponential {α : ℝ} {n b : ℕ}
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) (hb : 2 ≤ b) (hn : 2 * b ≤ n)
    (he : blockRateError α n b ≤ blockDecay α / 12)
    (p : EdgeParameters n) (hp : Admissible α p) :
    eventProbability p (blockEvent n b) ≤
      Real.exp (-(blockDecay α / 12 - blockRateError α n b) * n / b) := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hy0 := blockY_pos hα hαhalf hn1 hb
  have hE : blockLogError α n b ≤ blockRateError α n b * n / b := by
    apply (le_div_iff₀ hb0).2
    have h := blockLogError_le hα hαhalf hn1 hb
    have hid : blockRateError α n b * n = (blockDecay α + 5) * blockEntropy n b := by
      unfold blockRateError
      field_simp
    rw [hid, mul_comm]
    exact h
  have hlog : Real.log (blockY α n b) + Real.log 2 ≤
      -(blockDecay α / 12 - blockRateError α n b) * n / b := by
    rw [blockY_log_identity hα hαhalf hn1 hb]
    calc
      _ = -(blockDecay α / 12) * n / b + blockLogError α n b := by ring
      _ ≤ -(blockDecay α / 12) * n / b + blockRateError α n b * n / b := add_le_add (le_refl _) hE
      _ = _ := by ring
  have hexp : -(blockDecay α / 12 - blockRateError α n b) * n / b ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) hn0.le) hb0.le
  have hyhalf : blockY α n b ≤ 1 / 2 := by
    calc
      _ = Real.exp (Real.log (blockY α n b)) := (Real.exp_log hy0).symm
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  have hy1 : blockY α n b < 1 := by linarith
  have hbound := (finite_block_bound hα hαhalf hb hn p hp).2 hy1
  calc
    _ ≤ blockY α n b / (1 - blockY α n b) := hbound
    _ ≤ 2 * blockY α n b := by
      apply (div_le_iff₀ (by linarith : 0 < 1 - blockY α n b)).2
      nlinarith
    _ = Real.exp (Real.log (blockY α n b) + Real.log 2) := by
      rw [Real.exp_add, Real.exp_log hy0, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hlog

end AdaptiveOrthogonalRigidity
