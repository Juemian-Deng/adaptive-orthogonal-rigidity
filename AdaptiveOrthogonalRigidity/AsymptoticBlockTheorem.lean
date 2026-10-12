import AdaptiveOrthogonalRigidity.BlockExponentialArithmetic
import Mathlib.Analysis.Asymptotics.Lemmas

open Filter Asymptotics

namespace AdaptiveOrthogonalRigidity

/-- The explicit error sequence depends only on the block sizes and density
margin, and is selected before every heterogeneous edge-parameter array. -/
theorem asymptotic_block_bound (α : ℝ) (b : ℕ → ℕ)
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) (hb : ∀ n, 2 ≤ b n)
    (hsmall : IsLittleO atTop
      (fun n => (b n : ℝ) ^ 3 * Real.log ((b n : ℝ) + 1) +
        (b n : ℝ) ^ 2 * Real.log n) (fun n => (n : ℝ))) :
    ∃ (e : ℕ → ℝ) (N : ℕ), Tendsto e atTop (nhds 0) ∧
      ∀ n, N ≤ n → ∀ p : EdgeParameters n, Admissible α p →
        eventProbability p (blockEvent n (b n)) ≤
          Real.exp (-((-Real.log (gamma α)) / 12 - e n) * n / (b n : ℝ)) := by
  let e : ℕ → ℝ := fun n => blockRateError α n (b n)
  have hratio : Tendsto (fun n => blockEntropy n (b n) / n) atTop (nhds 0) :=
    hsmall.tendsto_div_nhds_zero
  have he : Tendsto e atTop (nhds 0) := by
    simpa only [e, blockRateError, mul_div_assoc, mul_zero] using
      hratio.const_mul (blockDecay α + 5)
  have hevent : ∀ᶠ n in atTop, 1 ≤ n ∧ 2 * b n ≤ n ∧ e n ≤ blockDecay α / 12 := by
    filter_upwards [eventually_ge_atTop 1,
      hratio.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
      he.eventually_lt_const (div_pos (blockDecay_pos hα hαhalf) (by norm_num : (0 : ℝ) < 12))]
      with n hn hr he'
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hg := blockEntropy_ge_size hn (hb n)
    have hbound : (2 : ℝ) * (b n : ℝ) ≤ n := by
      have h := (div_lt_iff₀ hn0).mp hr
      linarith
    exact ⟨hn, by exact_mod_cast hbound, he'.le⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨e, N, he, ?_⟩
  intro n hn p hp
  exact small_error_block_exponential hα hαhalf (hb n) (hN n hn).2.1 (hN n hn).2.2 p hp

end AdaptiveOrthogonalRigidity
