import AdaptiveOrthogonalRigidity.FiniteBlockTheorem
import Mathlib.Algebra.Order.Field.GeomSum

open scoped BigOperators

namespace AdaptiveOrthogonalRigidity

theorem leftBlockCount_ge_third {q : ℕ} (hq : 1 ≤ q) :
    (1 / 3 : ℝ) * q ≤ (leftBlockCount q : ℝ) := by
  have h : q ≤ 3 * leftBlockCount q := by
    unfold leftBlockCount
    split_ifs <;> omega
  have hr : (q : ℝ) ≤ 3 * (leftBlockCount q : ℝ) := by exact_mod_cast h
  linarith

/-- Pure numerical geometric-series step; includes the special one-block case. -/
theorem block_sum_geometric {a ε : ℝ} (ha : 1 ≤ a) (hε : 0 ≤ ε)
    (hy : a * ε ^ (1 / 3 : ℝ) < 1) (N : ℕ) :
    (∑ q ∈ Finset.Icc 1 N, a ^ q * (min 1 ε) ^ leftBlockCount q) ≤
      (a * ε ^ (1 / 3 : ℝ)) / (1 - a * ε ^ (1 / 3 : ℝ)) := by
  have hroot : 0 ≤ ε ^ (1 / 3 : ℝ) := Real.rpow_nonneg hε _
  have hy0 : 0 ≤ a * ε ^ (1 / 3 : ℝ) := mul_nonneg (by linarith) hroot
  have hε1 : ε < 1 := by
    by_contra! h
    have hr := Real.one_le_rpow h (show (0 : ℝ) ≤ 1 / 3 by norm_num)
    have hm := mul_le_mul ha hr (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ a)
    norm_num at hm
    linarith
  have hterm (q : ℕ) (hq : q ∈ Finset.Icc 1 N) :
      a ^ q * (min 1 ε) ^ leftBlockCount q ≤ (a * ε ^ (1 / 3 : ℝ)) ^ q := by
    rw [min_eq_right hε1.le, mul_pow]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith) _)
    rw [← Real.rpow_natCast, ← Real.rpow_mul_natCast hε]
    exact Real.rpow_le_rpow_of_exponent_ge' hε hε1.le
      (by positivity) (leftBlockCount_ge_third (Finset.mem_Icc.mp hq).1)
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 N, (a * ε ^ (1 / 3 : ℝ)) ^ q :=
      Finset.sum_le_sum hterm
    _ ≤ _ := by
      simpa only [Finset.Ico_add_one_right_eq_Icc, pow_one] using
        (geom_sum_Ico_le_of_lt_one (m := 1) (n := N + 1) hy0 hy)

theorem blockCandidateCount_one_le {n b : ℕ} (hn : 1 ≤ n) (hb : 2 ≤ b) :
    1 ≤ blockCandidateCount n b := by
  have hb' : (1 : ℝ) ≤ (b : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact one_le_mul_of_one_le_of_one_le hb' (one_le_pow₀ hn')

/-- The full finite block theorem, including the geometric corollary, for
heterogeneous independent graphs and adaptive arbitrary-real witnesses. -/
theorem finite_block_bound {α : ℝ} {n b : ℕ}
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) (hb : 2 ≤ b) (hn : 2 * b ≤ n)
    (p : EdgeParameters n) (hp : Admissible α p) :
    eventProbability p (blockEvent n b) ≤ finiteBlockSum α n b ∧
      (blockY α n b < 1 →
        eventProbability p (blockEvent n b) ≤ blockY α n b / (1 - blockY α n b)) := by
  have h := finite_block_sum_bound hα hαhalf hb hn p hp
  refine ⟨h, fun hy => h.trans ?_⟩
  exact block_sum_geometric (blockCandidateCount_one_le (by omega) hb)
    (blockEpsilon_nonneg hα hαhalf n b) hy (n / 2)

end AdaptiveOrthogonalRigidity
