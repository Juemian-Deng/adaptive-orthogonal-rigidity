import AdaptiveOrthogonalRigidity.FiniteBounds
import Mathlib.Tactic.Linarith

namespace AdaptiveOrthogonalRigidity

theorem leftBlockCount_lower {q : ℕ} (hq : 1 ≤ q) :
    q ≤ 3 * leftBlockCount q := by
  unfold leftBlockCount
  split_ifs <;> omega

theorem leftBlockCount_eq_half {q : ℕ} (hq : 2 ≤ q) :
    leftBlockCount q = q / 2 := by
  simp [leftBlockCount, show q ≠ 1 by omega]

theorem beta_pos {α : ℝ} (hα : 0 < α) (hα' : α ≤ 1 / 2) : 0 < beta α := by
  unfold beta
  linarith

theorem beta_lt_one {α : ℝ} (hα : 0 < α) : beta α < 1 := by
  unfold beta
  linarith

theorem gamma_pos {α : ℝ} (hα : 0 < α) (hα' : α ≤ 1 / 2) : 0 < gamma α := by
  unfold gamma
  nlinarith

theorem gamma_lt_one {α : ℝ} (hα : 0 < α) : gamma α < 1 := by
  unfold gamma
  nlinarith

theorem beta_lt_gamma {α : ℝ} (hα : 0 < α) (hα' : α ≤ 1 / 2) :
    beta α < gamma α := by
  unfold beta gamma
  nlinarith

theorem two_thirds_lt_gamma {α : ℝ} (hα : 0 < α) (hα' : α ≤ 1 / 2) :
    (2 / 3 : ℝ) < gamma α := by
  unfold gamma
  nlinarith

end AdaptiveOrthogonalRigidity
