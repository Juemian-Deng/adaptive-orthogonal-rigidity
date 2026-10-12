import AdaptiveOrthogonalRigidity.QuadraticAlgebra
import Mathlib.Algebra.Field.ZMod

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

private theorem two_zmod_three_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

/-- Every fiber of a nonzero symmetric F3 quadratic form misses a Boolean corner
at some prescribed one- or two-coordinate face. This includes diagonal forms. -/
theorem f3_quadratic_atom {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : ι → unitInterval) (hp : ∀ i, α ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ 1 - α)
    (H : Matrix ι ι (ZMod 3)) (hsym : H.IsSymm) (hne : H ≠ 0) (z : ZMod 3) :
    (cubeMeasure p).real {x | cubeQuadratic H x = z} ≤ 1 - α ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  by_cases hoff : ∃ i j, i ≠ j ∧ H i j ≠ 0
  · obtain ⟨i, j, hij, hneij⟩ := hoff
    apply cube_atom_le_of_pair_missing p i j hij hα (hp i) (hp j)
    intro r
    by_contra hmissing
    push Not at hmissing
    have hm := cubeQuadratic_pair_mixed H i j hij r
    have hconst (a b : Bool) : cubeQuadratic H (patchTwo i j r a b) = z :=
      hmissing (a, b)
    have hs : H j i = H i j := congrFun (congrFun hsym i) j
    rw [hconst true true, hconst true false, hconst false true, hconst false false, hs] at hm
    have hz : (2 : ZMod 3) * H i j = 0 := by linear_combination -hm
    exact hneij ((mul_eq_zero.mp hz).resolve_left two_zmod_three_ne_zero)
  · have hdiag : ∀ i j, i ≠ j → H i j = 0 := by
      intro i j hij
      by_contra h
      exact hoff ⟨i, j, hij, h⟩
    have hex : ∃ i, H i i ≠ 0 := by
      by_contra h
      push Not at h
      apply hne
      ext i j
      by_cases hij : i = j
      · subst j; exact h i
      · exact hdiag i j hij
    obtain ⟨i, hi⟩ := hex
    have hbound : (cubeMeasure p).real {x | cubeQuadratic H x = z} ≤ 1 - α := by
      apply cube_atom_le_of_single_missing p i hα (hp i)
      intro r
      by_contra hmissing
      push Not at hmissing
      have hm := cubeQuadratic_diagonal_single_difference H hdiag i r
      have hconst (a : Bool) : cubeQuadratic H (patchOne i r a) = z := hmissing a
      rw [hconst true, hconst false, sub_self] at hm
      exact hi hm.symm
    exact hbound.trans (by nlinarith)

end AdaptiveOrthogonalRigidity
