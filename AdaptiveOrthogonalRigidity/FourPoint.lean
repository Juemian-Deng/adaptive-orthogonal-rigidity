import AdaptiveOrthogonalRigidity.Model
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite weighted-atom bounds used by both the affine cube and quadratic Gram
arguments. These are local ingredients, not either global rigidity theorem. -/

open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- A finite atom misses the mass of any point outside that atom. -/
theorem finite_atom_le_of_missing {Ω T : Type*} [Fintype Ω]
    (w : Ω → ℝ) (f : Ω → T) (z : T) (a : Ω)
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1) (ha : f a ≠ z) :
    (∑ x, if f x = z then w x else 0) ≤ 1 - w a := by
  classical
  have hpoint (x : Ω) :
      (if f x = z then w x else 0) + (if x = a then w a else 0) ≤ w x := by
    by_cases hxa : x = a
    · subst x
      simp [ha]
    · simp only [hxa, ite_false, add_zero]
      split_ifs
      · exact le_rfl
      · exact hw x
  have h := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hpoint x)
  simp only [Finset.sum_add_distrib] at h
  simp [hsum] at h
  linarith

def bitWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

def cornerWeight (p q : ℝ) (x : Bool × Bool) : ℝ :=
  bitWeight p x.1 * bitWeight q x.2

theorem cornerWeight_sum (p q : ℝ) : ∑ x : Bool × Bool, cornerWeight p q x = 1 := by
  simp [cornerWeight, bitWeight, Fintype.sum_prod_type]
  ring

theorem bitWeight_lower {α p : ℝ} (hp : α ≤ p ∧ p ≤ 1 - α) (b : Bool) :
    α ≤ bitWeight p b := by
  cases b <;> simp [bitWeight] <;> linarith [hp.1, hp.2]

theorem cornerWeight_lower {α p q : ℝ} (hα : 0 ≤ α)
    (hp : α ≤ p ∧ p ≤ 1 - α) (hq : α ≤ q ∧ q ≤ 1 - α)
    (x : Bool × Bool) : α ^ 2 ≤ cornerWeight p q x := by
  have h₁ := bitWeight_lower hp x.1
  have h₂ := bitWeight_lower hq x.2
  calc
    α ^ 2 = α * α := by ring
    _ ≤ cornerWeight p q x := mul_le_mul h₁ h₂ hα (hα.trans h₁)

/-- Excluding even one of the four corners costs at least alpha squared. -/
theorem two_bit_atom_le {T : Type*} {α p q : ℝ} (hα : 0 ≤ α)
    (hp : α ≤ p ∧ p ≤ 1 - α) (hq : α ≤ q ∧ q ≤ 1 - α)
    (f : Bool × Bool → T) (z : T) (hmissing : ∃ x, f x ≠ z) :
    (∑ x : Bool × Bool, if f x = z then cornerWeight p q x else 0) ≤ 1 - α ^ 2 := by
  classical
  obtain ⟨a, ha⟩ := hmissing
  have hlow := cornerWeight_lower hα hp hq a
  have hw (x : Bool × Bool) : 0 ≤ cornerWeight p q x :=
    (sq_nonneg α).trans (cornerWeight_lower hα hp hq x)
  have h := finite_atom_le_of_missing (cornerWeight p q) f z a hw
    (cornerWeight_sum p q) ha
  linarith

/-- The quadratic mixed difference before reduction modulo one or modulo three. -/
theorem square_mixed_difference (t a b : ℝ) :
    (t + a + b) ^ 2 - (t + a) ^ 2 - (t + b) ^ 2 + t ^ 2 = 2 * a * b := by
  ring

end AdaptiveOrthogonalRigidity
