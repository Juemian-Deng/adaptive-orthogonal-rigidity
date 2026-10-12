import AdaptiveOrthogonalRigidity.QuadraticAlgebra
import AdaptiveOrthogonalRigidity.FiniteBounds
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Tactic.FinCases

open scoped BigOperators Classical Matrix

noncomputable section
namespace AdaptiveOrthogonalRigidity

/-- The standard complex additive character of F3. -/
def f3Char : ZMod 3 → ℂ := ZMod.stdAddChar

@[simp] theorem f3Char_zero : f3Char 0 = 1 := AddChar.map_zero_eq_one _

theorem f3Char_add (x y : ZMod 3) : f3Char (x + y) = f3Char x * f3Char y :=
  AddChar.map_add_eq_mul _ _ _

@[simp] theorem norm_f3Char (x : ZMod 3) : ‖f3Char x‖ = 1 := by
  simp only [f3Char, ZMod.stdAddChar_apply, Circle.norm_coe]

theorem f3Char_neg (x : ZMod 3) : f3Char (-x) = star (f3Char x) := by
  exact (AddChar.map_neg_eq_inv ZMod.stdAddChar x).trans (Complex.inv_eq_conj (norm_f3Char x))

theorem f3Char_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 3) :
    f3Char (∑ i ∈ s, f i) = ∏ i ∈ s, f3Char (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, f3Char_add, ih]

theorem f3_sum_three {A : Type*} [AddCommMonoid A] (f : ZMod 3 → A) :
    ∑ x, f x = f 0 + f 1 + f (-1) := by
  have hu : (Finset.univ : Finset (ZMod 3)) = {0, 1, -1} := by decide
  rw [hu]
  simp [show (0 : ZMod 3) ≠ 1 by decide, show (0 : ZMod 3) ≠ -1 by decide,
    show (1 : ZMod 3) ≠ -1 by decide, add_assoc]

theorem f3Char_mul_sum (t : ZMod 3) :
    ∑ x : ZMod 3, f3Char (x * t) = if t = 0 then 3 else 0 := by
  simpa [f3Char, ZMod.card] using AddChar.sum_mulShift t (ZMod.isPrimitive_stdAddChar 3)

theorem f3Char_re_of_ne_zero {t : ZMod 3} (ht : t ≠ 0) : (f3Char t).re = -(1 / 2) := by
  have hs := f3Char_mul_sum t
  rw [f3_sum_three] at hs
  simp only [zero_mul, one_mul, neg_one_mul, f3Char_zero, f3Char_neg, ite_eq_right ht] at hs
  have h := congrArg Complex.re hs
  simp only [Complex.add_re, Complex.one_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at h
  linarith

/-- Exact Bernoulli characteristic-function modulus squared at a nonzero F3 frequency. -/
theorem f3_bernoulli_character_norm_sq (p : ℝ) {t : ZMod 3} (ht : t ≠ 0) :
    ‖((1 - p : ℝ) : ℂ) + (p : ℂ) * f3Char t‖ ^ 2 = 1 - 3 * p * (1 - p) := by
  have hu : (f3Char t).re ^ 2 + (f3Char t).im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, norm_f3Char, pow_two] using Complex.normSq_eq_norm_sq (f3Char t)
  have hr := f3Char_re_of_ne_zero ht
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add]
  rw [hr] at hu ⊢
  nlinarith [congrArg (fun x : ℝ => p ^ 2 * x) hu]

theorem kappa_nonneg (α : ℝ) : 0 ≤ kappa α := Real.sqrt_nonneg _

theorem kappa_sq (α : ℝ) : (kappa α) ^ 2 = 1 - 3 * α * (1 - α) := by
  apply Real.sq_sqrt
  nlinarith [sq_nonneg (α - 1 / 2)]

theorem kappa_le_one {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) : kappa α ≤ 1 := by
  have h := mul_nonneg hα (sub_nonneg.mpr hα1)
  nlinarith [kappa_sq α, kappa_nonneg α]

/-- The heterogeneous Bernoulli Fourier factor is bounded by the manuscript's κ. -/
theorem f3_bernoulli_character_norm_le {α p : ℝ}
    (hp : α ≤ p ∧ p ≤ 1 - α) (t : ZMod 3) :
    ‖((1 - p : ℝ) : ℂ) + (p : ℂ) * f3Char t‖ ≤ if t = 0 then 1 else kappa α := by
  by_cases ht : t = 0
  · subst t
    simp only [f3Char_zero, mul_one, ite_true]
    have h : ((1 - p : ℝ) : ℂ) + (p : ℂ) = 1 := by push_cast; ring
    rw [h, norm_one]
  · rw [ite_eq_right ht]
    have hm := mul_nonneg (sub_nonneg.mpr hp.1) (sub_nonneg.mpr hp.2)
    have hn := f3_bernoulli_character_norm_sq p ht
    nlinarith [kappa_sq α, kappa_nonneg α, norm_nonneg
      (((1 - p : ℝ) : ℂ) + (p : ℂ) * f3Char t)]

/-- Orthogonality of all vector frequencies, proved by products of scalar characters. -/
theorem f3_vector_character_sum {k : ℕ} (w : Fin k → ZMod 3) :
    ∑ v : Fin k → ZMod 3, f3Char (v ⬝ᵥ w) = if w = 0 then (3 : ℂ) ^ k else 0 := by
  simp_rw [dotProduct, f3Char_sum]
  rw [← Fintype.prod_sum (fun (i : Fin k) (t : ZMod 3) => f3Char (t * w i))]
  simp_rw [f3Char_mul_sum]
  by_cases hw : w = 0
  · simp [hw]
  · rw [ite_eq_right hw]
    have hex : ∃ j, w j ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hw (funext hn)
    obtain ⟨j, hj⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

/-- Finite Fourier inversion of a point indicator, without any probabilistic assumption. -/
theorem f3_vector_fourier_indicator {k : ℕ} (y z : Fin k → ZMod 3) :
    ∑ v : Fin k → ZMod 3, f3Char (-(v ⬝ᵥ z)) * f3Char (v ⬝ᵥ y) =
      if y = z then (3 : ℂ) ^ k else 0 := by
  have he (v : Fin k → ZMod 3) :
      f3Char (-(v ⬝ᵥ z)) * f3Char (v ⬝ᵥ y) = f3Char (v ⬝ᵥ (y - z)) := by
    rw [← f3Char_add, dotProduct_sub]
    congr 1
    ring
  simp_rw [he]
  simpa only [sub_eq_zero] using f3_vector_character_sum (y - z)

/-- Fourier inversion, weighted by an arbitrary nonnegative finite law. -/
theorem f3_weighted_atom_fourier {Ω : Type*} [Fintype Ω] {k : ℕ}
    (w : Ω → ℝ) (Y : Ω → Fin k → ZMod 3) (z : Fin k → ZMod 3) :
    ((∑ x, if Y x = z then w x else 0 : ℝ) : ℂ) * (3 : ℂ) ^ k =
      ∑ v : Fin k → ZMod 3, f3Char (-(v ⬝ᵥ z)) *
        ∑ x, (w x : ℂ) * f3Char (v ⬝ᵥ Y x) := by
  rw [Complex.ofReal_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = (w x : ℂ) * (if Y x = z then (3 : ℂ) ^ k else 0) := by
      split_ifs <;> simp_all
    _ = (w x : ℂ) * ∑ v : Fin k → ZMod 3,
        f3Char (-(v ⬝ᵥ z)) * f3Char (v ⬝ᵥ Y x) := by rw [f3_vector_fourier_indicator]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring

/-- Triangle inequality applied to exact finite Fourier inversion. -/
theorem f3_weighted_atom_le_fourier {Ω : Type*} [Fintype Ω] {k : ℕ}
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (Y : Ω → Fin k → ZMod 3)
    (z : Fin k → ZMod 3) :
    (∑ x, if Y x = z then w x else 0) * (3 : ℝ) ^ k ≤
      ∑ v : Fin k → ZMod 3, ‖∑ x, (w x : ℂ) * f3Char (v ⬝ᵥ Y x)‖ := by
  have hm : 0 ≤ ∑ x, if Y x = z then w x else 0 :=
    Finset.sum_nonneg (fun x _ => by split_ifs; exact hw x; exact le_rfl)
  have he := f3_weighted_atom_fourier w Y z
  have hn := congrArg norm he
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm,
    norm_pow, Complex.norm_ofNat] at hn
  calc
    _ = ‖∑ v : Fin k → ZMod 3, f3Char (-(v ⬝ᵥ z)) *
        ∑ x, (w x : ℂ) * f3Char (v ⬝ᵥ Y x)‖ := hn
    _ ≤ ∑ v : Fin k → ZMod 3, ‖f3Char (-(v ⬝ᵥ z)) *
        ∑ x, (w x : ℂ) * f3Char (v ⬝ᵥ Y x)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_f3Char, one_mul]

/-- The vector sum made from independent original Boolean coordinates. -/
def f3RowSum {ι : Type*} [Fintype ι] {k : ℕ} (u : ι → Fin k → ZMod 3) (x : ι → Bool) :
    Fin k → ZMod 3 := ∑ i, (bitValue (x i) : ZMod 3) • u i

/-- Exact factorization of a characteristic function in the heterogeneous product law. -/
theorem f3_cube_character_factorization {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} (p : ι → unitInterval) (u : ι → Fin k → ZMod 3) (v : Fin k → ZMod 3) :
    (∑ x : ι → Bool, (cubeWeight p x : ℂ) * f3Char (v ⬝ᵥ f3RowSum u x)) =
      ∏ i, (((1 - (p i : ℝ) : ℝ) : ℂ) + ((p i : ℝ) : ℂ) * f3Char (v ⬝ᵥ u i)) := by
  simp only [f3RowSum, dotProduct_sum, dotProduct_smul, smul_eq_mul, f3Char_sum,
    cubeWeight, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : ι) (b : Bool) =>
    (bitWeight (p i : ℝ) b : ℂ) * f3Char ((bitValue b : ZMod 3) * (v ⬝ᵥ u i)))]
  apply Finset.prod_congr rfl
  intro i _
  simp [bitWeight, bitValue, add_comm]

/-- A proved finite Fourier atom bound; no anti-concentration assumption is supplied. -/
theorem f3_cube_atom_le_fourier_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} {α : ℝ} (p : ι → unitInterval)
    (hp : ∀ i, α ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ 1 - α)
    (u : ι → Fin k → ZMod 3) (z : Fin k → ZMod 3) :
    (cubeMeasure p).real {x | f3RowSum u x = z} * (3 : ℝ) ^ k ≤
      ∑ v : Fin k → ZMod 3, ∏ i, if v ⬝ᵥ u i = 0 then 1 else kappa α := by
  have he : (cubeMeasure p).real {x | f3RowSum u x = z} =
      ∑ x, if f3RowSum u x = z then cubeWeight p x else 0 := by
    rw [cubeMeasure_real_eq_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : f3RowSum u x = z <;> simp [hx]
  rw [he]
  refine (f3_weighted_atom_le_fourier (cubeWeight p) (cubeWeight_nonneg p) (f3RowSum u) z).trans ?_
  apply Finset.sum_le_sum
  intro v _
  rw [f3_cube_character_factorization, norm_prod]
  apply Finset.prod_le_prod₀
  · intro i _; exact norm_nonneg _
  · intro i _; exact f3_bernoulli_character_norm_le (hp i) _

end AdaptiveOrthogonalRigidity
