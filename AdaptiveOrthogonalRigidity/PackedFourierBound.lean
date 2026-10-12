import AdaptiveOrthogonalRigidity.F3FourierAtoms
import AdaptiveOrthogonalRigidity.LinearBasePacking
import Mathlib.Analysis.MeanInequalities
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.Dual

open scoped BigOperators Classical Matrix
noncomputable section
namespace AdaptiveOrthogonalRigidity

/-- Evaluation against an actual row basis is a bijection, over every field. -/
def rowBasisEvaluationEquiv {K ι : Type*} [Field K] [Fintype ι] {k : ℕ}
    (u : ι → Fin k → K) (hu : LinearIndependent K u) (hc : Fintype.card ι = k) :
    (Fin k → K) ≃ₗ[K] (ι → K) :=
  let b := basisOfLinearIndependentOfCardEqFinrank' u hu (by simpa using hc)
  (dotProductEquiv K (Fin k)).trans b.dualBasis.equivFun

theorem rowBasisEvaluationEquiv_apply {K ι : Type*} [Field K] [Fintype ι] {k : ℕ}
    (u : ι → Fin k → K) (hu : LinearIndependent K u) (hc : Fintype.card ι = k)
    (v : Fin k → K) (i : ι) : rowBasisEvaluationEquiv u hu hc v i = v ⬝ᵥ u i := by
  simp [rowBasisEvaluationEquiv, Module.Basis.dualBasis_equivFun,
    coe_basisOfLinearIndependentOfCardEqFinrank']

/-- Equal-exponent finite Young inequality, a pointwise form of Hölder. -/
theorem finite_product_le_mean_powers {R : ℕ} (hR : 1 ≤ R) (x : Fin R → ℝ)
    (hx : ∀ a, 0 ≤ x a) :
    ∏ a, x a ≤ (R : ℝ)⁻¹ * ∑ a, x a ^ R := by
  have hR0 : R ≠ 0 := by omega
  have hRc : (R : ℝ) ≠ 0 := by exact_mod_cast hR0
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _a : Fin R => (R : ℝ)⁻¹) (fun a => x a ^ R)
    (by intro a _; positivity) (by simp [hRc]) (by intro a _; exact pow_nonneg (hx a) _)
  have he (a : Fin R) : (x a ^ R) ^ (R : ℝ)⁻¹ = x a :=
    Real.pow_rpow_inv_natCast (hx a) hR0
  simpa only [he, ← Finset.mul_sum] using h

/-- The Fourier weight of a vector over F3. -/
def f3FourierWeight {ι : Type*} [Fintype ι] (c : ℝ) (v : ι → ZMod 3) : ℝ :=
  ∏ i, if v i = 0 then 1 else c

theorem f3FourierWeight_nonneg {ι : Type*} [Fintype ι] {c : ℝ} (hc : 0 ≤ c)
    (v : ι → ZMod 3) : 0 ≤ f3FourierWeight c v := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact zero_le_one
  · exact hc

/-- Exact F3 product partition function, with no loss in the exponent. -/
theorem sum_f3FourierWeight_pow {ι : Type*} [Fintype ι] (c : ℝ) (R : ℕ) :
    ∑ v : ι → ZMod 3, f3FourierWeight c v ^ R = (1 + 2 * c ^ R) ^ Fintype.card ι := by
  simp only [f3FourierWeight, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun (_i : ι) (t : ZMod 3) => (if t = 0 then (1 : ℝ) else c) ^ R)]
  have he : (∑ t : ZMod 3, (if t = 0 then (1 : ℝ) else c) ^ R) = 1 + 2 * c ^ R := by
    rw [f3_sum_three]
    norm_num
    ring
  simp_rw [he]
  simp

/-- The finite Hölder estimate for a family of actual row bases. -/
theorem f3_basis_family_fourier_bound {R k : ℕ} (hR : 1 ≤ R)
    (ι : Fin R → Type*) [∀ a, Fintype (ι a)] (u : ∀ a, ι a → Fin k → ZMod 3)
    (hu : ∀ a, LinearIndependent (ZMod 3) (u a)) (hc : ∀ a, Fintype.card (ι a) = k)
    (c : ℝ) (hc0 : 0 ≤ c) :
    (∑ v : Fin k → ZMod 3, ∏ a, f3FourierWeight c (fun i => v ⬝ᵥ u a i)) ≤
      (1 + 2 * c ^ R) ^ k := by
  have hR0 : R ≠ 0 := by omega
  have hRc : (R : ℝ) ≠ 0 := by exact_mod_cast hR0
  have hm (a : Fin R) :
      (∑ v : Fin k → ZMod 3, f3FourierWeight c (fun i => v ⬝ᵥ u a i) ^ R) =
        (1 + 2 * c ^ R) ^ k := by
    let e := rowBasisEvaluationEquiv (u a) (hu a) (hc a)
    calc
      _ = ∑ w : ι a → ZMod 3, f3FourierWeight c w ^ R := by
        exact Fintype.sum_equiv e.toEquiv _ _ (fun v => by
          congr 2
          funext i
          exact (rowBasisEvaluationEquiv_apply (u a) (hu a) (hc a) v i).symm)
      _ = _ := by rw [sum_f3FourierWeight_pow, hc a]
  calc
    _ ≤ ∑ v : Fin k → ZMod 3, (R : ℝ)⁻¹ *
        ∑ a, f3FourierWeight c (fun i => v ⬝ᵥ u a i) ^ R := by
      apply Finset.sum_le_sum
      intro v _
      exact finite_product_le_mean_powers hR _
        (fun a => f3FourierWeight_nonneg hc0 _)
    _ = (R : ℝ)⁻¹ * ∑ a : Fin R, ∑ v : Fin k → ZMod 3,
        f3FourierWeight c (fun i => v ⬝ᵥ u a i) ^ R := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = _ := by simp_rw [hm]; simp [hRc]

/-- A complete packed-row atom estimate under the original heterogeneous Boolean product law. -/
theorem f3_basis_family_atom {R k : ℕ} (hR : 1 ≤ R)
    (ι : Fin R → Type*) [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)]
    (u : ∀ a, ι a → Fin k → ZMod 3)
    (hu : ∀ a, LinearIndependent (ZMod 3) (u a)) (hc : ∀ a, Fintype.card (ι a) = k)
    {α : ℝ} (p : (Σ a, ι a) → unitInterval)
    (hp : ∀ i, α ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ 1 - α) (z : Fin k → ZMod 3) :
    (cubeMeasure p).real {x | f3RowSum (fun i => u i.1 i.2) x = z} ≤
      (1 / 3 : ℝ) ^ k * (1 + 2 * (kappa α) ^ R) ^ k := by
  have h := f3_cube_atom_le_fourier_product p hp (fun i => u i.1 i.2) z
  have hb := f3_basis_family_fourier_bound hR ι u hu hc (kappa α) (kappa_nonneg α)
  have he (v : Fin k → ZMod 3) :
      (∏ i : Σ a, ι a, if v ⬝ᵥ u i.1 i.2 = 0 then (1 : ℝ) else kappa α) =
        ∏ a, f3FourierWeight (kappa α) (fun i => v ⬝ᵥ u a i) := by
    rw [Fintype.prod_sigma]
    rfl
  simp_rw [he] at h
  have hprod := h.trans hb
  simpa [div_eq_mul_inv, div_pow, mul_comm] using
    (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 3) k)).mpr hprod

end AdaptiveOrthogonalRigidity
