import AdaptiveOrthogonalRigidity.KrylovColumns
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

open Matrix Polynomial
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Independence of the actual input Krylov columns detects every polynomial
relation whose degrees lie in the independence window, over an arbitrary field. -/
theorem krylov_polynomial_relation_eq_zero {K ι τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype τ]
    (d : ℕ) (C : Matrix ι ι K) (V : τ → ι → K)
    (hI : LinearIndependent K (krylovColumns d C V))
    (q : τ → Polynomial K) (hq : ∀ t, (q t).natDegree ≤ d)
    (hrel : ∑ t, (Polynomial.aeval C (q t)).mulVec (V t) = 0) :
    ∀ t, q t = 0 := by
  have heval (t : τ) : Polynomial.aeval C (q t) =
      ∑ a : Fin (d + 1), (q t).coeff a.val • C ^ a.val := by
    rw [Polynomial.aeval_eq_sum_range' (n := d + 1) (by have := hq t; omega)]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  have hs : (∑ aj : Fin (d + 1) × τ,
      (q aj.2).coeff aj.1.val • krylovColumns d C V aj) = 0 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simpa only [heval, Matrix.sum_mulVec, Matrix.smul_mulVec, krylovColumns] using hrel
  have hc := Fintype.linearIndependent_iff.mp hI _ hs
  intro t
  ext a
  by_cases ha : a < d + 1
  · exact hc (⟨a, ha⟩, t)
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hq t; omega)

/-- Cross multiplication of two polynomial filters is forced to agree by
input-Krylov independence through the sum of their degree bounds. This is
simultaneous in all output columns; no nonzero-output assumption is used. -/
theorem polynomial_filter_cross_unique {K ι τ υ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype τ]
    (k : ℕ) (C : Matrix ι ι K) (V : τ → ι → K) (Z : υ → ι → K)
    (hI : LinearIndependent K (krylovColumns (2 * k) C V))
    (g₁ g₂ : Polynomial K) (P₁ P₂ : τ → υ → Polynomial K)
    (hg₁ : g₁.natDegree ≤ k) (hg₂ : g₂.natDegree ≤ k)
    (hP₁ : ∀ t j, (P₁ t j).natDegree ≤ k)
    (hP₂ : ∀ t j, (P₂ t j).natDegree ≤ k)
    (hf₁ : ∀ j, (Polynomial.aeval C g₁).mulVec (Z j) =
      ∑ t, (Polynomial.aeval C (P₁ t j)).mulVec (V t))
    (hf₂ : ∀ j, (Polynomial.aeval C g₂).mulVec (Z j) =
      ∑ t, (Polynomial.aeval C (P₂ t j)).mulVec (V t)) :
    ∀ t j, g₂ * P₁ t j = g₁ * P₂ t j := by
  intro t j
  have hr : ∑ s, (Polynomial.aeval C (g₂ * P₁ s j - g₁ * P₂ s j)).mulVec (V s) = 0 := by
    simp only [map_sub, map_mul, Matrix.sub_mulVec, Finset.sum_sub_distrib,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sum, ← hf₁, ← hf₂]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← map_mul, ← map_mul, mul_comm g₂ g₁,
      sub_self]
  have hd (s : τ) : (g₂ * P₁ s j - g₁ * P₂ s j).natDegree ≤ 2 * k := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · exact (Polynomial.natDegree_mul_le).trans (by have := hP₁ s j; omega)
    · exact (Polynomial.natDegree_mul_le).trans (by have := hP₂ s j; omega)
  exact sub_eq_zero.mp (krylov_polynomial_relation_eq_zero (2 * k) C V hI _ hd hr t)

end AdaptiveOrthogonalRigidity
