import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Basic.Real.Basic

open Matrix
open scoped BigOperators

namespace AdaptiveOrthogonalRigidity

/-- Every field extension has a linear retraction of its scalar inclusion.
This is a linear map, not a field homomorphism. -/
theorem exists_scalar_retraction (K L : Type*) [Field K] [Field L] [Algebra K L] :
    ∃ ρ : L →ₗ[K] K, ∀ a : K, ρ (algebraMap K L a) = a := by
  obtain ⟨ρ, hρ⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective K L))
  refine ⟨ρ, fun a => ?_⟩
  exact LinearMap.congr_fun hρ a

/-- An affine linear system with coefficients in the base field has a solution
there whenever it has a solution over a field extension. The equation index
need not be finite. -/
theorem descend_finite_linear_system {K L ι τ : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype τ] (A : Matrix ι τ K) (b : ι → K)
    (h : ∃ x : τ → L, (A.map (algebraMap K L)).mulVec x =
      fun i => algebraMap K L (b i)) :
    ∃ x : τ → K, A.mulVec x = b := by
  obtain ⟨ρ, hρ⟩ := exists_scalar_retraction K L
  obtain ⟨x, hx⟩ := h
  refine ⟨fun j => ρ (x j), ?_⟩
  funext i
  have hi := congrArg ρ (congrFun hx i)
  simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
    ← Algebra.smul_def, map_smul, smul_eq_mul, hρ] using hi

/-- Simultaneous descent keeps every output column, including zero or linearly
dependent output columns. -/
theorem descend_matrix_equation {K L ι τ υ : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype τ] (A : Matrix ι τ K) (B : Matrix ι υ K)
    (h : ∃ X : Matrix τ υ L,
      A.map (algebraMap K L) * X = B.map (algebraMap K L)) :
    ∃ X : Matrix τ υ K, A * X = B := by
  classical
  obtain ⟨X, hX⟩ := h
  have hc : ∀ j : υ, ∃ x : τ → K, A.mulVec x = B.col j := by
    intro j
    apply descend_finite_linear_system (L := L) A (B.col j)
    refine ⟨X.col j, ?_⟩
    funext i
    exact congrFun (congrFun hX i) j
  choose x hx using hc
  refine ⟨fun i j => x j i, ?_⟩
  ext i j
  exact congrFun (hx j) i

/-- In particular, a real solution of a rational affine system descends to a
rational solution; no rationality assumption on the real solution is needed. -/
theorem rational_affine_descent {ι τ : Type*} [Fintype τ]
    (A : Matrix ι τ ℚ) (b : ι → ℚ)
    (h : ∃ x : τ → ℝ, (A.map (Rat.castHom ℝ)).mulVec x = fun i => (b i : ℝ)) :
    ∃ x : τ → ℚ, A.mulVec x = b :=
  @descend_finite_linear_system ℚ ℝ ι τ _ _ _ _ A b h

/-- The bounded polynomial-filter coefficient system descends with its leading
coefficient fixed at one. Here `A a = C^a Z` and `B a = C^a V` in the intended
application. All output labels `υ` occur in the single simultaneous identity. -/
theorem monic_filter_coefficients_descent {K L ι τ υ : Type*}
    [Field K] [Field L] [Algebra K L] [Fintype τ]
    (k : ℕ) (A : Fin (k + 1) → Matrix ι υ K)
    (B : Fin (k + 1) → Matrix ι τ K)
    (g : Fin (k + 1) → L) (P : Fin (k + 1) → Matrix τ υ L)
    (hg : g (Fin.last k) = 1)
    (hf : ∀ i j,
      (∑ a, g a * algebraMap K L (A a i j)) =
        ∑ a, ∑ t, algebraMap K L (B a i t) * P a t j) :
    ∃ (g' : Fin (k + 1) → K) (P' : Fin (k + 1) → Matrix τ υ K),
      g' (Fin.last k) = 1 ∧
      ∀ i j, (∑ a, g' a * A a i j) = ∑ a, ∑ t, B a i t * P' a t j := by
  obtain ⟨ρ, hρ⟩ := exists_scalar_retraction K L
  refine ⟨fun a => ρ (g a), fun a t j => ρ (P a t j), ?_, ?_⟩
  · change ρ (g (Fin.last k)) = 1
    rw [hg, ← map_one (algebraMap K L), hρ]
  · intro i j
    have hi := congrArg ρ (hf i j)
    simpa only [map_sum, mul_comm (g _), ← Algebra.smul_def, map_smul,
      smul_eq_mul, mul_comm (A _ _ _)] using hi

end AdaptiveOrthogonalRigidity
