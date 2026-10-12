import AdaptiveOrthogonalRigidity.FieldGraphMatrix
import AdaptiveOrthogonalRigidity.FieldExtensionRank
import AdaptiveOrthogonalRigidity.PolynomialKernel

open Matrix
open scoped Classical

namespace AdaptiveOrthogonalRigidity

theorem fieldGraphMatrix_map {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (n : ℕ) (diag : Fin n → K) (ω : GraphSample n) :
    (fieldGraphMatrix K n diag ω).map f = fieldGraphMatrix L n (fun i => f (diag i)) ω := by
  ext i j
  by_cases hij : i < j
  · simp only [Matrix.map_apply, fieldGraphMatrix_upper n _ ω i j hij]
    simp [bitValue]
  · by_cases hji : j < i
    · rw [Matrix.map_apply, ← (fieldGraphMatrix_isSymm n diag ω).apply i j,
        ← (fieldGraphMatrix_isSymm n (fun i => f (diag i)) ω).apply i j,
        fieldGraphMatrix_upper n _ ω j i hji, fieldGraphMatrix_upper n _ ω j i hji]
      simp [bitValue]
    · have heq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      subst j
      simp only [Matrix.map_apply, fieldGraphMatrix_diag]

theorem fieldGraphMatrix_sub_scalar {K : Type*} [Field K]
    (n : ℕ) (diag : Fin n → K) (ω : GraphSample n) (c : K) :
    fieldGraphMatrix K n diag ω - c • (1 : Matrix (Fin n) (Fin n) K) =
      fieldGraphMatrix K n (fun i => diag i - c) ω := by
  ext i j
  by_cases hij : i < j
  · simp [Matrix.sub_apply, Matrix.smul_apply, ne_of_lt hij,
      fieldGraphMatrix_upper n _ ω i j hij]
  · by_cases hji : j < i
    · rw [Matrix.sub_apply, ← (fieldGraphMatrix_isSymm n diag ω).apply i j,
        ← (fieldGraphMatrix_isSymm n (fun i => diag i - c) ω).apply i j,
        fieldGraphMatrix_upper n _ ω j i hji, fieldGraphMatrix_upper n _ ω j i hji]
      simp [Matrix.smul_apply, ne_of_gt hji]
    · have heq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      subst j
      simp [Matrix.sub_apply, fieldGraphMatrix_diag]

/-- Polynomial evaluation commutes with the genuine coefficient embedding. -/
theorem matrix_aeval_map_field {K L ι : Type*} [Field K] [Field L]
    [Fintype ι] [DecidableEq ι] (f : K →+* L) (M : Matrix ι ι K) (p : Polynomial K) :
    (Polynomial.aeval M p).map f = Polynomial.aeval (M.map f) (p.map f) := by
  exact Polynomial.map_aeval_eq_aeval_map (φ := f) (ψ := f.mapMatrix) (by
    ext c i j
    by_cases h : i = j <;> simp [Matrix.algebraMap_matrix_apply, Matrix.map_apply, h]) p M

theorem matrix_mulVecLin_aeval {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (p : Polynomial K) :
    (Polynomial.aeval M p).mulVecLin = Polynomial.aeval M.mulVecLin p := by
  exact (Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := ι)) M p).symm

theorem matrix_mulVecLin_sub_scalar {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (c : K) :
    (M - c • 1).mulVecLin = M.mulVecLin - c • 1 := by
  change Matrix.toLinAlgEquiv' (M - c • 1) = Matrix.toLinAlgEquiv' M - c • 1
  simp

theorem split_matrix_polynomial_kernel_bound {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) (p : Polynomial K)
    (hp : p ≠ 0) (hsplit : p.Splits) (t : ℕ)
    (hroot : ∀ a ∈ p.roots, Module.finrank K (M - a • 1).mulVecLin.ker ≤ t) :
    Module.finrank K (Polynomial.aeval M p).mulVecLin.ker ≤ p.natDegree * t := by
  rw [matrix_mulVecLin_aeval]
  apply split_polynomial_kernel_bound M.mulVecLin p hp hsplit t
  intro a ha
  rw [← matrix_mulVecLin_sub_scalar]
  exact hroot a ha

end AdaptiveOrthogonalRigidity
