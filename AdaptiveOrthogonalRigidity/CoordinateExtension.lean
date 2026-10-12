import Mathlib.LinearAlgebra.Matrix.ToLin

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

def coordinateRestriction {ι : Type*} (K : Type*) [Semiring K] (U : Finset ι) :
    (ι → K) →ₗ[K] (U → K) := LinearMap.funLeft K K Subtype.val

def coordinateExtension {ι : Type*} [DecidableEq ι] (K : Type*) [Semiring K] (U : Finset ι) :
    (U → K) →ₗ[K] (ι → K) where
  toFun x i := if h : i ∈ U then x ⟨i, h⟩ else 0
  map_add' x y := by funext i; by_cases hi : i ∈ U <;> simp [hi]
  map_smul' c x := by funext i; by_cases hi : i ∈ U <;> simp [hi]

theorem coordinateExtension_restrict {ι : Type*} [DecidableEq ι]
    (K : Type*) [Semiring K] (U : Finset ι) (x : U → K) :
    coordinateRestriction K U (coordinateExtension K U x) = x := by
  funext i
  simp [coordinateRestriction, coordinateExtension, i.property]

theorem mulVec_coordinateExtension {K ι μ : Type*} [Semiring K] [Fintype ι] [DecidableEq ι]
    (M : Matrix μ ι K) (U : Finset ι) (x : U → K) :
    M.mulVec (coordinateExtension K U x) = (M.submatrix id Subtype.val).mulVec x := by
  funext i
  change (∑ j, M i j * (if h : j ∈ U then x ⟨j, h⟩ else 0)) = ∑ j : U, M i j.val * x j
  calc
    _ = ∑ j ∈ U, M i j * (if h : j ∈ U then x ⟨j, h⟩ else 0) := by
      symm
      apply Finset.sum_subset U.subset_univ
      intro j _ hj
      rw [dite_eq_right hj, mul_zero]
    _ = _ := by
      rw [← Finset.sum_attach U]
      apply Finset.sum_congr rfl
      intro j _
      rw [dite_eq_left j.property]

/-- A rectangular principal restriction is exactly restriction after extension,
with no change of ambient labels. -/
theorem principal_mulVec_coordinateExtension {K ι : Type*} [Semiring K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (U : Finset ι) (x : U → K) :
    (M.submatrix Subtype.val Subtype.val).mulVec x =
      coordinateRestriction K U (M.mulVec (coordinateExtension K U x)) := by
  rw [mulVec_coordinateExtension]
  rfl

end AdaptiveOrthogonalRigidity
