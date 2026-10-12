import AdaptiveOrthogonalRigidity.CoordinateExtension

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

theorem coordinateExtension_dot {K ι : Type*} [CommSemiring K] [Fintype ι] [DecidableEq ι]
    (U : Finset ι) (x : U → K) (y : ι → K) :
    coordinateExtension K U x ⬝ᵥ y = x ⬝ᵥ coordinateRestriction K U y := by
  change (∑ j, (if h : j ∈ U then x ⟨j, h⟩ else 0) * y j) = ∑ j : U, x j * y j.val
  calc
    _ = ∑ j ∈ U, (if h : j ∈ U then x ⟨j, h⟩ else 0) * y j := by
      symm
      apply Finset.sum_subset U.subset_univ
      intro j _ hj
      rw [dite_eq_right hj, zero_mul]
    _ = _ := by
      rw [← Finset.sum_attach U]
      apply Finset.sum_congr rfl
      intro j _
      rw [dite_eq_left j.property]

theorem coordinateExtension_bilinear {K ι : Type*} [CommSemiring K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (U : Finset ι) (x y : U → K) :
    coordinateExtension K U x ⬝ᵥ M.mulVec (coordinateExtension K U y) =
      x ⬝ᵥ (M.submatrix Subtype.val Subtype.val).mulVec y := by
  rw [coordinateExtension_dot, ← principal_mulVec_coordinateExtension]

/-- The original coordinates split into a principal action and the actual
cross columns. -/
theorem coordinateRestriction_mulVec {K ι : Type*} [Semiring K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (U : Finset ι) (x : ι → K) :
    coordinateRestriction K U (M.mulVec x) =
      (M.submatrix (fun i : U => i.val) (fun i : U => i.val)).mulVec
        (coordinateRestriction K U x) +
      (M.submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val)).mulVec
        (coordinateRestriction K Uᶜ x) := by
  funext i
  change (∑ j, M i.val j * x j) =
    (∑ j : U, M i.val j.val * x j.val) + (∑ j : ↑Uᶜ, M i.val j.val * x j.val)
  calc
    _ = (∑ j ∈ U, M i.val j * x j) + (∑ j ∈ Uᶜ, M i.val j * x j) :=
      (Finset.sum_add_sum_compl U _).symm
    _ = _ := by
      rw [← Finset.sum_attach U, ← Finset.sum_attach Uᶜ]
      rfl

end AdaptiveOrthogonalRigidity
