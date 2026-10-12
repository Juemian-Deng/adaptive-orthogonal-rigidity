import AdaptiveOrthogonalRigidity.ProjectedMovementRanks
import AdaptiveOrthogonalRigidity.CoordinateAlgebra
import AdaptiveOrthogonalRigidity.RectangularDuality

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

theorem orthogonal_fixed_of_transpose_fixed {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (x : Fin n → ℝ) (hx : Q.transpose.mulVec x = x) : Q.mulVec x = x := by
  have h := congrArg Q.mulVec hx
  rw [Matrix.mulVec_mulVec, hQ.2, Matrix.one_mulVec] at h
  exact h.symm

theorem conjugate_bilinear {n : ℕ} (A Q : RealMatrix n) (x y : Fin n → ℝ) :
    x ⬝ᵥ (conjugate A Q).mulVec y = Q.mulVec x ⬝ᵥ A.mulVec (Q.mulVec y) := by
  unfold conjugate
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_transpose_mulVec, dotProduct_comm]

/-- Shared-block conjugation transports the actual original U-column
movement image into the projected movement space. -/
theorem projected_action_column_movement {n : ℕ} (A Q : RealMatrix n)
    (hQ : Orthogonal Q) (U : Finset (Fin n))
    (hblock : (conjugate A Q).submatrix (fun i : U => i.val) (fun j : U => j.val) =
      A.submatrix (fun i : U => i.val) (fun j : U => j.val)) (x : U → ℝ) :
    coordinateRestriction ℝ U (A.mulVec
      (((Q - 1).submatrix id (fun j : U => j.val)).mulVec x)) ∈
      ((Q - 1).submatrix (fun i : U => i.val) id).mulVecLin.range := by
  apply (mem_rectangular_range_iff _ _).mpr
  intro z hz
  let e := coordinateExtension ℝ U z
  let y := coordinateExtension ℝ U x
  have htrans : (Q.transpose - 1).mulVec e = 0 := by
    rw [mulVec_coordinateExtension]
    simpa only [Matrix.transpose_submatrix, Matrix.transpose_sub, Matrix.transpose_one] using hz
  have hfixT : Q.transpose.mulVec e = e := by
    simpa only [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] using htrans
  have hfix := orthogonal_fixed_of_transpose_fixed Q hQ e hfixT
  have hshared : e ⬝ᵥ (conjugate A Q).mulVec y = e ⬝ᵥ A.mulVec y := by
    change coordinateExtension ℝ U z ⬝ᵥ (conjugate A Q).mulVec (coordinateExtension ℝ U x) = _
    rw [coordinateExtension_bilinear, hblock, ← coordinateExtension_bilinear]
  rw [conjugate_bilinear, hfix] at hshared
  have hzero : e ⬝ᵥ A.mulVec ((Q - 1).mulVec y) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, dotProduct_sub, hshared, sub_self]
  rw [mulVec_coordinateExtension] at hzero
  rw [coordinateExtension_dot] at hzero
  exact (dotProduct_comm _ _).trans hzero

end AdaptiveOrthogonalRigidity
