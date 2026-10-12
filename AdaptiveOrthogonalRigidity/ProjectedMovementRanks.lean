import AdaptiveOrthogonalRigidity.CoordinateExtension
import AdaptiveOrthogonalRigidity.MovementNormality

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

theorem movement_principal_kernel {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (U : Finset (Fin n)) :
    ((Q - 1).submatrix (fun i : U => i.val) (fun i : U => i.val)).mulVecLin.ker =
      ((Q - 1).submatrix id (fun i : U => i.val)).mulVecLin.ker := by
  ext x
  change ((Q - 1).submatrix (fun i : U => i.val) (fun i : U => i.val)).mulVec x = 0 ↔
    ((Q - 1).submatrix id (fun i : U => i.val)).mulVec x = 0
  constructor
  · intro hx
    have hh := supported_movement_zero Q hQ U (coordinateExtension ℝ U x)
      (by intro i hi; simp [coordinateExtension, hi]) (by
        intro i hi
        rw [principal_mulVec_coordinateExtension] at hx
        exact congrFun hx ⟨i, hi⟩)
    rw [mulVec_coordinateExtension] at hh
    exact hh
  · intro hx
    funext i
    exact congrFun hx i.val

/-- Normal movement has equal rank on the original U columns and U rows. -/
theorem movement_column_row_rank {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (U : Finset (Fin n)) :
    ((Q - 1).submatrix id (fun i : U => i.val)).rank =
      ((Q - 1).submatrix (fun i : U => i.val) id).rank := by
  let F := (Q - 1).submatrix id (fun i : U => i.val)
  let H := (Q - 1).submatrix (fun i : U => i.val) id
  have hgram : F.transpose * F = H * H.transpose := by
    ext i j
    have h := congrArg (fun M : RealMatrix n => M i.val j.val) (orthogonal_movement_normal Q hQ).2
    simpa only [F, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq] using h.symm
  calc
    F.rank = (F.transpose * F).rank := (Matrix.rank_transpose_mul_self F).symm
    _ = (H * H.transpose).rank := congrArg Matrix.rank hgram
    _ = H.rank := Matrix.rank_self_mul_transpose H

theorem movement_principal_row_rank {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (U : Finset (Fin n)) :
    ((Q - 1).submatrix (fun i : U => i.val) (fun i : U => i.val)).rank =
      ((Q - 1).submatrix (fun i : U => i.val) id).rank := by
  have hN := ((Q - 1).submatrix (fun i : U => i.val) (fun i : U => i.val)).mulVecLin.finrank_range_add_finrank_ker
  have hF := ((Q - 1).submatrix id (fun i : U => i.val)).mulVecLin.finrank_range_add_finrank_ker
  rw [movement_principal_kernel Q hQ U] at hN
  have heq : ((Q - 1).submatrix (fun i : U => i.val) (fun i : U => i.val)).rank =
      ((Q - 1).submatrix id (fun i : U => i.val)).rank := by
    change _ + _ = _ at hN hF
    exact Nat.add_right_cancel (hN.trans hF.symm)
  exact heq.trans (movement_column_row_rank Q hQ U)

/-- The principal movement image is the entire projected movement image,
not merely a subspace assumed to be surjective. -/
theorem movement_principal_row_range {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (U : Finset (Fin n)) :
    ((Q - 1).submatrix (fun i : U => i.val) (fun i : U => i.val)).mulVecLin.range =
      ((Q - 1).submatrix (fun i : U => i.val) id).mulVecLin.range := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro y ⟨x, rfl⟩
    refine ⟨coordinateExtension ℝ U x, ?_⟩
    exact mulVec_coordinateExtension ((Q - 1).submatrix (fun i : U => i.val) id) U x
  · exact movement_principal_row_rank Q hQ U

theorem projected_movement_lifting {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (U : Finset (Fin n)) (z : U → ℝ)
    (hz : z ∈ ((Q - 1).submatrix (fun i : U => i.val) id).mulVecLin.range) :
    ∃ f : Fin n → ℝ, f ∈ ((Q - 1).submatrix id (fun i : U => i.val)).mulVecLin.range ∧
      coordinateRestriction ℝ U f = z := by
  rw [← movement_principal_row_range Q hQ U] at hz
  obtain ⟨x, hx⟩ := hz
  refine ⟨((Q - 1).submatrix id (fun i : U => i.val)).mulVec x, ⟨x, rfl⟩, ?_⟩
  exact hx

end AdaptiveOrthogonalRigidity
