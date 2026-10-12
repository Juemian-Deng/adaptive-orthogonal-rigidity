import AdaptiveOrthogonalRigidity.KernelDimensions

open Matrix
open scoped Classical

namespace AdaptiveOrthogonalRigidity

private theorem normal_block_rank (K : Type*) [Field K] (r k : ℕ) :
    (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 0 (0 : Matrix (Fin k) (Fin k) K)).rank = r := by
  rw [← Matrix.diagonal_one, ← Matrix.diagonal_zero, Matrix.fromBlocks_diagonal, Matrix.rank_diagonal]
  rw [Fintype.card_congr Equiv.subtypeSum]
  simp

/-- Matrix rank is unchanged by extending the coefficient field. The proof
maps a genuine invertible rank normal form, so no probabilistic law changes. -/
theorem square_rank_map_field {K L ι : Type*} [Field K] [Field L]
    [Fintype ι] [DecidableEq ι] (f : K →+* L) (M : Matrix ι ι K) :
    (M.map f).rank = M.rank := by
  obtain ⟨V, U, e, hV, hU, hform⟩ := Matrix.exists_rank_normal_form M
  have hV' : IsUnit (V.map f) := hV.map f.mapMatrix
  have hU' : IsUnit (U.map f) := hU.map f.mapMatrix
  have hVdet := (Matrix.isUnit_iff_isUnit_det _).mp hV'
  have hUdet := (Matrix.isUnit_iff_isUnit_det _).mp hU'
  have hm := congrArg (fun A : Matrix ι ι K => A.map f) hform
  simp only [Matrix.map_mul, ← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_zero _ (map_zero f)] at hm
  calc
    (M.map f).rank = (V.map f * M.map f * U.map f).rank := by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUdet,
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVdet]
    _ = _ := congrArg Matrix.rank hm
    _ = M.rank := by rw [Matrix.rank_submatrix]; exact normal_block_rank L _ _

theorem square_kernel_finrank_map_field {K L ι : Type*} [Field K] [Field L]
    [Fintype ι] [DecidableEq ι] (f : K →+* L) (M : Matrix ι ι K) :
    Module.finrank L (M.map f).mulVecLin.ker = Module.finrank K M.mulVecLin.ker := by
  have hK := M.mulVecLin.finrank_range_add_finrank_ker
  have hL := (M.map f).mulVecLin.finrank_range_add_finrank_ker
  change M.rank + Module.finrank K M.mulVecLin.ker = Module.finrank K (ι → K) at hK
  change (M.map f).rank + Module.finrank L (M.map f).mulVecLin.ker = Module.finrank L (ι → L) at hL
  rw [square_rank_map_field f M, Module.finrank_pi] at hL
  rw [Module.finrank_pi] at hK
  omega

end AdaptiveOrthogonalRigidity
