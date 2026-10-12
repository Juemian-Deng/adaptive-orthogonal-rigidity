import AdaptiveOrthogonalRigidity.MovementNormality
import AdaptiveOrthogonalRigidity.RectangularDuality

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

theorem movement_transpose_kernel_iff {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (x : Fin n → ℝ) : (Q - 1).transpose.mulVec x = 0 ↔ (Q - 1).mulVec x = 0 := by
  constructor
  · intro hx
    apply orthogonal_movement_zero_of_dot_zero Q hQ x
    rw [← dotProduct_transpose_mulVec (Q - 1) x x, hx, dotProduct_zero]
  · intro hx
    have hh := orthogonal_movement_zero_of_dot_zero Q.transpose (orthogonal_transpose Q hQ) x
    have hd : x ⬝ᵥ (Q.transpose - 1).mulVec x = 0 := by
      have heq : Q.transpose - 1 = (Q - 1).transpose := by simp only [Matrix.transpose_sub, Matrix.transpose_one]
      rw [heq, dotProduct_transpose_mulVec, hx, dotProduct_zero]
    simpa only [Matrix.transpose_sub, Matrix.transpose_one] using hh hd

theorem movement_range_transpose {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q) :
    (Q - 1).transpose.mulVecLin.range = (Q - 1).mulVecLin.range := by
  ext x
  rw [mem_rectangular_transpose_range_iff, mem_rectangular_range_iff]
  constructor
  · intro hx v hv
    exact hx v ((movement_transpose_kernel_iff Q hQ v).mp hv)
  · intro hx v hv
    exact hx v ((movement_transpose_kernel_iff Q hQ v).mpr hv)

end AdaptiveOrthogonalRigidity
