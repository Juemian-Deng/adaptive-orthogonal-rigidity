import AdaptiveOrthogonalRigidity.OrthogonalAlgebra
import Mathlib.LinearAlgebra.Matrix.DotProduct

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

theorem orthogonal_dotProduct {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (x y : Fin n → ℝ) : Q.mulVec x ⬝ᵥ Q.mulVec y = x ⬝ᵥ y := by
  calc
    _ = y ⬝ᵥ Q.transpose.mulVec (Q.mulVec x) := (Matrix.dotProduct_transpose_mulVec Q y (Q.mulVec x)).symm
    _ = y ⬝ᵥ x := by rw [Matrix.mulVec_mulVec, hQ.1, Matrix.one_mulVec]
    _ = x ⬝ᵥ y := dotProduct_comm _ _

theorem orthogonal_movement_normal {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q) :
    (Q - 1) + (Q - 1).transpose = -(Q - 1).transpose * (Q - 1) ∧
      (Q - 1) * (Q - 1).transpose = (Q - 1).transpose * (Q - 1) := by
  constructor <;>
    simp only [Matrix.transpose_sub, Matrix.transpose_one, neg_mul, sub_mul, mul_sub,
      Matrix.mul_one, Matrix.one_mul, hQ.1, hQ.2] <;> abel

theorem orthogonal_movement_quadratic {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (x : Fin n → ℝ) :
    (Q - 1).mulVec x ⬝ᵥ (Q - 1).mulVec x = -2 * (x ⬝ᵥ (Q - 1).mulVec x) := by
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, sub_dotProduct, dotProduct_sub]
  rw [orthogonal_dotProduct Q hQ, dotProduct_comm (Q.mulVec x) x]
  ring

/-- The only vector with zero movement quadratic form is a fixed vector. -/
theorem orthogonal_movement_zero_of_dot_zero {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (x : Fin n → ℝ) (hx : x ⬝ᵥ (Q - 1).mulVec x = 0) : (Q - 1).mulVec x = 0 := by
  apply dotProduct_self_eq_zero.mp
  rw [orthogonal_movement_quadratic Q hQ x, hx, mul_zero]

/-- A vector supported on U whose movement vanishes on U has zero full
movement. This is the principal-kernel injectivity step in projected transport. -/
theorem supported_movement_zero {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (U : Finset (Fin n)) (x : Fin n → ℝ) (hx : ∀ i ∉ U, x i = 0)
    (hR : ∀ i ∈ U, (Q - 1).mulVec x i = 0) : (Q - 1).mulVec x = 0 := by
  apply orthogonal_movement_zero_of_dot_zero Q hQ x
  unfold dotProduct
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ U
  · rw [hR i hi, mul_zero]
  · rw [hx i hi, zero_mul]

end AdaptiveOrthogonalRigidity
