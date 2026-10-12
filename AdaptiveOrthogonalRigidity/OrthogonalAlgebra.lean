import AdaptiveOrthogonalRigidity.BasicAlgebra

namespace AdaptiveOrthogonalRigidity

theorem orthogonal_one (n : ℕ) : Orthogonal (1 : RealMatrix n) := by
  simp [Orthogonal]

theorem orthogonal_transpose {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q) :
    Orthogonal Q.transpose := by
  simpa [Orthogonal] using And.intro hQ.2 hQ.1

theorem orthogonal_mul {n : ℕ} (Q P : RealMatrix n)
    (hQ : Orthogonal Q) (hP : Orthogonal P) : Orthogonal (Q * P) := by
  constructor
  · calc
      (Q * P).transpose * (Q * P) =
          P.transpose * (Q.transpose * Q) * P := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hQ.1]; simpa using hP.1
  · calc
      (Q * P) * (Q * P).transpose =
          Q * (P * P.transpose) * Q.transpose := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hP.2]; simpa using hQ.2

theorem conjugate_mul {n : ℕ} (A Q P : RealMatrix n) :
    conjugate A (Q * P) = conjugate (conjugate A Q) P := by
  simp [conjugate, Matrix.transpose_mul, Matrix.mul_assoc]

/-- Right-normalizing against an orthogonal reference cannot increase the movement rank. -/
theorem normalized_movement_rank_le {n : ℕ} (Q P : RealMatrix n)
    (hP : Orthogonal P) :
    (Q * P.transpose - 1).rank ≤ (Q - P).rank := by
  have h : Q * P.transpose - 1 = (Q - P) * P.transpose := by
    rw [sub_mul, hP.2]
  rw [h]
  exact Matrix.rank_mul_le_left _ _

theorem conjugate_transpose_cancel {n : ℕ} (A P : RealMatrix n)
    (hP : Orthogonal P) :
    conjugate (conjugate A P.transpose) P = A := by
  rw [← conjugate_mul, hP.1]
  simp [conjugate]

end AdaptiveOrthogonalRigidity
