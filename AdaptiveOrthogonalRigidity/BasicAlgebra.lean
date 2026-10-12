import AdaptiveOrthogonalRigidity.Model
import Mathlib.Tactic.NoncommRing

open scoped Matrix

namespace AdaptiveOrthogonalRigidity

/-- Rank subadditivity over real finite matrices, proved from inclusion of images. -/
theorem matrix_rank_add_le {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  apply le_trans (Submodule.finrank_mono ?_)
    (Submodule.finrank_add_le_finrank_add_finrank
      (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin))
  rintro v ⟨x, rfl⟩
  rw [Matrix.mulVecLin_add, LinearMap.add_apply]
  exact Submodule.mem_sup.mpr
    ⟨A.mulVecLin x, ⟨x, rfl⟩, B.mulVecLin x, ⟨x, rfl⟩, rfl⟩

/-- Exact displacement expansion; orthogonality is not needed for this identity. -/
theorem conjugate_sub_eq {n : ℕ} (A Q : RealMatrix n) :
    conjugate A Q - A =
      Q.transpose * A * (Q - 1) + (Q.transpose - 1) * A := by
  unfold conjugate
  noncomm_ring

/-- Manuscript equation (displacement-rank): small movement bounds displacement rank. -/
theorem displacement_rank_le {n r : ℕ} (A Q : RealMatrix n)
    (hr : (Q - 1).rank ≤ r) :
    (conjugate A Q - A).rank ≤ 2 * r := by
  rw [conjugate_sub_eq]
  have h₁ := Matrix.rank_mul_le_right (Q.transpose * A) (Q - 1)
  have h₂ := Matrix.rank_mul_le_left (Q.transpose - 1) A
  have ht : (Q.transpose - 1).rank = (Q - 1).rank := by
    have hmat : Q.transpose - 1 = (Q - 1).transpose := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.transpose_apply, h, eq_comm]
    rw [hmat]
    exact Matrix.rank_transpose (Q - (1 : RealMatrix n))
  have hsum := matrix_rank_add_le (Q.transpose * A * (Q - 1))
    ((Q.transpose - 1) * A)
  rw [ht] at h₂
  omega

end AdaptiveOrthogonalRigidity
