import AdaptiveOrthogonalRigidity.MovementImage

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Reflection in the hyperplane perpendicular to u, in original coordinates. -/
noncomputable def householderMatrix {n : ℕ} (u : Fin n → ℝ) : RealMatrix n :=
  1 - (2 / (u ⬝ᵥ u)) • Matrix.vecMulVec u u

theorem householderMatrix_mulVec {n : ℕ} (u x : Fin n → ℝ) :
    (householderMatrix u).mulVec x = x - (2 * (u ⬝ᵥ x) / (u ⬝ᵥ u)) • u := by
  simp only [householderMatrix, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, op_smul_eq_mul]
  ring

theorem householderMatrix_transpose {n : ℕ} (u : Fin n → ℝ) :
    (householderMatrix u).transpose = householderMatrix u := by
  simp only [householderMatrix, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_smul, Matrix.transpose_vecMulVec]

theorem householderMatrix_square {n : ℕ} (u : Fin n → ℝ) (hu : u ≠ 0) :
    householderMatrix u * householderMatrix u = 1 := by
  have hd : u ⬝ᵥ u ≠ 0 := fun h => hu (dotProduct_self_eq_zero.mp h)
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [← Matrix.mulVec_mulVec, householderMatrix_mulVec, householderMatrix_mulVec,
    Matrix.one_mulVec]
  simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem householderMatrix_orthogonal {n : ℕ} (u : Fin n → ℝ) (hu : u ≠ 0) :
    Orthogonal (householderMatrix u) := by
  constructor <;> rw [householderMatrix_transpose] <;> exact householderMatrix_square u hu

theorem householderMatrix_fixed {n : ℕ} (u x : Fin n → ℝ) (hx : u ⬝ᵥ x = 0) :
    (householderMatrix u).mulVec x = x := by
  rw [householderMatrix_mulVec, hx, mul_zero, zero_div, zero_smul, sub_zero]

/-- A reflection in a nonzero movement direction preserves all old fixed
vectors and creates an additional one. This yields strict rank descent without
complex eigenvalues or determinant parity. -/
theorem householder_movement_rank_drop {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (u : Fin n → ℝ) (hu : u ≠ 0) (hmove : u ∈ (Q - 1).mulVecLin.range) :
    (householderMatrix u * Q - 1).rank < (Q - 1).rank := by
  obtain ⟨w, hw⟩ := hmove
  change (Q - 1).mulVec w = u at hw
  have hle : (Q - 1).mulVecLin.ker ≤ (householderMatrix u * Q - 1).mulVecLin.ker := by
    intro x hx
    change (Q - 1).mulVec x = 0 at hx
    have hfix : Q.mulVec x = x := by
      simpa only [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] using hx
    have hdot : u ⬝ᵥ x = 0 := by
      rw [← hw, dotProduct_comm, ← dotProduct_transpose_mulVec]
      rw [(movement_transpose_kernel_iff Q hQ x).mpr hx, dotProduct_zero]
    change (householderMatrix u * Q - 1).mulVec x = 0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hfix,
      householderMatrix_fixed u x hdot, sub_self]
  have hnew : w ∈ (householderMatrix u * Q - 1).mulVecLin.ker := by
    have hd : u ⬝ᵥ u ≠ 0 := fun h => hu (dotProduct_self_eq_zero.mp h)
    have hquad := orthogonal_movement_quadratic Q hQ w
    rw [hw] at hquad
    have hQw : Q.mulVec w = w + u := by
      have hh : Q.mulVec w - w = u := by simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using hw
      have ht := (sub_eq_iff_eq_add).mp hh
      simpa only [add_comm] using ht
    have hcoef : 2 * (u ⬝ᵥ Q.mulVec w) / (u ⬝ᵥ u) = 1 := by
      rw [hQw, dotProduct_add, dotProduct_comm u w]
      apply (div_eq_one_iff_eq hd).mpr
      linarith
    change (householderMatrix u * Q - 1).mulVec w = 0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      householderMatrix_mulVec, hcoef, one_smul, hQw, add_sub_cancel_right, sub_self]
  have hnot : w ∉ (Q - 1).mulVecLin.ker := by
    intro hz
    exact hu (hw.symm.trans hz)
  have hlt : (Q - 1).mulVecLin.ker < (householderMatrix u * Q - 1).mulVecLin.ker := by
    apply lt_of_le_of_ne hle
    intro heq
    exact hnot (heq ▸ hnew)
  have hd := Submodule.finrank_lt_finrank_of_lt hlt
  have h1 := (Q - 1).mulVecLin.finrank_range_add_finrank_ker
  have h2 := (householderMatrix u * Q - 1).mulVecLin.finrank_range_add_finrank_ker
  change Module.finrank ℝ (householderMatrix u * Q - 1).mulVecLin.range <
    Module.finrank ℝ (Q - 1).mulVecLin.range
  omega

end AdaptiveOrthogonalRigidity
