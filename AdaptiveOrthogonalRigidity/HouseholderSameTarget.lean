import AdaptiveOrthogonalRigidity.HouseholderMovement

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

theorem eigenvector_householder_commute {n : ℕ} (A : RealMatrix n) (hA : A.IsSymm)
    (u : Fin n → ℝ) (μ : ℝ) (hu : A.mulVec u = μ • u) :
    A * householderMatrix u = householderMatrix u * A := by
  have hrow : u ᵥ* A = μ • u := by
    rw [← hA, Matrix.vecMul_transpose]
    exact hu
  simp only [householderMatrix, mul_sub, sub_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    hu, hrow, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]

theorem eigenvector_householder_same_target {n : ℕ} (A Q : RealMatrix n) (hA : A.IsSymm)
    (u : Fin n → ℝ) (hu : u ≠ 0) (μ : ℝ) (heigen : A.mulVec u = μ • u) :
    conjugate A (householderMatrix u * Q) = conjugate A Q := by
  rw [conjugate_mul]
  congr 1
  unfold conjugate
  rw [householderMatrix_transpose, ← eigenvector_householder_commute A hA u μ heigen,
    Matrix.mul_assoc, householderMatrix_square u hu, Matrix.mul_one]

/-- A same-target witness of no larger rank whose movement contains no
nonzero eigenvector. All reflections are constructed, not postulated. -/
theorem exists_same_target_no_movement_eigenvector {n : ℕ} (A Q : RealMatrix n)
    (hA : A.IsSymm) (hQ : Orthogonal Q) :
    ∃ Q₀ : RealMatrix n, Orthogonal Q₀ ∧ conjugate A Q₀ = conjugate A Q ∧
      (Q₀ - 1).rank ≤ (Q - 1).rank ∧
      ∀ u ∈ (Q₀ - 1).mulVecLin.range, ∀ μ : ℝ, A.mulVec u = μ • u → u = 0 := by
  generalize h_rank : (Q - 1).rank = r
  induction r using Nat.strong_induction_on generalizing Q with
  | h r ih =>
    by_cases hnone : ∀ u ∈ (Q - 1).mulVecLin.range, ∀ μ : ℝ, A.mulVec u = μ • u → u = 0
    · exact ⟨Q, hQ, rfl, h_rank.le, hnone⟩
    · push Not at hnone
      obtain ⟨u, hmove, μ, heigen, hu⟩ := hnone
      let Q' := householderMatrix u * Q
      have hQ' : Orthogonal Q' := orthogonal_mul _ _ (householderMatrix_orthogonal u hu) hQ
      have htarget : conjugate A Q' = conjugate A Q :=
        eigenvector_householder_same_target A Q hA u hu μ heigen
      have hdrop : (Q' - 1).rank < r := by
        rw [← h_rank]
        exact householder_movement_rank_drop Q hQ u hu hmove
      obtain ⟨Q₀, hQ₀, ht₀, hr₀, hn₀⟩ := ih _ hdrop Q' hQ' rfl
      exact ⟨Q₀, hQ₀, ht₀.trans htarget, hr₀.trans hdrop.le, hn₀⟩

end AdaptiveOrthogonalRigidity
