import AdaptiveOrthogonalRigidity.ModelLemmas
import AdaptiveOrthogonalRigidity.OrthogonalAlgebra

namespace AdaptiveOrthogonalRigidity

theorem permutationMatrix_mul_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (A : RealMatrix n) (i j : Fin n) :
    (permutationMatrix σ * A) i j = A (σ i) j := by
  simp [Matrix.mul_apply, permutationMatrix, ite_mul]

theorem mul_permutationMatrix_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (A : RealMatrix n) (i j : Fin n) :
    (A * permutationMatrix σ) i j = A i (σ.symm j) := by
  simp [Matrix.mul_apply, permutationMatrix, ← Equiv.eq_symm_apply, mul_ite]

theorem permutationMatrix_transpose {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (permutationMatrix σ).transpose = permutationMatrix σ.symm := by
  ext i j
  by_cases h : σ j = i
  · have hh : σ.symm i = j := by
      apply σ.injective
      simpa using h.symm
    simp [Matrix.transpose_apply, permutationMatrix, h, hh]
  · have hh : σ.symm i ≠ j := by
      intro he
      apply h
      calc
        σ j = σ (σ.symm i) := congrArg σ he.symm
        _ = i := σ.apply_symm_apply i
    simp [Matrix.transpose_apply, permutationMatrix, h, hh]

theorem permutationMatrix_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    permutationMatrix σ * permutationMatrix τ = permutationMatrix (σ.trans τ) := by
  ext i j
  rw [permutationMatrix_mul_apply]
  rfl

theorem permutationMatrix_orthogonal {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Orthogonal (permutationMatrix σ) := by
  constructor <;> rw [permutationMatrix_transpose, permutationMatrix_mul] <;> simp

theorem permutation_conjugate_apply {n : ℕ} (A : RealMatrix n)
    (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    conjugate A (permutationMatrix σ) i j = A (σ.symm i) (σ.symm j) := by
  unfold conjugate
  rw [permutationMatrix_transpose, mul_permutationMatrix_apply, permutationMatrix_mul_apply]

theorem ordinary_permutation_conjugate {n : ℕ} (A : RealMatrix n)
    (hA : Ordinary A) (σ : Equiv.Perm (Fin n)) :
    Ordinary (conjugate A (permutationMatrix σ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simp only [permutation_conjugate_apply]
    exact hA.1 _ _
  · intro i
    simp only [permutation_conjugate_apply]
    exact hA.2.1 _
  · intro i j
    simp only [permutation_conjugate_apply]
    exact hA.2.2 _ _

theorem ordinarilyIsomorphic_trans {n : ℕ} {A B C : RealMatrix n}
    (hAB : OrdinarilyIsomorphic A B) (hBC : OrdinarilyIsomorphic B C) :
    OrdinarilyIsomorphic A C := by
  obtain ⟨σ, rfl⟩ := hAB
  obtain ⟨τ, rfl⟩ := hBC
  exact ⟨σ.trans τ, by rw [← permutationMatrix_mul, conjugate_mul]⟩

/-- The identity-relative event used in the finite proof. -/
def identityMovementEvent (n r : ℕ) : Set (GraphSample n) :=
  {ω | ∃ Q B : RealMatrix n,
    Orthogonal Q ∧ Ordinary B ∧ B = conjugate (adjacency ω) Q ∧
    ¬ OrdinarilyIsomorphic (adjacency ω) B ∧ (Q - 1).rank ≤ r}

/-- Target-only ordinary permutation normalization is an equality of adaptive events.
The sampled input is unchanged, and no union over the permutation group is needed. -/
theorem movementEvent_eq_identityMovementEvent (n r : ℕ) :
    movementEvent n r = identityMovementEvent n r := by
  ext ω
  constructor
  · rintro ⟨Q, B, hQ, hB, htarget, hnoniso, σ, hr⟩
    let P := permutationMatrix σ
    have hP : Orthogonal P := permutationMatrix_orthogonal σ
    refine ⟨Q * P.transpose, conjugate B P.transpose,
      orthogonal_mul Q P.transpose hQ (orthogonal_transpose P hP), ?_, ?_, ?_, ?_⟩
    · rw [show P.transpose = permutationMatrix σ.symm from permutationMatrix_transpose σ]
      exact ordinary_permutation_conjugate B hB σ.symm
    · rw [conjugate_mul, ← htarget]
    · intro h
      apply hnoniso
      apply ordinarilyIsomorphic_trans h
      exact ⟨σ, (conjugate_transpose_cancel B P hP).symm⟩
    · exact (normalized_movement_rank_le Q P hP).trans hr
  · rintro ⟨Q, B, hQ, hB, htarget, hnoniso, hr⟩
    refine ⟨Q, B, hQ, hB, htarget, hnoniso, Equiv.refl _, ?_⟩
    simpa using hr

end AdaptiveOrthogonalRigidity
