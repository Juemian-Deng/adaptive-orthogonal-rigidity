import AdaptiveOrthogonalRigidity.PhysicalNormalization
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace AdaptiveOrthogonalRigidity

theorem diagonal_conjugate_apply {n : ℕ} (A : RealMatrix n) (d : Fin n → ℝ)
    (i j : Fin n) :
    conjugate A (Matrix.diagonal d) i j = d i * A i j * d j := by
  simp [conjugate, Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- Sign conjugation cannot alter an ordinary graph while keeping the target ordinary. -/
theorem sign_conjugate_eq {n : ℕ} (A : RealMatrix n) (hA : Ordinary A)
    (d : Fin n → ℝ) (hd : ∀ i, d i = 1 ∨ d i = -1)
    (hB : Ordinary (conjugate A (Matrix.diagonal d))) :
    conjugate A (Matrix.diagonal d) = A := by
  ext i j
  have hbit := hB.2.2 i j
  rcases hA.2.2 i j with ha | ha
  · simp [diagonal_conjugate_apply, ha]
  · rcases hd i with hi | hi <;> rcases hd j with hj | hj <;>
      simp_all [diagonal_conjugate_apply]

/-- An orthogonal physical partition into singleton blocks is a diagonal sign matrix. -/
theorem physical_cap_one_diagonal {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (hblocks : PhysicalBlockDecomposition Q 1) :
    ∃ d : Fin n → ℝ, (∀ i, d i = 1 ∨ d i = -1) ∧ Q = Matrix.diagonal d := by
  classical
  obtain ⟨s, hcard, hzero⟩ := hblocks
  have hoff (i j : Fin n) (hij : i ≠ j) : Q i j = 0 := by
    apply hzero i j
    intro hrel
    have hc : Fintype.card {k : Fin n // s.r i k} ≤ 1 := by
      simpa [Nat.card_eq_fintype_card] using hcard i
    let : Subsingleton {k : Fin n // s.r i k} :=
      Fintype.card_le_one_iff_subsingleton.mp hc
    have heq : (⟨i, s.refl i⟩ : {k : Fin n // s.r i k}) = ⟨j, hrel⟩ :=
      Subsingleton.elim _ _
    exact hij (congrArg Subtype.val heq)
  refine ⟨fun i => Q i i, ?_, ?_⟩
  · intro i
    apply sq_eq_one_iff.mp
    have hsum : (∑ j, Q i j ^ 2) = Q i i ^ 2 := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        simp [hoff i j (Ne.symm hji)]
      · simp
    rw [← hsum]
    exact row_norm_sq Q hQ i
  · ext i j
    by_cases h : i = j
    · subst j
      simp
    · simp [h, hoff i j h]

theorem singleton_blocks_target_eq {n : ℕ} (A Q B : RealMatrix n)
    (hA : Ordinary A) (hQ : Orthogonal Q) (hB : Ordinary B)
    (htarget : B = conjugate A Q) (hblocks : PhysicalBlockDecomposition Q 1) :
    B = A := by
  obtain ⟨d, hd, hdiag⟩ := physical_cap_one_diagonal Q hQ hblocks
  rw [hdiag] at htarget
  have hB' : Ordinary (conjugate A (Matrix.diagonal d)) := htarget ▸ hB
  exact htarget.trans (sign_conjugate_eq A hA d hd hB')

/-- Any physical partition witnessing a nonisomorphic ordinary target has a nontrivial block. -/
theorem physical_witness_nontrivial_block {n : ℕ} (A Q B : RealMatrix n)
    (hA : Ordinary A) (hQ : Orthogonal Q) (hB : Ordinary B)
    (htarget : B = conjugate A Q) (hnoniso : ¬ OrdinarilyIsomorphic A B)
    (s : Setoid (Fin n)) (hzero : ∀ i j, ¬ s.r i j → Q i j = 0) :
    ∃ i, 2 ≤ Nat.card {j : Fin n // s.r i j} := by
  classical
  by_contra h
  push Not at h
  have hcard (i : Fin n) : Nat.card {j : Fin n // s.r i j} ≤ 1 := by
    have := h i
    omega
  have heq := singleton_blocks_target_eq A Q B hA hQ hB htarget ⟨s, hcard, hzero⟩
  apply hnoniso
  rw [heq]
  exact ordinarilyIsomorphic_refl A

end AdaptiveOrthogonalRigidity
