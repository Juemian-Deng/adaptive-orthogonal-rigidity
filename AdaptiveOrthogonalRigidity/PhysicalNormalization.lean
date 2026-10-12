import AdaptiveOrthogonalRigidity.PermutationAlgebra
import AdaptiveOrthogonalRigidity.SupportComponents

open scoped BigOperators

namespace AdaptiveOrthogonalRigidity

/-- A nonzero determinant supplies a perfect matching of nonzero entries. -/
theorem support_perfect_matching {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, Q i (σ i) ≠ 0 := by
  classical
  have hdet : Q.det ≠ 0 := by
    have h := congrArg Matrix.det hQ.1
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    intro hz
    simp [hz] at h
  rw [Matrix.det_apply] at hdet
  obtain ⟨τ, _, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
  have hp : (∏ i, Q (τ i) i) ≠ 0 := by
    intro hz
    simp [hz] at hτ
  refine ⟨τ.symm, ?_⟩
  intro i hz
  have hz' : Q (τ (τ.symm i)) (τ.symm i) = 0 := by simpa using hz
  exact hp (Finset.prod_eq_zero (Finset.mem_univ (τ.symm i)) hz')

theorem supportAdjacent_symm {n : ℕ} {Q : RealMatrix n}
    {v w : Fin n ⊕ Fin n} (h : SupportAdjacent Q v w) :
    SupportAdjacent Q w v := by
  cases v <;> cases w <;> exact h

theorem supportReachable_symm {n : ℕ} {Q : RealMatrix n}
    {v w : Fin n ⊕ Fin n} (h : SupportReachable Q v w) :
    SupportReachable Q w v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h₁ h₂ ih =>
    exact (Relation.ReflTransGen.tail Relation.ReflTransGen.refl
      (supportAdjacent_symm h₂)).trans ih

/-- Connected support rows form an honest partition of the original physical vertices. -/
def supportRowSetoid {n : ℕ} (Q : RealMatrix n) : Setoid (Fin n) where
  r i j := SupportReachable Q (Sum.inl i) (Sum.inl j)
  iseqv := ⟨fun _ => Relation.ReflTransGen.refl,
    fun h => supportReachable_symm h, fun h₁ h₂ => h₁.trans h₂⟩

/-- A partition of the physical vertex set into blocks of size at most b,
with all matrix entries between distinct blocks zero. -/
def PhysicalBlockDecomposition {n : ℕ} (Q : RealMatrix n) (b : ℕ) : Prop :=
  ∃ s : Setoid (Fin n),
    (∀ i, Nat.card {j : Fin n // s.r i j} ≤ b) ∧
    (∀ i j, ¬ s.r i j → Q i j = 0)

/-- An ordinary permutation of target coordinates puts each support component
on a physical row block, without permuting any sampled input coordinates. -/
theorem normalize_support_components {n b : ℕ} (Q : RealMatrix n)
    (hQ : Orthogonal Q) (hcap : SupportComponentCap Q b) :
    ∃ σ : Equiv.Perm (Fin n),
      PhysicalBlockDecomposition (Q * (permutationMatrix σ).transpose) b := by
  obtain ⟨σ, hσ⟩ := support_perfect_matching Q hQ
  refine ⟨σ, supportRowSetoid Q, ?_, ?_⟩
  · intro i
    exact hcap (Sum.inl i)
  · intro i j hnot
    have hent : (Q * (permutationMatrix σ).transpose) i j = Q i (σ j) := by
      rw [permutationMatrix_transpose, mul_permutationMatrix_apply]
      rfl
    rw [hent]
    by_contra hne
    apply hnot
    have hstep : SupportReachable Q (Sum.inl i) (Sum.inr (σ j)) :=
      Relation.ReflTransGen.tail Relation.ReflTransGen.refl hne
    exact Relation.ReflTransGen.tail hstep (hσ j)

def physicalBlockEvent (n b : ℕ) : Set (GraphSample n) :=
  {ω | ∃ Q B : RealMatrix n,
    Orthogonal Q ∧ Ordinary B ∧ B = conjugate (adjacency ω) Q ∧
    ¬ OrdinarilyIsomorphic (adjacency ω) B ∧ PhysicalBlockDecomposition Q b}

/-- Inclusion needed for the finite partition union bound. It retains the whole
target up to an ordinary target permutation and leaves the random graph unchanged. -/
theorem blockEvent_subset_physicalBlockEvent (n b : ℕ) :
    blockEvent n b ⊆ physicalBlockEvent n b := by
  intro ω hω
  obtain ⟨Q, B, hQ, hB, htarget, hnoniso, hcap⟩ := hω
  obtain ⟨σ, hblocks⟩ := normalize_support_components Q hQ hcap
  let P := permutationMatrix σ
  have hP : Orthogonal P := permutationMatrix_orthogonal σ
  refine ⟨Q * P.transpose, conjugate B P.transpose,
    orthogonal_mul Q P.transpose hQ (orthogonal_transpose P hP), ?_, ?_, ?_, hblocks⟩
  · rw [show P.transpose = permutationMatrix σ.symm from permutationMatrix_transpose σ]
    exact ordinary_permutation_conjugate B hB σ.symm
  · rw [conjugate_mul, ← htarget]
  · intro h
    apply hnoniso
    apply ordinarilyIsomorphic_trans h
    exact ⟨σ, (conjugate_transpose_cancel B P hP).symm⟩

end AdaptiveOrthogonalRigidity
