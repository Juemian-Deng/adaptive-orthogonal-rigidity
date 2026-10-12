import AdaptiveOrthogonalRigidity.TrivialBlocks

open scoped BigOperators

namespace AdaptiveOrthogonalRigidity

def IsSignedCoordinate {ι : Type*} (u : ι → ℝ) : Prop :=
  ∃ k, (u k = 1 ∨ u k = -1) ∧ ∀ i, i ≠ k → u i = 0

theorem other_coordinate_zero_of_sq_one {n : ℕ} (u : Fin n → ℝ)
    (hnorm : ∑ i, u i ^ 2 = 1) (j : Fin n) (hj : u j ^ 2 = 1)
    (k : Fin n) (hkj : k ≠ j) : u k = 0 := by
  have hs := Finset.sum_erase_add (s := Finset.univ) (f := fun i => u i ^ 2)
    (Finset.mem_univ j)
  have hrest : (∑ i ∈ Finset.univ.erase j, u i ^ 2) = 0 := by
    rw [hnorm, hj] at hs
    linarith
  have hle : u k ^ 2 ≤ ∑ i ∈ Finset.univ.erase j, u i ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (u i))
      (Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩)
  rw [hrest] at hle
  nlinarith [sq_nonneg (u k)]

/-- If one orthogonal column is supported at one row, that row has no other support. -/
theorem singleton_column_isolates_row {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (k j : Fin n) (hcol : ∀ i, i ≠ k → Q i j = 0) :
    ∀ l, l ≠ j → Q k l = 0 := by
  have hsq : Q k j ^ 2 = 1 := by
    have hsum : (∑ i, Q i j ^ 2) = Q k j ^ 2 := by
      apply Finset.sum_eq_single k
      · intro i _ hik
        simp [hcol i hik]
      · simp
    rw [← hsum]
    exact column_norm_sq Q hQ j
  intro l hlj
  exact other_coordinate_zero_of_sq_one (fun l => Q k l) (row_norm_sq Q hQ k) j hsq l hlj

/-- A path starting at an isolated support pair stays within that pair. -/
theorem supportReachable_isolated_pair {n : ℕ} (Q : RealMatrix n) (k j : Fin n)
    (hrow : ∀ l, l ≠ j → Q k l = 0) (hcol : ∀ i, i ≠ k → Q i j = 0)
    {w : Fin n ⊕ Fin n} (h : SupportReachable Q (Sum.inl k) w) :
    w = Sum.inl k ∨ w = Sum.inr j := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail v w h₁ h₂ ih =>
    rcases ih with hv | hv
    · subst v
      cases w with
      | inl i => exact False.elim h₂
      | inr l =>
        right
        have hlj : l = j := by
          by_contra hn
          exact h₂ (hrow l hn)
        exact congrArg Sum.inr hlj
    · subst v
      cases w with
      | inl i =>
        left
        have hik : i = k := by
          by_contra hn
          exact h₂ (hcol i hn)
        exact congrArg Sum.inl hik
      | inr l => exact False.elim h₂

theorem singleton_column_component_card_le_one {n : ℕ} (Q : RealMatrix n)
    (hQ : Orthogonal Q) (k j : Fin n) (hcol : ∀ i, i ≠ k → Q i j = 0) :
    Nat.card {i : Fin n // SupportReachable Q (Sum.inl k) (Sum.inl i)} ≤ 1 := by
  classical
  have hrow := singleton_column_isolates_row Q hQ k j hcol
  have heq (i : Fin n) (hi : SupportReachable Q (Sum.inl k) (Sum.inl i)) : i = k := by
    rcases supportReachable_isolated_pair Q k j hrow hcol hi with h | h
    · exact Sum.inl.inj h
    · cases h
  let : Subsingleton {i : Fin n // SupportReachable Q (Sum.inl k) (Sum.inl i)} :=
    ⟨fun a b => Subtype.ext ((heq a.val a.property).trans (heq b.val b.property).symm)⟩
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance

/-- Every column in a nontrivial actual support component is noncoordinate. -/
theorem actual_component_column_noncoordinate {n : ℕ} (Q : RealMatrix n)
    (hQ : Orthogonal Q) (k j : Fin n) (hkj : Q k j ≠ 0)
    (hsize : 2 ≤ Nat.card {i : Fin n // SupportReachable Q (Sum.inl k) (Sum.inl i)}) :
    ¬ IsSignedCoordinate (fun i => Q i j) := by
  rintro ⟨l, _, hcol⟩
  have hkl : k = l := by
    by_contra hn
    exact hkj (hcol k hn)
  subst l
  have hsmall := singleton_column_component_card_le_one Q hQ k j hcol
  omega

/-- A strengthened physical interface retaining the noncoordinate-column property
of every nontrivial block. It does not identify coarse blocks with components. -/
def NoncoordinateBlockDecomposition {n : ℕ} (Q : RealMatrix n) (b : ℕ) : Prop :=
  ∃ s : Setoid (Fin n),
    (∀ i, Nat.card {j : Fin n // s.r i j} ≤ b) ∧
    (∀ i j, ¬ s.r i j → Q i j = 0) ∧
    (∀ j, 2 ≤ Nat.card {i : Fin n // s.r j i} →
      ¬ IsSignedCoordinate (fun i => Q i j))

theorem normalize_support_components_noncoordinate {n b : ℕ} (Q : RealMatrix n)
    (hQ : Orthogonal Q) (hcap : SupportComponentCap Q b) :
    ∃ σ : Equiv.Perm (Fin n),
      NoncoordinateBlockDecomposition (Q * (permutationMatrix σ).transpose) b := by
  obtain ⟨σ, hσ⟩ := support_perfect_matching Q hQ
  have hent (i j : Fin n) :
      (Q * (permutationMatrix σ).transpose) i j = Q i (σ j) := by
    rw [permutationMatrix_transpose, mul_permutationMatrix_apply]
    rfl
  refine ⟨σ, supportRowSetoid Q, ?_, ?_, ?_⟩
  · intro i
    exact hcap (Sum.inl i)
  · intro i j hnot
    rw [hent]
    by_contra hne
    apply hnot
    have hstep : SupportReachable Q (Sum.inl i) (Sum.inr (σ j)) :=
      Relation.ReflTransGen.tail Relation.ReflTransGen.refl hne
    exact Relation.ReflTransGen.tail hstep (hσ j)
  · intro j hsize
    have hn := actual_component_column_noncoordinate Q hQ j (σ j) (hσ j) hsize
    simpa only [hent] using hn

/-- The finite block proof will bound this necessary event, which retains the
noncoordinate-column condition that coarse physical partitions alone do not give. -/
def noncoordinateBlockEvent (n b : ℕ) : Set (GraphSample n) :=
  {ω | ∃ Q B : RealMatrix n,
    Orthogonal Q ∧ Ordinary B ∧ B = conjugate (adjacency ω) Q ∧
    ¬ OrdinarilyIsomorphic (adjacency ω) B ∧ NoncoordinateBlockDecomposition Q b}

theorem blockEvent_subset_noncoordinateBlockEvent (n b : ℕ) :
    blockEvent n b ⊆ noncoordinateBlockEvent n b := by
  intro ω hω
  obtain ⟨Q, B, hQ, hB, htarget, hnoniso, hcap⟩ := hω
  obtain ⟨σ, hblocks⟩ := normalize_support_components_noncoordinate Q hQ hcap
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
