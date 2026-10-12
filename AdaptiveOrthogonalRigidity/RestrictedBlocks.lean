import AdaptiveOrthogonalRigidity.GramAtoms

open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

theorem sum_subtype_eq_of_zero {ι : Type*} [Fintype ι] (P : ι → Prop)
    (f : ι → ℝ) (hz : ∀ i, ¬ P i → f i = 0) :
    (∑ i : {i // P i}, f i.val) = ∑ i, f i := by
  have h := Fintype.sum_subtype_add_sum_subtype P f
  have ho : (∑ i : {i // ¬ P i}, f i.val) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact hz i.val i.property
  simpa only [ho, add_zero] using h

def restrictedColumn {n : ℕ} (Q : RealMatrix n) (s : Setoid (Fin n)) (j : Fin n) :
    {i : Fin n // s.r j i} → ℝ := fun i => Q i.val j

theorem restrictedColumn_norm {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (s : Setoid (Fin n)) (hs : ∀ i j, ¬ s.r i j → Q i j = 0) (j : Fin n) :
    (∑ i, restrictedColumn Q s j i ^ 2) = 1 := by
  unfold restrictedColumn
  rw [sum_subtype_eq_of_zero (s.r j) (fun i => Q i j ^ 2)]
  · exact column_norm_sq Q hQ j
  · intro i hi
    rw [hs i j (fun h => hi (s.symm h))]
    simp

/-- Restriction to the actual physical block preserves noncoordinate status.
Coordinates outside that block vanish, so a restricted coordinate witness would
also be a forbidden ambient coordinate witness. -/
theorem restrictedColumn_noncoordinate {n : ℕ} (Q : RealMatrix n)
    (s : Setoid (Fin n)) (hs : ∀ i j, ¬ s.r i j → Q i j = 0) (j : Fin n)
    (hnon : ¬ IsSignedCoordinate (fun i => Q i j)) :
    ¬ IsSignedCoordinate (restrictedColumn Q s j) := by
  rintro ⟨k, hk, hzero⟩
  apply hnon
  refine ⟨k.val, hk, ?_⟩
  intro i hik
  by_cases hi : s.r j i
  · exact hzero ⟨i, hi⟩ (fun h => hik (congrArg Subtype.val h))
  · exact hs i j (fun h => hi (s.symm h))

/-- The normalized witness supplies a genuine unit noncoordinate vector on
every nontrivial block, in the same finite type used by the Gram atom theorem. -/
theorem noncoordinateBlock_restricted_vectors {n b : ℕ} (Q : RealMatrix n)
    (hQ : Orthogonal Q) (hblocks : NoncoordinateBlockDecomposition Q b) :
    ∃ s : Setoid (Fin n),
      (∀ i, Nat.card {j : Fin n // s.r i j} ≤ b) ∧
      (∀ i j, ¬ s.r i j → Q i j = 0) ∧
      (∀ j, (∑ i, restrictedColumn Q s j i ^ 2) = 1) ∧
      (∀ j, 2 ≤ Nat.card {i : Fin n // s.r j i} →
        ¬ IsSignedCoordinate (restrictedColumn Q s j)) := by
  obtain ⟨s, hsize, hs, hnon⟩ := hblocks
  refine ⟨s, hsize, hs, ?_, ?_⟩
  · intro j; exact restrictedColumn_norm Q hQ s hs j
  · intro j hj; exact restrictedColumn_noncoordinate Q s hs j (hnon j hj)

end AdaptiveOrthogonalRigidity
