import AdaptiveOrthogonalRigidity.ProductFibers

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Exact independence for arbitrarily sized disjoint original-coordinate
families. Events may themselves existentially quantify over real witnesses. -/
theorem cube_family_event_probability {τ : Type*} [Fintype τ] [DecidableEq τ]
    (ι : τ → Type*) [∀ t, Fintype (ι t)] [∀ t, DecidableEq (ι t)]
    (p : (Σ t, ι t) → unitInterval) (E : ∀ t, Set (ι t → Bool)) :
    (cubeMeasure p).real {X | ∀ t, (fun i => X ⟨t, i⟩) ∈ E t} =
      ∏ t, (cubeMeasure (fun i => p ⟨t, i⟩)).real (E t) := by
  rw [cubeMeasure_real_eq_sum]
  simp_rw [cubeMeasure_real_eq_sum]
  simp only [Set.mem_ofPred_eq]
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv (Equiv.piCurry (fun (t : τ) (_ : ι t) => Bool))
  intro Y
  by_cases h : ∀ t, (fun i => Y ⟨t, i⟩) ∈ E t
  · rw [ite_eq_left h]
    have h' (t : τ) : (Equiv.piCurry (fun (t : τ) (_ : ι t) => Bool)) Y t ∈ E t := h t
    simp_rw [ite_eq_left (h' _)]
    exact Fintype.prod_sigma _
  · rw [ite_eq_right h]
    symm
    push Not at h
    obtain ⟨t, ht⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ t)
    exact ite_eq_right ht

theorem cube_family_event_le {τ : Type*} [Fintype τ] [DecidableEq τ]
    (ι : τ → Type*) [∀ t, Fintype (ι t)] [∀ t, DecidableEq (ι t)]
    (p : (Σ t, ι t) → unitInterval) (E : ∀ t, Set (ι t → Bool)) (C : ℝ)
    (hbound : ∀ t, (cubeMeasure (fun i => p ⟨t, i⟩)).real (E t) ≤ C) :
    (cubeMeasure p).real {X | ∀ t, (fun i => X ⟨t, i⟩) ∈ E t} ≤ C ^ Fintype.card τ := by
  rw [cube_family_event_probability]
  calc
    _ ≤ ∏ _t : τ, C := by
      apply Finset.prod_le_prod₀
      · intro t _; exact measureReal_nonneg
      · intro t _; exact hbound t
    _ = _ := by simp

end AdaptiveOrthogonalRigidity
