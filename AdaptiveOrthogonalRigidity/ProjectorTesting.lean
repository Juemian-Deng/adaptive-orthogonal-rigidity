import AdaptiveOrthogonalRigidity.FiniteProjectors
import AdaptiveOrthogonalRigidity.TrainingSpan

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Testing an already determined finite set of actual noncoordinate unit
projectors on fresh, independent rectangles, with varying nonempty widths. -/
theorem finite_projector_testing_bound {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ] (κ : τ → Type*)
    [∀ t, Fintype (κ t)] [∀ t, DecidableEq (κ t)] [∀ t, Nonempty (κ t)]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : (Σ t, ι × κ t) → unitInterval)
    (hp : ∀ e, α ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - α)
    (C : Set (SymmetricSpace ℝ ι)) (hfinite : C.Finite) (N : ℕ) (hcard : Nat.card C ≤ N) :
    (cubeMeasure p).real {X | ∃ T ∈ C, IsNoncoordinateProjector T ∧
      ∀ t, ∃ k : ℤ, (T.val * (gramSymmetric (R := ℝ) (fun e => X ⟨t, e⟩)).val).trace = k} ≤
        (N : ℝ) * (1 - α ^ 2) ^ Fintype.card τ := by
  have : Finite C := hfinite.to_subtype
  let := Fintype.ofFinite C
  let D := (1 - α ^ 2) ^ Fintype.card τ
  have hD : 0 ≤ D := pow_nonneg (by nlinarith) _
  let F (T : C) : Set ((Σ t, ι × κ t) → Bool) :=
    {X | IsNoncoordinateProjector T.val ∧
      ∀ t, ∃ k : ℤ, (T.val.val * (gramSymmetric (R := ℝ) (fun e => X ⟨t, e⟩)).val).trace = k}
  have hF (T : C) : (cubeMeasure p).real (F T) ≤ D := by
    by_cases hT : IsNoncoordinateProjector T.val
    · obtain ⟨u, hu, hnon, hTu⟩ := hT
      have hb := cube_family_event_le (fun t => ι × κ t) p
        (fun t => {Y | ∃ k : ℤ,
          quadraticValue (cubeMatrix Y * (cubeMatrix Y).transpose) u = k})
        (1 - α ^ 2) (fun t => real_gram_integer_atom hα
          (fun e => p ⟨t, e⟩) (fun e => hp ⟨t, e⟩) u hu hnon)
      apply (measureReal_mono (show F T ⊆ _ from ?_)).trans hb
      intro X hX t
      have ht := hX.2 t
      rw [hTu, vectorProjector_trace] at ht
      exact ht
    · simpa [F, hT] using hD
  calc
    _ ≤ (cubeMeasure p).real (⋃ T : C, F T) := by
      refine measureReal_mono ?_ (by finiteness)
      rintro X ⟨T, hTC, hT, htests⟩
      exact Set.mem_iUnion.mpr ⟨⟨T, hTC⟩, hT, htests⟩
    _ ≤ ∑ T : C, (cubeMeasure p).real (F T) := measureReal_iUnion_fintype_le F
    _ ≤ ∑ _T : C, D := Finset.sum_le_sum (fun T _ => hF T)
    _ = (Nat.card C : ℝ) * D := by simp [Nat.card_eq_fintype_card]
    _ ≤ (N : ℝ) * D := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hD

/-- After full-span integer training, the testing probability already includes
all unknown real unit vectors compatible with the bounded training values. -/
theorem integer_training_testing_bound {ι σ τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ] (κ : τ → Type*)
    [∀ t, Fintype (κ t)] [∀ t, DecidableEq (κ t)] [∀ t, Nonempty (κ t)]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : (Σ t, ι × κ t) → unitInterval)
    (hp : ∀ e, α ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - α)
    (G : σ → SymmetricSpace ℤ ι)
    (hspan : Submodule.span (ZMod 3) (Set.range (fun t => castSymmetric (ZMod 3) (G t))) = ⊤)
    (b : ℕ) :
    (cubeMeasure p).real {X | ∃ u : ι → ℝ, (∑ i, u i ^ 2 = 1) ∧ ¬ IsSignedCoordinate u ∧
      (∀ s, ∃ m : ℕ, m ≤ b ∧ quadraticValue (castSymmetric ℝ (G s)).val u = m) ∧
      ∀ t, ∃ k : ℤ, quadraticValue (gramSymmetric (R := ℝ) (fun e => X ⟨t, e⟩)).val u = k} ≤
        (b + 1 : ℝ) ^ (Fintype.card ι * (Fintype.card ι + 1) / 2) *
          (1 - α ^ 2) ^ Fintype.card τ := by
  obtain ⟨hfinite, hcard⟩ := integer_training_candidates_bound G hspan b
  have hb := finite_projector_testing_bound κ hα hα1 p hp
    (boundedTraceCandidates (fun s => castSymmetric ℝ (G s)) b) hfinite
    ((b + 1) ^ (Fintype.card ι * (Fintype.card ι + 1) / 2)) hcard
  have hsub : {X : (Σ t, ι × κ t) → Bool | ∃ u : ι → ℝ, (∑ i, u i ^ 2 = 1) ∧ ¬ IsSignedCoordinate u ∧
      (∀ s, ∃ m : ℕ, m ≤ b ∧ quadraticValue (castSymmetric ℝ (G s)).val u = m) ∧
      ∀ t, ∃ k : ℤ, quadraticValue (gramSymmetric (R := ℝ) (fun e => X ⟨t, e⟩)).val u = k} ⊆
      {X | ∃ T ∈ boundedTraceCandidates (fun s => castSymmetric ℝ (G s)) b,
        IsNoncoordinateProjector T ∧
        ∀ t, ∃ k : ℤ, (T.val * (gramSymmetric (R := ℝ) (fun e => X ⟨t, e⟩)).val).trace = k} := by
    rintro X ⟨u, hu, hnon, htrain, htest⟩
    refine ⟨vectorProjector u, ?_, ⟨u, hu, hnon, rfl⟩, ?_⟩
    · intro s
      simpa only [vectorProjector_trace] using htrain s
    · intro t
      simpa only [vectorProjector_trace] using htest t
  have h := (measureReal_mono hsub).trans hb
  simpa using h

end AdaptiveOrthogonalRigidity
