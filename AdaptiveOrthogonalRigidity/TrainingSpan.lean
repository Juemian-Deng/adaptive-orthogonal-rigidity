import AdaptiveOrthogonalRigidity.SymmetricSpace
import AdaptiveOrthogonalRigidity.GramAtoms
import AdaptiveOrthogonalRigidity.IndependentFamilies

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

private theorem f3_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

def gramSymmetric {ι κ R : Type*} [Fintype κ] [CommRing R]
    (X : ι × κ → Bool) : SymmetricSpace R ι :=
  ⟨cubeMatrix X * (cubeMatrix X).transpose, by
    change (cubeMatrix (R := R) X * (cubeMatrix (R := R) X).transpose).transpose = _
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]⟩

/-- Exact training-span failure bound for independent nonempty rectangles of
possibly different widths. No unknown real vector has been fixed or conditioned on. -/
theorem training_gram_span_failure {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ] (κ : τ → Type*)
    [∀ t, Fintype (κ t)] [∀ t, DecidableEq (κ t)] [∀ t, Nonempty (κ t)]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : (Σ t, ι × κ t) → unitInterval)
    (hp : ∀ e, α ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - α) :
    (cubeMeasure p).real {X |
      Submodule.span (ZMod 3) (Set.range (fun t =>
        gramSymmetric (R := ZMod 3) (fun e => X ⟨t, e⟩))) ≠ ⊤} ≤
      (3 : ℝ) ^ (Fintype.card ι * (Fintype.card ι + 1) / 2) *
        (1 - α ^ 2) ^ Fintype.card τ := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  let C := (1 - α ^ 2) ^ Fintype.card τ
  have hC : 0 ≤ C := pow_nonneg (by nlinarith) _
  let F (H : SymmetricSpace (ZMod 3) ι) : Set ((Σ t, ι × κ t) → Bool) :=
    {X | H ≠ 0 ∧ ∀ t, (H.val * (gramSymmetric (R := ZMod 3) (fun e => X ⟨t, e⟩)).val).trace = 0}
  have hF (H : SymmetricSpace (ZMod 3) ι) : (cubeMeasure p).real (F H) ≤ C := by
    by_cases hH : H = 0
    · simpa [F, hH] using hC
    · have hn : H.val ≠ 0 := by
        intro hz
        exact hH (Subtype.ext hz)
      have hb := cube_family_event_le (fun t => ι × κ t) p
        (fun t => {Y | (H.val * (gramSymmetric (R := ZMod 3) Y).val).trace = 0})
        (1 - α ^ 2) (fun t => f3_gram_atom hα hα1
          (fun e => p ⟨t, e⟩) (fun e => hp ⟨t, e⟩) H.val H.property hn 0)
      apply (measureReal_mono (show F H ⊆ _ from fun X hX => hX.2)).trans hb
  calc
    _ ≤ (cubeMeasure p).real (⋃ H, F H) := by
      refine measureReal_mono ?_ (by finiteness)
      intro X hX
      obtain ⟨H, hH, htrace⟩ := exists_symmetric_trace_annihilator f3_two_ne_zero
        (fun t => gramSymmetric (R := ZMod 3) (fun e => X ⟨t, e⟩)) hX
      exact Set.mem_iUnion.mpr ⟨H, hH, htrace⟩
    _ ≤ ∑ H, (cubeMeasure p).real (F H) := measureReal_iUnion_fintype_le F
    _ ≤ ∑ _H : SymmetricSpace (ZMod 3) ι, C := Finset.sum_le_sum (fun H _ => hF H)
    _ = _ := by simp [C, symmetric_space_card]

end AdaptiveOrthogonalRigidity
