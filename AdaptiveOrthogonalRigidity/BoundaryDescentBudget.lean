import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic

namespace AdaptiveOrthogonalRigidity

/-- Finite state loss accounts for every enlarged-boundary cost. This purely
deterministic induction does not enumerate deletion paths. -/
theorem budgeted_boundary_descent {ι : Type*} [DecidableEq ι] (b R : ℕ)
    (W : Finset ι → ℕ → Prop) (Done : Finset ι → Prop)
    (hstep : ∀ (S : Finset ι) (k : ℕ), W S k → S.card + R * k ≤ b →
      Done S ∨ ∃ (S' : Finset ι) (k' : ℕ), S ⊆ S' ∧ k' < k ∧
        S'.card + R * k' ≤ S.card + R * k ∧ W S' k')
    (S : Finset ι) (k : ℕ) (hW : W S k) (hbudget : S.card + R * k ≤ b) :
    ∃ S' : Finset ι, S ⊆ S' ∧ S'.card ≤ S.card + R * k ∧ Done S' := by
  induction k using Nat.strong_induction_on generalizing S with
  | h k ih =>
    rcases hstep S k hW hbudget with hd | ⟨T, l, hST, hl, hcost, hT⟩
    · exact ⟨S, Finset.Subset.refl _, Nat.le_add_right _ _, hd⟩
    · obtain ⟨U, hTU, hU, hd⟩ := ih l hl T hT (hcost.trans hbudget)
      exact ⟨U, hST.trans hTU, hU.trans hcost, hd⟩

end AdaptiveOrthogonalRigidity
