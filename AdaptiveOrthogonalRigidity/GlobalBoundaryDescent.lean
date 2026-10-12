import AdaptiveOrthogonalRigidity.BoundaryStateTermination
import AdaptiveOrthogonalRigidity.IntegerBoundaryControlled
import AdaptiveOrthogonalRigidity.DescriptorRowTransport
import AdaptiveOrthogonalRigidity.GraphBoundaryDescriptorStep

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Repeated actual-boundary reduction ends with every target column in the
original enlarged input space, within the exact R times state budget. -/
theorem graph_boundary_descent_terminates {n b r R k : ℕ}
    (S₀ : Finset (Fin n)) (ω : GraphSample n) (Target : RealMatrix n)
    (D₀ : GraphBoundaryDescriptor S₀ ω Target k)
    (hkr : k ≤ r) (hR : 1 ≤ R) (hbudget : S₀.card + R * k ≤ b)
    (hblock : Target.submatrix (fun i : ↑S₀ᶜ => i.val) (fun j : ↑S₀ᶜ => j.val) =
      (adjacency ω).submatrix (fun i : ↑S₀ᶜ => i.val) (fun j : ↑S₀ᶜ => j.val))
    (hkGood : ω ∉ boundaryKrylovFailure n b (2 * r))
    (hdGood : ω ∉ boundaryDescriptorFailure n b r R) :
    ∃ S : Finset (Fin n), S₀ ⊆ S ∧ S.card ≤ S₀.card + R * k ∧
      Target.submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val) =
        (adjacency ω).submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val) ∧
      ((integerBoundaryOutputs S Target).map (Int.castRingHom (ZMod 3))).mulVecLin.range ≤
        ((integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3))).mulVecLin.range := by
  let W (S : Finset (Fin n)) (k : ℕ) : Prop := k ≤ r ∧
    Target.submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val) =
      (adjacency ω).submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val) ∧
    Nonempty (GraphBoundaryDescriptor S ω Target k)
  let Done (S : Finset (Fin n)) : Prop :=
    Target.submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val) =
      (adjacency ω).submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val) ∧
    ((integerBoundaryOutputs S Target).map (Int.castRingHom (ZMod 3))).mulVecLin.range ≤
      ((integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3))).mulVecLin.range
  have hstep : ∀ (S : Finset (Fin n)) (k : ℕ), W S k → S.card + R * k ≤ b →
      Done S ∨ ∃ (S' : Finset (Fin n)) (k' : ℕ), S ⊆ S' ∧ k' < k ∧
        S'.card + R * k' ≤ S.card + R * k ∧ W S' k' := by
    intro S k hW hb
    obtain ⟨hkr, hblock, ⟨D⟩⟩ := hW
    by_cases hk : k = 0
    · subst k
      exact Or.inl ⟨hblock, D.zero_state_outputs⟩
    · have hk1 : 1 ≤ k := by omega
      rcases D.packing_alternative hR with hpacked | ⟨T, hdef, hcost⟩
      · exact Or.inl ⟨hblock, D.packed_outputs
          (boundary_descriptor_good_at hdGood S (by omega) hk1 hkr) hpacked⟩
      · have hSb : (enlargedBoundary S T).card ≤ b := by
          rw [enlarged_boundary_card]
          have hm := Nat.mul_le_mul_left R (Nat.sub_le k
            (D.dynamic.submatrix (fun i : ↑Tᶜ => i.val) id).rank)
          omega
        have hI := krylov_input_independent _ _ (2 * r)
          (integer_boundary_mod3_krylov_independent (enlargedBoundary S T) (2 * r) ω
            (boundary_krylov_good_at hkGood _ hSb))
        obtain ⟨k', D', hrank⟩ := graph_boundary_descriptor_step D hblock T hI
        have hloss := boundary_state_loss_budget S T hdef hcost hrank
        refine Or.inr ⟨enlargedBoundary S T, k', boundary_subset_enlarged S T,
          hloss.1, hloss.2.le, ?_⟩
        exact ⟨hloss.1.le.trans hkr,
          shared_block_enlarged (adjacency ω) Target S _ (boundary_subset_enlarged S T) hblock,
          ⟨D'⟩⟩
  obtain ⟨S, hS, hcard, hdone⟩ := budgeted_boundary_descent b R W Done hstep
    S₀ k ⟨hkr, hblock, ⟨D₀⟩⟩ hbudget
  exact ⟨S, hS, hcard, hdone.1, hdone.2⟩

end AdaptiveOrthogonalRigidity
