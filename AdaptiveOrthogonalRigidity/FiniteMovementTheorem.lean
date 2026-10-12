import AdaptiveOrthogonalRigidity.InitialBoundaryDescriptor
import AdaptiveOrthogonalRigidity.GlobalBoundaryDescent
import AdaptiveOrthogonalRigidity.MovementExceptionalProbability

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Every adaptive real nonisomorphic movement witness lies in one of the four
original exceptional events. The original target is retained through the entire
boundary descent and the final same-target canonical closure. -/
theorem movementEvent_subset_exceptional {n r R : ℕ} {lam : ℝ}
    (hlam : 0 ≤ lam) (hR : 1 ≤ R) :
    movementEvent n r ⊆ movementExceptionalEvent n r R lam := by
  intro ω hω
  by_contra hbad
  have hc : ω ∉ compatibleCoverBadEvent n lam := fun h => hbad (Or.inl h)
  have hk : ω ∉ boundaryKrylovFailure n (totalBoundary lam r R) (2 * r) :=
    fun h => hbad (Or.inr (Or.inl h))
  have hd : ω ∉ boundaryDescriptorFailure n (totalBoundary lam r R) r R :=
    fun h => hbad (Or.inr (Or.inr (Or.inl h)))
  have ha : ω ∉ boundaryCubeFailure n (totalBoundary lam r R) :=
    fun h => hbad (Or.inr (Or.inr (Or.inr h)))
  obtain ⟨Q, B, S₀, hQ, hB, ht, hnon, hr, hS₀, hblock⟩ :=
    movement_good_cover_boundary hlam hc hω
  have hS₀b : S₀.card ≤ totalBoundary lam r R :=
    hS₀.trans (Nat.le_add_right _ _)
  obtain ⟨k, hkr, ⟨D⟩⟩ := initial_graph_boundary_descriptor S₀ ω Q B hQ hB ht hr hblock
    (boundary_krylov_good_at hk S₀ hS₀b)
  have hbudget : S₀.card + R * k ≤ totalBoundary lam r R :=
    Nat.add_le_add hS₀ (Nat.mul_le_mul_left R hkr)
  obtain ⟨S, _, hS, hblockS, hout⟩ := graph_boundary_descent_terminates S₀ ω B D
    hkr hR hbudget hblock hk hd
  have hSb := hS.trans hbudget
  exact hnon (ordinarily_isomorphic_of_boundary_good S ω Q B hQ hB ht hr hblockS
    (boundary_krylov_good_at hk S hSb) (boundary_cube_good_at ha S hSb)
    (boundary_output_range_implies_cube_span S ω B hout))

/-- F1 (manuscript thm:finite): the complete finite heterogeneous independent
random-graph movement-rank bound, with the original all-real adaptive event. -/
theorem finite_movement_bound (α lam : ℝ) (n r R t : ℕ)
    (hα : 0 < α) (hhalf : α ≤ 1 / 2) (hn : 2 ≤ n) (_hr : 1 ≤ r)
    (hR : 1 ≤ R) (_ht : 2 ≤ t)
    (hlam : max 1 (2 * coverEntropy n / coverRate α) ≤ lam)
    (hb : totalBoundary lam r R ≤ n - 2) (hbudget : R * r ≤ n - totalBoundary lam r R)
    (p : EdgeParameters n) (hp : Admissible α p) :
    eventProbability p (movementEvent n r) ≤ finiteMovementBound α lam n r R t := by
  have hlam0 : 0 ≤ lam := (by norm_num : (0 : ℝ) ≤ 1).trans ((le_max_left _ _).trans hlam)
  exact (measureReal_mono (movementEvent_subset_exceptional hlam0 hR)).trans
    (movement_exceptional_probability hα hhalf hn hR hlam hb hbudget p hp)

end AdaptiveOrthogonalRigidity
