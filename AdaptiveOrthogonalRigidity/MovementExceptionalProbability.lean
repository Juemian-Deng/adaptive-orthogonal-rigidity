import AdaptiveOrthogonalRigidity.CompatibleCoverProbability
import AdaptiveOrthogonalRigidity.UniformKrylov
import AdaptiveOrthogonalRigidity.UniformDescriptors

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- A union of four genuine events on the original graph sample space. -/
noncomputable def movementExceptionalEvent (n r R : ℕ) (lam : ℝ) : Set (GraphSample n) :=
  compatibleCoverBadEvent n lam ∪
    (boundaryKrylovFailure n (totalBoundary lam r R) (2 * r) ∪
      (boundaryDescriptorFailure n (totalBoundary lam r R) r R ∪
        boundaryCubeFailure n (totalBoundary lam r R)))

/-- The exact four-term numerical estimate for the simultaneous original
exceptional event; deterministic event containment is a separate theorem. -/
theorem movement_exceptional_probability {n r R t : ℕ} {α lam : ℝ}
    (hα : 0 < α) (hhalf : α ≤ 1 / 2) (hn : 2 ≤ n) (hR : 1 ≤ R)
    (hlam : max 1 (2 * coverEntropy n / coverRate α) ≤ lam)
    (hb : totalBoundary lam r R ≤ n - 2) (hbudget : R * r ≤ n - totalBoundary lam r R)
    (p : EdgeParameters n) (hp : Admissible α p) :
    eventProbability p (movementExceptionalEvent n r R lam) ≤ finiteMovementBound α lam n r R t := by
  let b := totalBoundary lam r R
  have hbn : b < n := by dsimp [b]; omega
  have h1 := compatible_displacement_cover_probability hn hα hhalf hlam p hp
  have h2 := uniform_movement_krylov_bound hbn r t hα.le hhalf p hp
  have h3 := uniform_descriptor_bound hα hhalf hR hbudget p hp
  have h4 := uniform_affine_cube_bound hα.le (by linarith : α ≤ 1) p hp (b := b)
  have hu : eventProbability p (movementExceptionalEvent n r R lam) ≤
      eventProbability p (compatibleCoverBadEvent n lam) +
        (eventProbability p (boundaryKrylovFailure n b (2 * r)) +
          (eventProbability p (boundaryDescriptorFailure n b r R) +
            eventProbability p (boundaryCubeFailure n b))) := by
    exact (measureReal_union_le _ _).trans
      (add_le_add le_rfl ((measureReal_union_le _ _).trans
        (add_le_add le_rfl (measureReal_union_le _ _))))
  apply hu.trans
  have hh := add_le_add h1 (add_le_add h2 (add_le_add h3 h4))
  simpa only [finiteMovementBound, b, add_assoc] using hh

end AdaptiveOrthogonalRigidity
