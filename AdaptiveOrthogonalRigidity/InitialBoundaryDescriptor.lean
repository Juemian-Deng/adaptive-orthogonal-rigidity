import AdaptiveOrthogonalRigidity.GraphBoundaryDescriptor
import AdaptiveOrthogonalRigidity.IntegerBoundaryControlled
import AdaptiveOrthogonalRigidity.IntegralDescriptorRegular

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- The actual adaptive real witness produces a regular F3 descriptor for all
its target boundary columns. All integrality and rank hypotheses are proved
from the original integer graph data and the original Krylov good event. -/
theorem initial_graph_boundary_descriptor {n r : ℕ} (S : Finset (Fin n))
    (ω : GraphSample n) (Q B : RealMatrix n)
    (hQ : Orthogonal Q) (hB : Ordinary B) (ht : B = conjugate (adjacency ω) Q)
    (hr : (Q - 1).rank ≤ r)
    (hblock : B.submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val) =
      (adjacency ω).submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val))
    (hkGood : ω ∉ fixedBoundaryKrylovFailure S (2 * r)) :
    ∃ k : ℕ, k ≤ r ∧ Nonempty (GraphBoundaryDescriptor S ω B k) := by
  obtain ⟨H, hdim, hC, hZ⟩ := integer_boundary_real_controlled S ω Q B hQ hB ht hr hblock
  have hI := integer_boundary_mod3_krylov_independent S (2 * r) ω hkGood
  obtain ⟨k, X, E, M, F, B₀, L, G, hk, hact, hout, hjoint, _, hreg⟩ :=
    integer_real_regular_descriptor (integerBoundaryBulk S ω) (integerBoundaryInputs S ω)
      (integerBoundaryOutputs S B) r H hdim hI hC hZ
  exact ⟨k, hk, ⟨⟨X, E, M, F, B₀, L, G, hjoint, hreg, hact, hout⟩⟩⟩

end AdaptiveOrthogonalRigidity
