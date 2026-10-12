import AdaptiveOrthogonalRigidity.GraphBoundaryDescriptor
import AdaptiveOrthogonalRigidity.BoundaryEnlargement
import AdaptiveOrthogonalRigidity.BoundaryDescentBudget

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- With no states, all actual target outputs already belong to the original
augmented input space. -/
theorem GraphBoundaryDescriptor.zero_state_outputs {n : ℕ} {S : Finset (Fin n)}
    {ω : GraphSample n} {Target : RealMatrix n} (D : GraphBoundaryDescriptor S ω Target 0) :
    ((integerBoundaryOutputs S Target).map (Int.castRingHom (ZMod 3))).mulVecLin.range ≤
      ((integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3))).mulVecLin.range := by
  have hz : D.X * D.L = 0 := by ext i j; simp [Matrix.mul_apply]
  rw [D.output, hz, zero_add]
  rintro z ⟨v, rfl⟩
  refine ⟨D.G.mulVec v, ?_⟩
  exact Matrix.mulVec_mulVec v _ _

/-- The packing rank defect strictly decreases states and pays for the exact
cardinality of the enlarged original boundary. -/
theorem boundary_state_loss_budget {n k k' R d : ℕ} (S : Finset (Fin n))
    (T : Finset (↑Sᶜ)) (hdef : 1 ≤ k - d) (hcost : T.card < R * (k - d))
    (hstate : k' ≤ d) :
    k' < k ∧ (enlargedBoundary S T).card + R * k' < S.card + R * k := by
  have hd : d ≤ k := by omega
  have hkd : k - d + d = k := Nat.sub_add_cancel hd
  rw [enlarged_boundary_card]
  constructor
  · omega
  · have hm := Nat.mul_le_mul_left R hstate
    nlinarith

end AdaptiveOrthogonalRigidity
