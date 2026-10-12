import AdaptiveOrthogonalRigidity.BoundaryDescriptorWitnesses
import AdaptiveOrthogonalRigidity.InitialMovementBoundary

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- The original real witness supplies a controlled space for the actual
integer boundary matrices after their ordinary real cast. -/
theorem integer_boundary_real_controlled {n r : ℕ} (S : Finset (Fin n))
    (ω : GraphSample n) (Q B : RealMatrix n)
    (hQ : Orthogonal Q) (hB : Ordinary B) (ht : B = conjugate (adjacency ω) Q)
    (hr : (Q - 1).rank ≤ r)
    (hblock : B.submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val) =
      (adjacency ω).submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val)) :
    ∃ H : Submodule ℝ (↑Sᶜ → ℝ), Module.finrank ℝ H ≤ r ∧
      (∀ w ∈ H, ((integerBoundaryBulk S ω).map (Int.castRingHom ℝ)).mulVec w ∈
        H ⊔ ((integerBoundaryInputs S ω).map (Int.castRingHom ℝ)).mulVecLin.range) ∧
      ((integerBoundaryOutputs S B).map (Int.castRingHom ℝ)).mulVecLin.range ≤
        H ⊔ ((integerBoundaryInputs S ω).map (Int.castRingHom ℝ)).mulVecLin.range := by
  rw [integerBoundaryBulk_real, integerBoundaryInputs_real, integerBoundaryOutputs_real S B hB]
  rw [ht] at hblock ⊢
  generalize hU : Sᶜ = U at hblock ⊢
  have hS : S = Uᶜ := by rw [← hU, compl_compl]
  subst S
  exact projected_augmented_controlled_space (adjacency ω) Q U hQ hr hblock

/-- A uniform original-boundary good event supplies each individual Krylov
instance without any conditional probability assertion. -/
theorem boundary_krylov_good_at {n b d : ℕ} {ω : GraphSample n}
    (hgood : ω ∉ boundaryKrylovFailure n b d) (S : Finset (Fin n)) (hS : S.card ≤ b) :
    ω ∉ fixedBoundaryKrylovFailure S d := fun h => hgood ⟨S, hS, h⟩

theorem boundary_descriptor_good_at {n b r R k : ℕ} {ω : GraphSample n}
    (hgood : ω ∉ boundaryDescriptorFailure n b r R)
    (S : Finset (Fin n)) (hS : S.card ≤ b) (hk : 1 ≤ k) (hkr : k ≤ r) :
    ω ∉ fixedBoundaryDescriptorFailure S k R :=
  fun h => hgood ⟨S, hS, k, Finset.mem_Icc.mpr ⟨hk, hkr⟩, h⟩

theorem boundary_cube_good_at {n b : ℕ} {ω : GraphSample n}
    (hgood : ω ∉ boundaryCubeFailure n b) (S : Finset (Fin n)) (hS : S.card ≤ b) :
    ω ∉ fixedBoundaryCubeFailure S := fun h => hgood ⟨S, hS, h⟩

end AdaptiveOrthogonalRigidity
