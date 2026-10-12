import AdaptiveOrthogonalRigidity.CompatibleCoverProbability
import AdaptiveOrthogonalRigidity.ProjectedTransport
import AdaptiveOrthogonalRigidity.CanonicalTarget

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

theorem ordinary_difference_compatible {n : ℕ} (A B : RealMatrix n)
    (hA : Ordinary A) (hB : Ordinary B) : CompatibleDisplacement A (B - A) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [Matrix.sub_apply, hB.1 i j, hA.1 i j]
  · intro i
    simp only [Matrix.sub_apply, hB.2.1 i, hA.2.1 i, sub_self]
  · intro i j
    rcases hA.2.2 i j with ha | ha <;> rcases hB.2.2 i j with hb | hb <;>
      simp only [Matrix.sub_apply, ha, hb] <;> norm_num
  · have he : A + (B - A) = B := by abel
    rw [he]
    exact hB

/-- Normalization and the adaptive cover good event produce a true shared
principal block, leaving the sampled input graph and nonisomorphism unchanged. -/
theorem movement_good_cover_boundary {n r : ℕ} {lam : ℝ} {ω : GraphSample n}
    (hlam : 0 ≤ lam) (hgood : ω ∉ compatibleCoverBadEvent n lam)
    (hω : ω ∈ movementEvent n r) :
    ∃ (Q B : RealMatrix n) (S : Finset (Fin n)),
      Orthogonal Q ∧ Ordinary B ∧ B = conjugate (adjacency ω) Q ∧
      ¬ OrdinarilyIsomorphic (adjacency ω) B ∧ (Q - 1).rank ≤ r ∧
      S.card ≤ initialBoundary lam r ∧
      B.submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val) =
        (adjacency ω).submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val) := by
  rw [movementEvent_eq_identityMovementEvent] at hω
  obtain ⟨Q, B, hQ, hB, ht, hnon, hr⟩ := hω
  have hD : B - adjacency ω ≠ 0 := by
    intro hz
    have hb : B = adjacency ω := sub_eq_zero.mp hz
    exact hnon (hb.symm ▸ ordinarilyIsomorphic_refl (adjacency ω))
  have hcomp := ordinary_difference_compatible (adjacency ω) B (adjacency_ordinary ω) hB
  have hdrank : (B - adjacency ω).rank ≤ 2 * r := by
    rw [ht]
    exact displacement_rank_le _ _ hr
  obtain ⟨S, hS, hs⟩ := initial_boundary_of_cover_good hlam hgood _ hD hcomp hdrank
  refine ⟨Q, B, S, hQ, hB, ht, hnon, hr, hS, ?_⟩
  ext i j
  exact sub_eq_zero.mp (hs i.val (Finset.mem_compl.mp i.property) j.val
    (Finset.mem_compl.mp j.property))

/-- The actual projected movement provides the controlled-space hypotheses
for all target boundary columns at once, with the original augmented inputs. -/
theorem projected_augmented_controlled_space {n r : ℕ} (A Q : RealMatrix n)
    (U : Finset (Fin n)) (hQ : Orthogonal Q) (hr : (Q - 1).rank ≤ r)
    (hblock : (conjugate A Q).submatrix (fun i : U => i.val) (fun j : U => j.val) =
      A.submatrix (fun i : U => i.val) (fun j : U => j.val)) :
    let C := A.submatrix (fun i : U => i.val) (fun j : U => j.val)
    let V := augmentedColumnMatrix (A.submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val))
    let Z := (conjugate A Q).submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val)
    ∃ H : Submodule ℝ (U → ℝ), Module.finrank ℝ H ≤ r ∧
      (∀ w ∈ H, C.mulVec w ∈ H ⊔ V.mulVecLin.range) ∧
      Z.mulVecLin.range ≤ H ⊔ V.mulVecLin.range := by
  dsimp only
  have hy : boundaryInput A U ≤ (augmentedColumnMatrix
      (A.submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val))).mulVecLin.range := by
    rw [Matrix.range_mulVecLin]
    exact boundary_input_le_augmented A U
  have hs := sup_le_sup_left hy (projectedMovement Q U)
  refine ⟨projectedMovement Q U, (projected_movement_rank_le Q U).trans hr, ?_, ?_⟩
  · intro w hw
    exact hs (projected_movement_action A Q hQ U hblock w hw)
  · rintro z ⟨v, rfl⟩
    exact hs (target_boundary_mem_transport A Q hQ U hblock v)

end AdaptiveOrthogonalRigidity
