import AdaptiveOrthogonalRigidity.MovementTransport
import AdaptiveOrthogonalRigidity.MovementImage

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- The image of the actual movement after projecting to original U labels. -/
def projectedMovement {n : ℕ} (Q : RealMatrix n) (U : Finset (Fin n)) :
    Submodule ℝ (U → ℝ) :=
  ((Q - 1).submatrix (fun i : U => i.val) id).mulVecLin.range

/-- The span of the original cross-boundary columns. -/
def boundaryInput {n : ℕ} (A : RealMatrix n) (U : Finset (Fin n)) :
    Submodule ℝ (U → ℝ) :=
  (A.submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val)).mulVecLin.range

theorem projected_movement_rank_le {n : ℕ} (Q : RealMatrix n) (U : Finset (Fin n)) :
    Module.finrank ℝ (projectedMovement Q U) ≤ (Q - 1).rank := by
  exact Matrix.rank_submatrix_le _ _ _

theorem projected_movement_mem {n : ℕ} (Q : RealMatrix n) (U : Finset (Fin n))
    (x : Fin n → ℝ) (hx : x ∈ (Q - 1).mulVecLin.range) :
    coordinateRestriction ℝ U x ∈ projectedMovement Q U := by
  obtain ⟨v, rfl⟩ := hx
  exact ⟨v, rfl⟩

/-- The first shared-block transport inclusion, CH ⊆ H + col Y. -/
theorem projected_movement_action {n : ℕ} (A Q : RealMatrix n)
    (hQ : Orthogonal Q) (U : Finset (Fin n))
    (hblock : (conjugate A Q).submatrix (fun i : U => i.val) (fun j : U => j.val) =
      A.submatrix (fun i : U => i.val) (fun j : U => j.val))
    (z : U → ℝ) (hz : z ∈ projectedMovement Q U) :
    (A.submatrix (fun i : U => i.val) (fun j : U => j.val)).mulVec z ∈
      projectedMovement Q U ⊔ boundaryInput A U := by
  obtain ⟨f, ⟨x, hx⟩, hfz⟩ := projected_movement_lifting Q hQ U z hz
  have haf : coordinateRestriction ℝ U (A.mulVec f) ∈ projectedMovement Q U := by
    rw [← hx]
    exact projected_action_column_movement A Q hQ U hblock x
  have hy : (A.submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val)).mulVec
      (coordinateRestriction ℝ Uᶜ f) ∈ boundaryInput A U := ⟨_, rfl⟩
  have h := (projectedMovement Q U ⊔ boundaryInput A U).sub_mem
    (show coordinateRestriction ℝ U (A.mulVec f) ∈ projectedMovement Q U ⊔ boundaryInput A U
      from Submodule.mem_sup_left haf)
    (show _ ∈ projectedMovement Q U ⊔ boundaryInput A U from Submodule.mem_sup_right hy)
  rw [coordinateRestriction_mulVec, hfz, add_sub_cancel_right] at h
  exact h

theorem projected_action_movement {n : ℕ} (A Q : RealMatrix n)
    (hQ : Orthogonal Q) (U : Finset (Fin n))
    (hblock : (conjugate A Q).submatrix (fun i : U => i.val) (fun j : U => j.val) =
      A.submatrix (fun i : U => i.val) (fun j : U => j.val))
    (x : Fin n → ℝ) (hx : x ∈ (Q - 1).mulVecLin.range) :
    coordinateRestriction ℝ U (A.mulVec x) ∈ projectedMovement Q U ⊔ boundaryInput A U := by
  rw [coordinateRestriction_mulVec]
  apply Submodule.add_mem
  · exact projected_movement_action A Q hQ U hblock _ (projected_movement_mem Q U x hx)
  · exact Submodule.mem_sup_right (show _ ∈ boundaryInput A U from ⟨_, rfl⟩)

/-- The displacement expansion in movement and transpose movement. -/
theorem conjugate_displacement_expansion {n : ℕ} (A Q : RealMatrix n) :
    conjugate A Q - A = A * (Q - 1) + (Q - 1).transpose * A +
      (Q - 1).transpose * A * (Q - 1) := by
  simp only [conjugate, Matrix.transpose_sub, Matrix.transpose_one]
  noncomm_ring

/-- The second shared-block transport inclusion: every full displacement
column projects into H + col Y. -/
theorem projected_displacement {n : ℕ} (A Q : RealMatrix n)
    (hQ : Orthogonal Q) (U : Finset (Fin n))
    (hblock : (conjugate A Q).submatrix (fun i : U => i.val) (fun j : U => j.val) =
      A.submatrix (fun i : U => i.val) (fun j : U => j.val)) (x : Fin n → ℝ) :
    coordinateRestriction ℝ U ((conjugate A Q - A).mulVec x) ∈
      projectedMovement Q U ⊔ boundaryInput A U := by
  rw [conjugate_displacement_expansion]
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, map_add]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact projected_action_movement A Q hQ U hblock _ ⟨x, rfl⟩
    · apply Submodule.mem_sup_left
      apply projected_movement_mem
      rw [← movement_range_transpose Q hQ]
      exact ⟨_, rfl⟩
  · apply Submodule.mem_sup_left
    apply projected_movement_mem
    rw [← movement_range_transpose Q hQ]
    exact ⟨_, rfl⟩

/-- Every actual target boundary column is in the transported input space. -/
theorem target_boundary_mem_transport {n : ℕ} (A Q : RealMatrix n)
    (hQ : Orthogonal Q) (U : Finset (Fin n))
    (hblock : (conjugate A Q).submatrix (fun i : U => i.val) (fun j : U => j.val) =
      A.submatrix (fun i : U => i.val) (fun j : U => j.val)) (x : ↑Uᶜ → ℝ) :
    ((conjugate A Q).submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val)).mulVec x ∈
      projectedMovement Q U ⊔ boundaryInput A U := by
  have hd := projected_displacement A Q hQ U hblock (coordinateExtension ℝ Uᶜ x)
  rw [Matrix.sub_mulVec, map_sub, mulVec_coordinateExtension, mulVec_coordinateExtension] at hd
  change ((conjugate A Q).submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val)).mulVec x -
    (A.submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val)).mulVec x ∈
      projectedMovement Q U ⊔ boundaryInput A U at hd
  have hy : (A.submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val)).mulVec x ∈
      projectedMovement Q U ⊔ boundaryInput A U := Submodule.mem_sup_right ⟨x, rfl⟩
  have hh := (projectedMovement Q U ⊔ boundaryInput A U).add_mem hd hy
  simpa only [sub_add_cancel] using hh

end AdaptiveOrthogonalRigidity
