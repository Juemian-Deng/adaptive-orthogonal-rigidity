import AdaptiveOrthogonalRigidity.InducedGraphCuts
import AdaptiveOrthogonalRigidity.UniformAffineCube

open MeasureTheory Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

noncomputable def boundaryBulkEquiv {n : ℕ} (S : Finset (Fin n)) :
    Fin (n - S.card) ≃ ↥(Sᶜ) := Fintype.equivOfCardEq (by simp)

noncomputable def boundaryBulkEmbedding {n : ℕ} (S : Finset (Fin n)) : Fin (n - S.card) ↪ Fin n :=
  ⟨fun i => (boundaryBulkEquiv S i).val,
    Subtype.val_injective.comp (boundaryBulkEquiv S).injective⟩

def boundarySideEmbedding {n : ℕ} (S : Finset (Fin n)) : S ↪ Fin n :=
  ⟨Subtype.val, Subtype.val_injective⟩

theorem boundaryBulkDisjoint {n : ℕ} (S : Finset (Fin n))
    (i : Fin (n - S.card)) (j : S) : boundaryBulkEmbedding S i ≠ boundarySideEmbedding S j := by
  intro h
  have hin : (boundaryBulkEquiv S i).val ∈ S := by
    change boundaryBulkEmbedding S i ∈ S
    rw [h]
    exact j.property
  exact (Finset.mem_compl.mp (boundaryBulkEquiv S i).property) hin

noncomputable def boundaryKrylovCoordinates {n : ℕ} (S : Finset (Fin n)) :
    ((Fin (n - S.card) × S) ⊕ Edge (n - S.card)) ↪ Edge n :=
  cutBulkEdgeEmbedding (boundaryBulkEmbedding S) (boundarySideEmbedding S) (boundaryBulkDisjoint S)

noncomputable def fixedBoundaryKrylovFailure {n : ℕ} (S : Finset (Fin n)) (d : ℕ) : Set (GraphSample n) :=
  {ω | (fun e => ω (boundaryKrylovCoordinates S e)) ∈
    blockKrylovFailure (n - S.card) d (fun _ => 0) (fun _ => 1)}

noncomputable def boundaryKrylovFailure (n b d : ℕ) : Set (GraphSample n) :=
  {ω | ∃ S : Finset (Fin n), S.card ≤ b ∧ ω ∈ fixedBoundaryKrylovFailure S d}

/-- A prescribed original boundary has nonempty bulk; its constant mark is
therefore nonzero, and all bulk/cut coordinates remain distinct original edges. -/
theorem fixed_boundary_krylov_bound {n : ℕ} (S : Finset (Fin n)) (hS : S.card < n) (d t : ℕ)
    {α : ℝ} (hα : 0 ≤ α) (hαhalf : α ≤ 1 / 2)
    (p : EdgeParameters n) (hp : Admissible α p) :
    eventProbability p (fixedBoundaryKrylovFailure S d) ≤
      ((3 : ℝ) ^ ((d + 1) * (S.card + 1)) + markPairCount d) *
        (beta α) ^ (((n - S.card : ℕ) : ℝ) - 1 - d * t) +
      2 * rootCount d * (2 : ℝ) ^ (n - S.card) * (beta α) ^ (((t : ℝ) ^ 2 - 1) / 4) := by
  have hv : (fun _ : Fin (n - S.card) => (1 : ZMod 3)) ≠ 0 := by
    intro h
    have hx := congrFun h ⟨0, by omega⟩
    exact one_ne_zero hx
  have h := original_graph_krylov_bound (boundaryBulkEmbedding S) (boundarySideEmbedding S)
    (boundaryBulkDisjoint S) d t (fun _ => 0) (fun _ => 1) hv hα hαhalf p hp
  simp only [Fintype.card_coe] at h
  exact h

end AdaptiveOrthogonalRigidity
