import AdaptiveOrthogonalRigidity.AffineCubeColumns

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

namespace AdaptiveOrthogonalRigidity

theorem boundaryCutDisjoint {n : ℕ} (S : Finset (Fin n)) (i : ↥(Sᶜ)) (j : S) : i.val ≠ j.val := by
  intro h
  exact (Finset.mem_compl.mp i.property) (h ▸ j.property)

def boundaryBoolMatrix {n : ℕ} (S : Finset (Fin n)) (ω : GraphSample n) : ↥(Sᶜ) → S → Bool :=
  fun i j => ω (edgeOfDistinct i.val j.val (boundaryCutDisjoint S i j))

def fixedBoundaryCubeFailure {n : ℕ} (S : Finset (Fin n)) : Set (GraphSample n) :=
  {ω | ∃ z : ↥(Sᶜ) → Bool,
    boolVector (R := ZMod 3) z ∈ Set.range (augmentedCubeMatrix (boundaryBoolMatrix S ω)).mulVec ∧
      ¬ CanonicalBoolColumn (boundaryBoolMatrix S ω) z}

def boundaryCubeFailure (n b : ℕ) : Set (GraphSample n) :=
  {ω | ∃ S : Finset (Fin n), S.card ≤ b ∧ ω ∈ fixedBoundaryCubeFailure S}

theorem fixed_boundary_cube_bound {n : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : EdgeParameters n) (hp : Admissible α p) (S : Finset (Fin n)) :
    eventProbability p (fixedBoundaryCubeFailure S) ≤
      (3 : ℝ) ^ (S.card + 1) * (gamma α) ^ (n - S.card) := by
  have h := original_graph_binary_column_bound hα hα1 p hp
    (show ↥(Sᶜ) ↪ Fin n from ⟨Subtype.val, Subtype.val_injective⟩)
    (show S ↪ Fin n from ⟨Subtype.val, Subtype.val_injective⟩) (boundaryCutDisjoint S)
  simp only [Fintype.card_coe, Finset.card_compl, Fintype.card_fin] at h
  exact h

/-- The exact `C_n` term of the finite movement theorem, with a simultaneous
union over all original boundaries of size at most `b`. -/
theorem uniform_affine_cube_bound {n b : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : EdgeParameters n) (hp : Admissible α p) :
    eventProbability p (boundaryCubeFailure n b) ≤ cubeBound α n b := by
  let Q := Finset.range (b + 1)
  let F (q : Q) : Set (GraphSample n) :=
    ⋃ S : (Finset.univ : Finset (Fin n)).powersetCard q.val, fixedBoundaryCubeFailure S.val
  have hsub : boundaryCubeFailure n b ⊆ ⋃ q : Q, F q := by
    rintro ω ⟨S, hS, hω⟩
    have hq : S.card ∈ Q := Finset.mem_range.mpr (by omega)
    exact Set.mem_iUnion.mpr ⟨⟨S.card, hq⟩, Set.mem_iUnion.mpr
      ⟨⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩, hω⟩⟩
  have hF (q : Q) : eventProbability p (F q) ≤
      (n.choose q.val : ℝ) * (3 : ℝ) ^ (q.val + 1) * (gamma α) ^ (n - q.val) := by
    let D := (3 : ℝ) ^ (q.val + 1) * (gamma α) ^ (n - q.val)
    have hS (S : (Finset.univ : Finset (Fin n)).powersetCard q.val) :
        eventProbability p (fixedBoundaryCubeFailure S.val) ≤ D := by
      simpa only [(Finset.mem_powersetCard.mp S.property).2] using fixed_boundary_cube_bound hα hα1 p hp S.val
    calc
      _ ≤ ∑ S : (Finset.univ : Finset (Fin n)).powersetCard q.val,
          eventProbability p (fixedBoundaryCubeFailure S.val) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _S : (Finset.univ : Finset (Fin n)).powersetCard q.val, D :=
        Finset.sum_le_sum (fun S _ => hS S)
      _ = _ := by simp [D, Finset.card_powersetCard, mul_assoc]
  calc
    _ ≤ eventProbability p (⋃ q : Q, F q) := measureReal_mono hsub
    _ ≤ ∑ q : Q, eventProbability p (F q) := measureReal_iUnion_fintype_le F
    _ ≤ ∑ q : Q, (n.choose q.val : ℝ) * (3 : ℝ) ^ (q.val + 1) * (gamma α) ^ (n - q.val) :=
      Finset.sum_le_sum (fun q _ => hF q)
    _ = cubeBound α n b := by
      simp only [cubeBound, Q, Finset.univ_eq_attach]
      exact Finset.sum_attach _ (fun q => (n.choose q : ℝ) * (3 : ℝ) ^ (q + 1) * (gamma α) ^ (n - q))

end AdaptiveOrthogonalRigidity
