import AdaptiveOrthogonalRigidity.Model
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace AdaptiveOrthogonalRigidity

@[simp] theorem adjacency_diagonal {n : ℕ} (ω : GraphSample n) (i : Fin n) :
    adjacency ω i i = 0 := by
  simp [adjacency]

theorem adjacency_symmetric {n : ℕ} (ω : GraphSample n) (i j : Fin n) :
    adjacency ω i j = adjacency ω j i := by
  rcases lt_trichotomy i j with h | h | h
  · simp [adjacency, h, not_lt_of_gt h]
  · subst j
    rfl
  · simp [adjacency, h, not_lt_of_gt h]

theorem adjacency_binary {n : ℕ} (ω : GraphSample n) (i j : Fin n) :
    adjacency ω i j = 0 ∨ adjacency ω i j = 1 := by
  unfold adjacency bitReal
  split_ifs <;> simp

theorem adjacency_ordinary {n : ℕ} (ω : GraphSample n) :
    Ordinary (adjacency ω) :=
  ⟨adjacency_symmetric ω, adjacency_diagonal ω, adjacency_binary ω⟩

/-- Encode any real matrix's entries equal to one; for ordinary matrices this is an inverse. -/
noncomputable def graphOfOrdinary {n : ℕ} (A : RealMatrix n) : GraphSample n := by
  classical
  exact fun e => decide (A e.val.1 e.val.2 = 1)

theorem adjacency_graphOfOrdinary {n : ℕ} (A : RealMatrix n) (hA : Ordinary A) :
    adjacency (graphOfOrdinary A) = A := by
  classical
  funext i j
  rcases lt_trichotomy i j with h | h | h
  · rcases hA.2.2 i j with h0 | h1
    · simp [adjacency, h, graphOfOrdinary, bitReal, h0]
    · simp [adjacency, h, graphOfOrdinary, bitReal, h1]
  · subst j
    simp [hA.2.1]
  · have hn : ¬ i < j := not_lt_of_gt h
    rcases hA.2.2 j i with h0 | h1
    · have h0' : A i j = 0 := (hA.1 i j).trans h0
      simp [adjacency, h, hn, graphOfOrdinary, bitReal, h0, h0']
    · have h1' : A i j = 1 := (hA.1 i j).trans h1
      simp [adjacency, h, hn, graphOfOrdinary, bitReal, h1, h1']

theorem ordinary_iff_adjacency {n : ℕ} (A : RealMatrix n) :
    Ordinary A ↔ ∃ ω : GraphSample n, adjacency ω = A := by
  constructor
  · intro hA
    exact ⟨graphOfOrdinary A, adjacency_graphOfOrdinary A hA⟩
  · rintro ⟨ω, rfl⟩
    exact adjacency_ordinary ω

instance graphMeasure_isProbability {n : ℕ} (p : EdgeParameters n) :
    IsProbabilityMeasure (graphMeasure p) := by
  unfold graphMeasure
  infer_instance

@[simp] theorem graphMeasure_univ {n : ℕ} (p : EdgeParameters n) :
    graphMeasure p Set.univ = 1 := measure_univ

@[simp] theorem eventProbability_univ {n : ℕ} (p : EdgeParameters n) :
    eventProbability p Set.univ = 1 := by
  simp [eventProbability]

theorem edge_coordinates_independent {n : ℕ} (p : EdgeParameters n) :
    iIndepFun (fun e (ω : GraphSample n) => ω e) (graphMeasure p) := by
  exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

theorem graphMeasure_singleton {n : ℕ} (p : EdgeParameters n) (ω : GraphSample n) :
    graphMeasure p {ω} =
      ∏ e, bernoulliMeasure true false (p e) {ω e} := by
  exact Measure.pi_singleton _ _

theorem coordinate_law {n : ℕ} (p : EdgeParameters n) (e : Edge n) :
    (graphMeasure p).map (fun ω : GraphSample n => ω e) =
      bernoulliMeasure true false (p e) := by
  exact (measurePreserving_eval (fun e => bernoulliMeasure true false (p e)) e).map_eq

theorem edge_probability {n : ℕ} (p : EdgeParameters n) (e : Edge n) :
    eventProbability p {ω | ω e = true} = (p e : ℝ) := by
  calc
    eventProbability p {ω | ω e = true} =
        (graphMeasure p).real ((fun ω : GraphSample n => ω e) ⁻¹' {true}) := rfl
    _ = ((graphMeasure p).map (fun ω : GraphSample n => ω e)).real {true} :=
      (map_measureReal_apply (measurable_pi_apply e) (MeasurableSet.singleton true)).symm
    _ = (p e : ℝ) := by
      rw [coordinate_law]
      exact bernoulliMeasure_real_apply_of_mem_of_notMem (p e)
        (MeasurableSet.singleton true) (by simp) (by simp)

theorem all_graph_events_measurable {n : ℕ} (E : Set (GraphSample n)) :
    MeasurableSet E := (Set.toFinite E).measurableSet

@[simp] theorem permutationMatrix_refl (n : ℕ) :
    permutationMatrix (Equiv.refl (Fin n)) = (1 : RealMatrix n) := by
  ext i j
  by_cases h : i = j <;> simp [permutationMatrix, Matrix.one_apply, h]

theorem ordinarilyIsomorphic_refl {n : ℕ} (A : RealMatrix n) :
    OrdinarilyIsomorphic A A := by
  refine ⟨Equiv.refl _, ?_⟩
  simp [conjugate]

end AdaptiveOrthogonalRigidity
