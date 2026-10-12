import AdaptiveOrthogonalRigidity.FourPoint
import AdaptiveOrthogonalRigidity.ModelLemmas

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- On a finite discrete space, the event mass is the actual sum of its singleton masses. -/
theorem finite_measure_real_sum {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (E : Set Ω) :
    μ.real E = ∑ x, if x ∈ E then μ.real {x} else 0 := by
  let s := Finset.univ.filter (fun x => x ∈ E)
  have hs : (s : Set Ω) = E := by ext x; simp [s]
  rw [← hs, ← sum_measureReal_singleton]
  simp [s, Finset.sum_filter]

theorem bernoulli_real_singleton (p : unitInterval) (b : Bool) :
    (bernoulliMeasure true false p).real {b} = bitWeight (p : ℝ) b := by
  cases b
  · exact bernoulliMeasure_real_apply_of_notMem_of_mem p
      (MeasurableSet.singleton false) (by simp) (by simp)
  · exact bernoulliMeasure_real_apply_of_mem_of_notMem p
      (MeasurableSet.singleton true) (by simp) (by simp)

noncomputable def cubeMeasure {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → unitInterval) :
    Measure (ι → Bool) := Measure.pi (fun i => bernoulliMeasure true false (p i))

instance cubeMeasure_isProbability {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → unitInterval) :
    IsProbabilityMeasure (cubeMeasure p) := by unfold cubeMeasure; infer_instance

def cubeWeight {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → unitInterval) (x : ι → Bool) : ℝ :=
  ∏ i, bitWeight (p i : ℝ) (x i)

theorem cubeMeasure_real_singleton {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → unitInterval) (x : ι → Bool) :
    (cubeMeasure p).real {x} = cubeWeight p x := by
  rw [measureReal_def, cubeMeasure, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact bernoulli_real_singleton (p i) (x i)

theorem cubeMeasure_real_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → unitInterval) (E : Set (ι → Bool)) :
    (cubeMeasure p).real E = ∑ x, if x ∈ E then cubeWeight p x else 0 := by
  rw [finite_measure_real_sum]
  simp only [cubeMeasure_real_singleton]

theorem cubeWeight_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → unitInterval) :
    ∑ x, cubeWeight p x = 1 := by
  have h := cubeMeasure_real_eq_sum p Set.univ
  simpa using h.symm

theorem cubeWeight_pos {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ℝ}
    (hα : 0 < α) (p : ι → unitInterval)
    (hp : ∀ i, α ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ 1 - α) (x : ι → Bool) :
    0 < cubeWeight p x := by
  apply Finset.prod_pos
  intro i _
  exact hα.trans_le (bitWeight_lower (hp i) (x i))

/-- This is an identity for the original graph law, not an alternative substitute distribution. -/
theorem eventProbability_eq_sum {n : ℕ} (p : EdgeParameters n) (E : Set (GraphSample n)) :
    eventProbability p E = ∑ ω, if ω ∈ E then cubeWeight p ω else 0 := by
  exact cubeMeasure_real_eq_sum p E

/-- Every labelled graph has strictly positive mass under the manuscript's alpha hypothesis. -/
theorem graph_singleton_positive {n : ℕ} {α : ℝ} (hα : 0 < α)
    (p : EdgeParameters n) (hp : Admissible α p) (ω : GraphSample n) :
    0 < eventProbability p {ω} := by
  change 0 < (cubeMeasure p).real {ω}
  rw [cubeMeasure_real_singleton]
  exact cubeWeight_pos hα p hp ω

end AdaptiveOrthogonalRigidity
