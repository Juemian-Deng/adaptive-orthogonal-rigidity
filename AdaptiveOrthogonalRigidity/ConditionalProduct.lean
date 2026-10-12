import AdaptiveOrthogonalRigidity.TrainingTesting

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- A conditional bound on new original coordinates multiplies the probability
of an event on old coordinates. No independence of the adaptive event is assumed. -/
theorem cube_event_le_conditional_product {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]
    (p : ν → unitInterval) (e : (ι ⊕ κ) ≃ ν) (E : Set (ν → Bool))
    (F : Set (κ → Bool)) (C : ℝ)
    (hpast : ∀ x r, splitAssignmentEquiv e (x, r) ∈ E → r ∈ F)
    (hbound : ∀ r ∈ F,
      (cubeMeasure (fun i => p (e (Sum.inl i)))).real
        {x | splitAssignmentEquiv e (x, r) ∈ E} ≤ C) :
    (cubeMeasure p).real E ≤ (cubeMeasure (fun j => p (e (Sum.inr j)))).real F * C := by
  rw [cube_event_probability_split p e E, cubeMeasure_real_eq_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro r _
  by_cases hr : r ∈ F
  · rw [ite_eq_left hr]
    exact mul_le_mul_of_nonneg_left (hbound r hr) (cubeWeight_nonneg _ r)
  · have hempty : {x | splitAssignmentEquiv e (x, r) ∈ E} = (∅ : Set (ι → Bool)) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hr (hpast x r hx)
    rw [hempty, measureReal_empty, ite_eq_right hr, mul_zero, zero_mul]

end AdaptiveOrthogonalRigidity
