import AdaptiveOrthogonalRigidity.GraphCorankPath

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

theorem markedCorankEvent_new_star_bound {K : Type*} [Field K] (n : ℕ)
    (diag : Fin (n + 1) → K) (a : ℕ) (S : Finset ℕ)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : EdgeParameters (n + 1)) (hp : Admissible α p) (r : GraphSample n) :
    (cubeMeasure (fun i => p (edgeToLast i))).real
      {x | splitAssignmentEquiv (edgeSuccEquiv n) (x, r) ∈ markedCorankEvent K (n + 1) diag a S} ≤
      if n ∈ S then (1 - α) ^ a else 1 := by
  by_cases hnS : n ∈ S
  · rw [ite_eq_left hnS]
    let A := fieldGraphMatrix K n (fun i => diag i.castSucc) r
    by_cases ha : a ≤ fieldGraphCorank K n (fun i => diag i.castSucc) r
    · have hsub : {x | splitAssignmentEquiv (edgeSuccEquiv n) (x, r) ∈ markedCorankEvent K (n + 1) diag a S} ⊆
        {x | Module.finrank K A.mulVecLin.ker ≤
          Module.finrank K (symmetricBorderMap A (boolVector x) (diag (Fin.last n))).ker} := by
        intro x hx
        have hcur := hx.2 hnS
        rw [fieldGraphCorank_succ, graphDropLast_split, graphLastStar_split] at hcur
        exact hcur.2
      have h := symmetric_border_nondecrease_probability A (fieldGraphMatrix_isSymm _ _ _)
        (diag (Fin.last n)) hα hα1 (fun i => p (edgeToLast i)) (fun i => hp (edgeToLast i))
      exact ((measureReal_mono hsub).trans h).trans
        (pow_le_pow_of_le_one (sub_nonneg.mpr hα1) (by linarith) ha)
    · have hempty : {x | splitAssignmentEquiv (edgeSuccEquiv n) (x, r) ∈ markedCorankEvent K (n + 1) diag a S} =
          (∅ : Set (Fin n → Bool)) := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hx
        have hcur := (hx.2 hnS).1
        rw [graphDropLast_split] at hcur
        exact ha hcur
      rw [hempty, measureReal_empty]
      exact pow_nonneg (sub_nonneg.mpr hα1) _
  · rw [ite_eq_right hnS]
    exact measureReal_le_one

theorem markedCorankEvent_probability {K : Type*} [Field K] (n : ℕ)
    (diag : Fin n → K) (a : ℕ) (S : Finset ℕ)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : EdgeParameters n) (hp : Admissible α p) :
    eventProbability p (markedCorankEvent K n diag a S) ≤
      (1 - α) ^ (a * (S ∩ Finset.range n).card) := by
  induction n with
  | zero => simpa [markedCorankEvent, eventProbability] using (measureReal_le_one (μ := graphMeasure p) (s := Set.univ))
  | succ n ih =>
    let pold : EdgeParameters n := fun e => p (edgeCastSucc e)
    let C : ℝ := if n ∈ S then (1 - α) ^ a else 1
    have hC : 0 ≤ C := by dsimp [C]; split_ifs <;> positivity
    have hprod : eventProbability p (markedCorankEvent K (n + 1) diag a S) ≤
        eventProbability pold (markedCorankEvent K n (fun i => diag i.castSucc) a S) * C := by
      apply cube_event_le_conditional_product p (edgeSuccEquiv n)
      · intro x r hx
        have h := hx.1
        rwa [graphDropLast_split] at h
      · intro r _
        exact markedCorankEvent_new_star_bound n diag a S hα hα1 p hp r
    have hold := ih (fun i => diag i.castSucc) pold (fun e => hp (edgeCastSucc e))
    have hcard : (S ∩ Finset.range (n + 1)).card =
        if n ∈ S then (S ∩ Finset.range n).card + 1 else (S ∩ Finset.range n).card := by
      rw [Finset.inter_comm, Finset.range_add_one, Finset.inter_insert]
      by_cases hn : n ∈ S
      · rw [ite_eq_left hn, Finset.card_insert_of_notMem (by simp), ite_eq_left hn, Finset.inter_comm]
      · rw [ite_eq_right hn, ite_eq_right hn, Finset.inter_comm]
    calc
      _ ≤ eventProbability pold (markedCorankEvent K n (fun i => diag i.castSucc) a S) * C := hprod
      _ ≤ (1 - α) ^ (a * (S ∩ Finset.range n).card) * C := mul_le_mul_of_nonneg_right hold hC
      _ = _ := by
        rw [hcard]
        dsimp [C]
        split_ifs <;> simp [Nat.mul_add, pow_add]

end AdaptiveOrthogonalRigidity
