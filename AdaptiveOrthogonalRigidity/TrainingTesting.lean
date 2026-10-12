import AdaptiveOrthogonalRigidity.ProjectorTesting

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

theorem cube_event_probability_split {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]
    (p : ν → unitInterval) (e : (ι ⊕ κ) ≃ ν) (E : Set (ν → Bool)) :
    (cubeMeasure p).real E = ∑ r : κ → Bool,
      cubeWeight (fun j => p (e (Sum.inr j))) r *
        (cubeMeasure (fun i => p (e (Sum.inl i)))).real
          {x | splitAssignmentEquiv e (x, r) ∈ E} := by
  rw [cubeMeasure_real_eq_sum]
  rw [← (splitAssignmentEquiv e).sum_comp (fun x => if x ∈ E then cubeWeight p x else 0)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [cubeWeight_splitAssignment]
  apply Finset.sum_congr rfl
  intro r _
  rw [cubeMeasure_real_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Set.mem_ofPred_eq]
  split_ifs <;> ring

/-- A bad-training/good-testing split integrated under the original product law. -/
theorem cube_event_le_bad_plus_good {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]
    (p : ν → unitInterval) (e : (ι ⊕ κ) ≃ ν) (E : Set (ν → Bool))
    (B : Set (κ → Bool)) (C : ℝ) (hC : 0 ≤ C)
    (hgood : ∀ r : κ → Bool, r ∉ B →
      (cubeMeasure (fun i => p (e (Sum.inl i)))).real
        {x | splitAssignmentEquiv e (x, r) ∈ E} ≤ C) :
    (cubeMeasure p).real E ≤ (cubeMeasure (fun j => p (e (Sum.inr j)))).real B + C := by
  rw [cube_event_probability_split p e E]
  let pr := fun j => p (e (Sum.inr j))
  calc
    _ ≤ ∑ r : κ → Bool, cubeWeight pr r * ((if r ∈ B then 1 else 0) + C) := by
      apply Finset.sum_le_sum
      intro r _
      apply mul_le_mul_of_nonneg_left _ (cubeWeight_nonneg pr r)
      by_cases hr : r ∈ B
      · simp only [hr, ↓reduceIte]
        exact measureReal_le_one.trans (by linarith)
      · simpa only [hr, ↓reduceIte, zero_add] using hgood r hr
    _ = (cubeMeasure pr).real B + C := by
      rw [cubeMeasure_real_eq_sum]
      simp_rw [mul_add, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, cubeWeight_sum, one_mul]

theorem cubeMatrix_intCast {ι κ R : Type*} [CommRing R] (X : ι × κ → Bool) :
    (cubeMatrix (R := ℤ) X).map (Int.castRingHom R) = cubeMatrix (R := R) X := by
  ext i j
  cases hx : X (i, j) <;> simp [cubeMatrix, bitValue, hx]

theorem cast_gramSymmetric {ι κ R : Type*} [Fintype κ] [CommRing R]
    (X : ι × κ → Bool) : castSymmetric R (gramSymmetric (R := ℤ) X) = gramSymmetric (R := R) X := by
  apply Subtype.ext
  change (cubeMatrix (R := ℤ) X * (cubeMatrix (R := ℤ) X).transpose).map (Int.castRingHom R) = _
  rw [Matrix.map_mul, Matrix.transpose_map, cubeMatrix_intCast]
  rfl

/-- Training/testing bound for full families of independent nonempty rectangles.
The real vector is existentially chosen after every bit has been sampled. -/
theorem adaptive_rectangle_training_testing {ι σ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    (ρ : σ → Type*) (κ : τ → Type*)
    [∀ s, Fintype (ρ s)] [∀ s, DecidableEq (ρ s)] [∀ s, Nonempty (ρ s)]
    [∀ t, Fintype (κ t)] [∀ t, DecidableEq (κ t)] [∀ t, Nonempty (κ t)]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (b : ℕ)
    (p : ((Σ t, ι × κ t) ⊕ (Σ s, ι × ρ s)) → unitInterval)
    (hp : ∀ e, α ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - α) :
    (cubeMeasure p).real {X | ∃ u : ι → ℝ, (∑ i, u i ^ 2 = 1) ∧ ¬ IsSignedCoordinate u ∧
      (∀ s, ∃ m : ℕ, m ≤ b ∧
        quadraticValue (gramSymmetric (R := ℝ) (fun e => X (Sum.inr ⟨s, e⟩))).val u = m) ∧
      ∀ t, ∃ k : ℤ,
        quadraticValue (gramSymmetric (R := ℝ) (fun e => X (Sum.inl ⟨t, e⟩))).val u = k} ≤
      (3 : ℝ) ^ (Fintype.card ι * (Fintype.card ι + 1) / 2) * (1 - α ^ 2) ^ Fintype.card σ +
        (b + 1 : ℝ) ^ (Fintype.card ι * (Fintype.card ι + 1) / 2) *
          (1 - α ^ 2) ^ Fintype.card τ := by
  let Bad : Set ((Σ s, ι × ρ s) → Bool) := {r |
    Submodule.span (ZMod 3) (Set.range (fun s => gramSymmetric (R := ZMod 3) (fun e => r ⟨s, e⟩))) ≠ ⊤}
  let C := (b + 1 : ℝ) ^ (Fintype.card ι * (Fintype.card ι + 1) / 2) *
    (1 - α ^ 2) ^ Fintype.card τ
  let E : Set (((Σ t, ι × κ t) ⊕ (Σ s, ι × ρ s)) → Bool) :=
    {X | ∃ u : ι → ℝ, (∑ i, u i ^ 2 = 1) ∧ ¬ IsSignedCoordinate u ∧
      (∀ s, ∃ m : ℕ, m ≤ b ∧
        quadraticValue (gramSymmetric (R := ℝ) (fun e => X (Sum.inr ⟨s, e⟩))).val u = m) ∧
      ∀ t, ∃ k : ℤ,
        quadraticValue (gramSymmetric (R := ℝ) (fun e => X (Sum.inl ⟨t, e⟩))).val u = k}
  have hC : 0 ≤ C := mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (by nlinarith) _)
  have hsplit := cube_event_le_bad_plus_good p (Equiv.refl _) E Bad C hC (by
    intro r hr
    have hspan : Submodule.span (ZMod 3) (Set.range (fun s =>
        castSymmetric (ZMod 3) (gramSymmetric (R := ℤ) (fun e => r ⟨s, e⟩)))) = ⊤ := by
      simpa only [Bad, Set.mem_ofPred_eq, not_not, cast_gramSymmetric] using hr
    have hb := integer_training_testing_bound κ hα hα1 (fun e => p (Sum.inl e))
      (fun e => hp (Sum.inl e)) (fun s => gramSymmetric (R := ℤ) (fun e => r ⟨s, e⟩)) hspan b
    simpa only [E, C, splitAssignmentEquiv, Equiv.refl_apply, Equiv.refl_symm, Equiv.coe_fn_mk,
      Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr, cast_gramSymmetric] using hb)
  apply hsplit.trans
  exact add_le_add (training_gram_span_failure ρ hα hα1 (fun e => p (Sum.inr e))
    (fun e => hp (Sum.inr e))) (le_refl C)

end AdaptiveOrthogonalRigidity
