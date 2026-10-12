import AdaptiveOrthogonalRigidity.KrylovColumns
import AdaptiveOrthogonalRigidity.GraphSeedPolynomials
import AdaptiveOrthogonalRigidity.MarkedPolynomialProbability

open MeasureTheory Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable def blockKrylovFailure {κ : Type*} [Fintype κ]
    (n d : ℕ) (diag : Fin n → ZMod 3) (v : Fin n → ZMod 3) :
    Set (((Fin n × κ) ⊕ Edge n) → Bool) :=
  {X | ¬ LinearIndependent (ZMod 3) (krylovColumns d
    (fieldGraphMatrix (ZMod 3) n diag (fun e => X (Sum.inr e)))
    (fun j : Option κ => j.elim v (fun k => boolVector (fun i => X (Sum.inl (i, k))))))}

/-- Complete finite block-Krylov estimate for an arbitrary prescribed nonzero
mark, the actual columns [v,Y,Cv,CY,...,C^d v,C^d Y], and the original
heterogeneous independent bulk/seed coordinates. -/
theorem block_krylov_probability_bound {κ : Type*} [Fintype κ] [DecidableEq κ]
    (n d t : ℕ) (diag : Fin n → ZMod 3) (v : Fin n → ZMod 3) (hv : v ≠ 0)
    {α : ℝ} (hα : 0 ≤ α) (hαhalf : α ≤ 1 / 2)
    (p : ((Fin n × κ) ⊕ Edge n) → unitInterval)
    (hp : ∀ e, α ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - α) :
    (cubeMeasure p).real (blockKrylovFailure n d diag v) ≤
      ((3 : ℝ) ^ ((d + 1) * (Fintype.card κ + 1)) + markPairCount d) *
        (beta α) ^ ((n : ℝ) - 1 - d * t) +
      2 * rootCount d * (2 : ℝ) ^ n * (beta α) ^ (((t : ℝ) ^ 2 - 1) / 4) := by
  let S : Set (((Fin n × κ) ⊕ Edge n) → Bool) :=
    {X | (fun ij => X (Sum.inl ij)) ∈ seedPolynomialFailure d
      (fieldGraphMatrix (ZMod 3) n diag (fun e => X (Sum.inr e))) v}
  let F : Set (((Fin n × κ) ⊕ Edge n) → Bool) :=
    {X | (fun e => X (Sum.inr e)) ∈ markedPolynomialFailure n d diag v}
  have hsub : blockKrylovFailure n d diag v ⊆ S ∪ F := by
    intro X hX
    exact marked_krylov_failure_split d _ v (fun ij => X (Sum.inl ij)) hX
  have hF : (cubeMeasure p).real F =
      eventProbability (fun e => p (Sum.inr e)) (markedPolynomialFailure n d diag v) :=
    cube_injective_projection_probability p
      (show Edge n ↪ ((Fin n × κ) ⊕ Edge n) from ⟨Sum.inr, Sum.inr_injective⟩)
      (markedPolynomialFailure n d diag v)
  let R : ℝ := (rootCount d : ℝ) * (2 : ℝ) ^ n * (beta α) ^ (((t : ℝ) ^ 2 - 1) / 4)
  let A : ℝ := (3 : ℝ) ^ ((d + 1) * (Fintype.card κ + 1))
  let B : ℝ := (beta α) ^ ((n : ℝ) - 1 - d * t)
  have hpow : (beta α) ^ ((n : ℝ) - d * t) ≤ B :=
    Real.rpow_le_rpow_of_exponent_ge (by dsimp [beta]; linarith)
      (by dsimp [beta]; linarith) (by linarith)
  have hS := graph_seed_polynomial_bound n d t diag v hα hαhalf p hp
  have hM := marked_polynomial_probability_bound n d t diag v hv hα hαhalf
    (fun e => p (Sum.inr e)) (fun e => hp (Sum.inr e))
  calc
    _ ≤ (cubeMeasure p).real (S ∪ F) := measureReal_mono hsub
    _ ≤ (cubeMeasure p).real S + (cubeMeasure p).real F := measureReal_union_le _ _
    _ ≤ (R + A * (beta α) ^ ((n : ℝ) - d * t)) + (R + (markPairCount d : ℝ) * B) :=
      add_le_add hS (hF.le.trans hM)
    _ ≤ (R + A * B) + (R + (markPairCount d : ℝ) * B) :=
      add_le_add (add_le_add (le_refl R) (mul_le_mul_of_nonneg_left hpow (pow_nonneg (by norm_num) _))) (le_refl _)
    _ = _ := by dsimp [R, A, B]; ring

end AdaptiveOrthogonalRigidity
