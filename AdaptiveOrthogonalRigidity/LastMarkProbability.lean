import AdaptiveOrthogonalRigidity.MarkedStarProbability
import AdaptiveOrthogonalRigidity.LastGraphCoordinates

open MeasureTheory Matrix Polynomial
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable def markedPolynomialFailure (n d : ℕ) (diag : Fin n → ZMod 3)
    (v : Fin n → ZMod 3) : Set (GraphSample n) :=
  {ω | ∃ q : Polynomial (ZMod 3), q ≠ 0 ∧ q.natDegree ≤ d ∧
    (Polynomial.aeval (fieldGraphMatrix (ZMod 3) n diag ω) q).mulVec v = 0}

/-- The last-coordinate-one specialization, integrated over the genuine old
principal graph and its fresh last star. -/
theorem last_mark_one_probability_bound (n d t : ℕ) (diag : Fin (n + 1) → ZMod 3)
    (v : Fin (n + 1) → ZMod 3) (hv : v (Fin.last n) = 1)
    {α : ℝ} (hα : 0 ≤ α) (hαhalf : α ≤ 1 / 2)
    (p : EdgeParameters (n + 1)) (hp : Admissible α p) :
    eventProbability p (markedPolynomialFailure (n + 1) d diag v) ≤
      (rootCount d : ℝ) * (2 : ℝ) ^ n * (beta α) ^ (((t : ℝ) ^ 2 - 1) / 4) +
        (markPairCount d : ℝ) * (beta α) ^ ((n : ℝ) - d * t) := by
  let diag0 := fun i : Fin n => diag i.castSucc
  let C : ℝ := (markPairCount d : ℝ) * (beta α) ^ ((n : ℝ) - d * t)
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (by dsimp [beta]; linarith) _)
  have hsplit := cube_event_le_bad_plus_good p (edgeSuccEquiv n)
    (markedPolynomialFailure (n + 1) d diag v) (polynomialKernelFailure n d t diag0) C hC (by
      intro r hr
      have hgood (q : Polynomial (ZMod 3)) (hq : q ≠ 0) (hd : q.natDegree ≤ d) :
          Module.finrank (ZMod 3) (Polynomial.aeval (fieldGraphMatrix (ZMod 3) n diag0 r) q).mulVecLin.ker ≤ d * t := by
        by_contra h
        exact hr ⟨q, hq, hd, lt_of_not_ge h⟩
      have hsub : {x | splitAssignmentEquiv (edgeSuccEquiv n) (x, r) ∈ markedPolynomialFailure (n + 1) d diag v} ⊆
          markedStarFailure d (fieldGraphMatrix (ZMod 3) n diag0 r) (fun i => v i.castSucc) (diag (Fin.last n)) := by
        rintro x ⟨q, hq, hd, hz⟩
        refine ⟨q, hq, hd, ?_⟩
        have h := congrArg (lastCoordinates (ZMod 3) n) hz
        rw [lastCoordinates_fieldGraph_aeval, map_zero, lastCoordinates_apply, hv] at h
        simpa only [graphDropLast_split, graphLastStar_split] using h
      have h := marked_star_probability_bound d (d * t) (fieldGraphMatrix (ZMod 3) n diag0 r)
        (fun i => v i.castSucc) (diag (Fin.last n)) hgood hα hαhalf
        (fun i => p ((edgeSuccEquiv n) (Sum.inl i))) (fun i => hp ((edgeSuccEquiv n) (Sum.inl i)))
      exact (measureReal_mono hsub).trans (by simpa only [C, Fintype.card_fin, Nat.cast_mul] using h))
  exact hsplit.trans (add_le_add
    (polynomial_kernel_bound n d t diag0 hα hαhalf (fun e => p ((edgeSuccEquiv n) (Sum.inr e)))
      (fun e => hp ((edgeSuccEquiv n) (Sum.inr e)))) (le_refl C))

/-- Scaling depends only on the prescribed mark, never on the random matrix. -/
theorem last_mark_probability_bound (n d t : ℕ) (diag : Fin (n + 1) → ZMod 3)
    (v : Fin (n + 1) → ZMod 3) (hv : v (Fin.last n) ≠ 0)
    {α : ℝ} (hα : 0 ≤ α) (hαhalf : α ≤ 1 / 2)
    (p : EdgeParameters (n + 1)) (hp : Admissible α p) :
    eventProbability p (markedPolynomialFailure (n + 1) d diag v) ≤
      (rootCount d : ℝ) * (2 : ℝ) ^ n * (beta α) ^ (((t : ℝ) ^ 2 - 1) / 4) +
        (markPairCount d : ℝ) * (beta α) ^ ((n : ℝ) - d * t) := by
  let w : Fin (n + 1) → ZMod 3 := (v (Fin.last n))⁻¹ • v
  have hw : w (Fin.last n) = 1 := by simp [w, hv]
  have hsub : markedPolynomialFailure (n + 1) d diag v ⊆ markedPolynomialFailure (n + 1) d diag w := by
    rintro ω ⟨q, hq, hd, hz⟩
    refine ⟨q, hq, hd, ?_⟩
    simp only [w, Matrix.mulVec_smul, hz, smul_zero]
  exact (measureReal_mono hsub).trans (last_mark_one_probability_bound n d t diag w hw hα hαhalf p hp)

end AdaptiveOrthogonalRigidity
