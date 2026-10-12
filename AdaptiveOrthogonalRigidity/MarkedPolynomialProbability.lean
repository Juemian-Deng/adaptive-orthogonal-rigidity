import AdaptiveOrthogonalRigidity.LastMarkProbability
import AdaptiveOrthogonalRigidity.GraphRelabeling

open MeasureTheory Matrix Polynomial
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Every prescribed nonzero mark is allowed. A coordinate permutation and
normalization are chosen from the mark before exposing any original edge. -/
theorem marked_polynomial_probability_bound (n d t : ℕ) (diag : Fin n → ZMod 3)
    (v : Fin n → ZMod 3) (hv : v ≠ 0)
    {α : ℝ} (hα : 0 ≤ α) (hαhalf : α ≤ 1 / 2)
    (p : EdgeParameters n) (hp : Admissible α p) :
    eventProbability p (markedPolynomialFailure n d diag v) ≤
      (rootCount d : ℝ) * (2 : ℝ) ^ n * (beta α) ^ (((t : ℝ) ^ 2 - 1) / 4) +
        (markPairCount d : ℝ) * (beta α) ^ ((n : ℝ) - 1 - d * t) := by
  cases n with
  | zero => exact False.elim (hv (by funext i; exact Fin.elim0 i))
  | succ n =>
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := Function.ne_iff.mp hv
    let e : Equiv.Perm (Fin (n + 1)) := Equiv.swap (Fin.last n) j
    have he : (v ∘ e) (Fin.last n) ≠ 0 := by simpa [e] using hj
    let E := markedPolynomialFailure (n + 1) d (diag ∘ e) (v ∘ e)
    have hsub : markedPolynomialFailure (n + 1) d diag v ⊆ {ω | relabelGraph e ω ∈ E} := by
      rintro ω ⟨q, hq, hd, hz⟩
      refine ⟨q, hq, hd, ?_⟩
      rw [fieldGraphMatrix_relabel_aeval, hz]
      rfl
    have hlaw : eventProbability p {ω | relabelGraph e ω ∈ E} =
        eventProbability (fun q => p (relabelEdgeEmbedding e q)) E :=
      cube_injective_projection_probability p (relabelEdgeEmbedding e) E
    have hb := last_mark_probability_bound n d t (diag ∘ e) (v ∘ e) he hα hαhalf
      (fun q => p (relabelEdgeEmbedding e q)) (fun q => hp (relabelEdgeEmbedding e q))
    have hβ : 0 ≤ (beta α) ^ (((t : ℝ) ^ 2 - 1) / 4) :=
      Real.rpow_nonneg (by dsimp [beta]; linarith) _
    have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n + 1) := by
      rw [pow_succ]
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) n]
    have hexp : ((n + 1 : ℕ) : ℝ) - 1 - d * t = (n : ℝ) - d * t := by push_cast; ring
    rw [hexp]
    exact ((measureReal_mono hsub).trans_eq hlaw).trans (hb.trans
      (add_le_add (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)) hβ) (le_refl _)))

end AdaptiveOrthogonalRigidity
