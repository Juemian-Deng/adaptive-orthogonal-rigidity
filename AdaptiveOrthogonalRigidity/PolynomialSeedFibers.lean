import AdaptiveOrthogonalRigidity.AffineFibers
import AdaptiveOrthogonalRigidity.PolynomialKernelProbability

open MeasureTheory Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- A nullity bound gives a real-exponent fiber bound, even when n-h is negative. -/
theorem matrix_fiber_bound_of_nullity_le {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {α : ℝ} (hα : 0 ≤ α) (hαhalf : α ≤ 1 / 2)
    (p : ι → unitInterval) (hp : ∀ i, α ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ 1 - α)
    (M : Matrix ι ι K) (h : ℕ) (hk : Module.finrank K M.mulVecLin.ker ≤ h) (z : ι → K) :
    (cubeMeasure p).real {x | M.mulVec (boolVector x) = z} ≤
      (beta α) ^ ((Fintype.card ι : ℝ) - h) := by
  have hr := M.mulVecLin.finrank_range_add_finrank_ker
  change M.rank + _ = _ at hr
  rw [Module.finrank_pi] at hr
  have hr' : (Fintype.card ι : ℝ) - h ≤ (M.rank : ℝ) := by
    have : Fintype.card ι ≤ M.rank + h := by omega
    exact_mod_cast (show (Fintype.card ι : ℤ) - h ≤ M.rank by omega)
  calc
    _ ≤ (1 - α) ^ M.rank := affine_matrix_fiber_bound hα (by linarith) p hp M z
    _ = (beta α) ^ (M.rank : ℝ) := by rw [Real.rpow_natCast]; rfl
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge (by dsimp [beta]; linarith)
      (by dsimp [beta]; linarith) hr'

/-- Condition only on the other original seed columns; one prescribed nonzero
coefficient polynomial forces an affine fiber of the selected fresh column. -/
theorem matrix_seed_relation_bound {K ι κ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {α : ℝ} (hα : 0 ≤ α) (hαhalf : α ≤ 1 / 2)
    (p : ι × κ → unitInterval) (hp : ∀ ij, α ≤ (p ij : ℝ) ∧ (p ij : ℝ) ≤ 1 - α)
    (M : κ → Matrix ι ι K) (j : κ) (h : ℕ)
    (hk : Module.finrank K (M j).mulVecLin.ker ≤ h) (z : ι → K) :
    (cubeMeasure p).real {X | ∑ k, (M k).mulVec (boolVector (fun i => X (i, k))) = z} ≤
      (beta α) ^ ((Fintype.card ι : ℝ) - h) := by
  apply cube_event_le_of_split_bound p (columnIndexEquiv j)
  intro r
  have heq (x : ι → Bool) :
      (∑ k, (M k).mulVec (boolVector (fun i => splitAssignmentEquiv (columnIndexEquiv j) (x, r) (i, k)))) =
        (M j).mulVec (boolVector x) +
          ∑ k : RemainingCoordinates j, (M k.val).mulVec (boolVector (fun i => r (i, k))) := by
    rw [← (singleIndexEquiv j).sum_comp]
    simp [Fintype.sum_sum_type, singleIndexEquiv,
      splitAssignment_selected_column, splitAssignment_other_column]
  have hb := matrix_fiber_bound_of_nullity_le hα hαhalf (fun i => p (i, j))
    (fun i => hp (i, j)) (M j) h hk
    (z - ∑ k : RemainingCoordinates j, (M k.val).mulVec (boolVector (fun i => r (i, k))))
  change (cubeMeasure (fun i => p (i, j))).real
    {x | (∑ k, (M k).mulVec (boolVector (fun i => splitAssignmentEquiv (columnIndexEquiv j) (x, r) (i, k)))) = z} ≤ _
  simpa only [heq, ← eq_sub_iff_add_eq] using hb

end AdaptiveOrthogonalRigidity
