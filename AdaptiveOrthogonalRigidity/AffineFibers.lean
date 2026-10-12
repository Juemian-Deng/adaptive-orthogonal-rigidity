import AdaptiveOrthogonalRigidity.CoordinatePivots
import AdaptiveOrthogonalRigidity.OriginalEdgeCuts
import AdaptiveOrthogonalRigidity.FiniteBounds

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

theorem bitValue_injective {K : Type*} [Zero K] [One K] [NeZero (1 : K)] :
    Function.Injective (bitValue (R := K)) := by
  intro a b h
  cases a <;> cases b
  · rfl
  · simp [bitValue] at h
  · simp [bitValue] at h
  · rfl

theorem linearMap_coordinate_sum {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (L : (ι → K) →ₗ[K] V) (v : ι → K) :
    L v = ∑ i, v i • L (Pi.single i 1) := by
  have hd : (∑ i, v i • Pi.single i (1 : K)) = v := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  calc
    L v = L (∑ i, v i • Pi.single i (1 : K)) := congrArg L hd.symm
    _ = _ := by simp only [map_sum, map_smul]

theorem linearMap_bool_split {K V ι κ ν : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ν]
    (L : (ν → K) →ₗ[K] V) (e : (ι ⊕ κ) ≃ ν) (x : ι → Bool) (r : κ → Bool) :
    L (boolVector (splitAssignmentEquiv e (x, r))) =
      (∑ i, bitValue (R := K) (x i) • L (Pi.single (e (Sum.inl i)) 1)) +
        ∑ j, bitValue (R := K) (r j) • L (Pi.single (e (Sum.inr j)) 1) := by
  rw [linearMap_coordinate_sum, ← e.sum_comp]
  simp [Fintype.sum_sum_type, boolVector, splitAssignmentEquiv]

theorem pivot_fiber_injective {K V ι κ ν : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ν]
    (L : (ν → K) →ₗ[K] V) (e : (ι ⊕ κ) ≃ ν)
    (hli : LinearIndependent K (fun i => L (Pi.single (e (Sum.inl i)) 1)))
    (r : κ → Bool) :
    Function.Injective (fun x : ι → Bool => L (boolVector (splitAssignmentEquiv e (x, r)))) := by
  intro x y h
  dsimp only at h
  rw [linearMap_bool_split, linearMap_bool_split] at h
  have hc : (fun i => bitValue (R := K) (x i)) = fun i => bitValue (R := K) (y i) := by
    apply (linearIndependent_iff_injective_fintypeLinearCombination.mp hli)
    exact add_right_cancel h
  funext i
  exact bitValue_injective (congrFun hc i)

theorem cube_singleton_le {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ℝ} (hα : 0 ≤ α)
    (p : ι → unitInterval) (hp : ∀ i, α ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ 1 - α)
    (x : ι → Bool) : (cubeMeasure p).real {x} ≤ (1 - α) ^ Fintype.card ι := by
  rw [cubeMeasure_real_singleton]
  unfold cubeWeight
  calc
    _ ≤ ∏ _i : ι, (1 - α) := by
      apply Finset.prod_le_prod₀
      · intro i _; exact hα.trans (bitWeight_lower (hp i) (x i))
      · intro i _
        have hi := hp i
        cases x i <;> simp [bitWeight] <;> linarith
    _ = _ := by simp

/-- Rank-many original independent pivot bits are forced in each remaining
coordinate fiber. The linear map and its target range over arbitrary fields. -/
theorem affine_fiber_bound {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : ι → unitInterval) (hp : ∀ i, α ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ 1 - α)
    (L : (ι → K) →ₗ[K] V) (z : V) :
    (cubeMeasure p).real {x | L (boolVector x) = z} ≤
      (1 - α) ^ Module.finrank K L.range := by
  obtain ⟨f, hf⟩ := linearMap_coordinate_pivots L
  let e := injectionSplitEquiv f
  have hli : LinearIndependent K (fun i => L (Pi.single (e (Sum.inl i)) 1)) := by
    simpa only [e, injectionSplitEquiv_inl] using hf
  apply cube_event_le_of_split_bound p e
  intro r
  have hinj := pivot_fiber_injective L e hli r
  by_cases hex : ∃ x, L (boolVector (splitAssignmentEquiv e (x, r))) = z
  · obtain ⟨x, hx⟩ := hex
    have hsub : {y | L (boolVector (splitAssignmentEquiv e (y, r))) = z} ⊆ {x} := by
      intro y hy
      exact hinj (hy.trans hx.symm)
    have hsingle := cube_singleton_le hα
      (fun i => p (e (Sum.inl i))) (fun i => hp (e (Sum.inl i))) x
    simp only [Fintype.card_fin] at hsingle
    exact (measureReal_mono hsub).trans hsingle
  · have hempty : {x | L (boolVector (splitAssignmentEquiv e (x, r))) = z} = ∅ := by
      ext x; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]; exact fun hx => hex ⟨x, hx⟩
    change (cubeMeasure _).real {x | L (boolVector (splitAssignmentEquiv e (x, r))) = z} ≤ _
    rw [hempty, measureReal_empty]
    exact pow_nonneg (sub_nonneg.mpr hα1) _

/-- An affine translate of a subspace has Bernoulli mass at most beta to its
codimension, over any field containing zero and one. -/
theorem affine_subspace_bound {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : ι → unitInterval) (hp : ∀ i, α ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ 1 - α)
    (W : Submodule K (ι → K)) (z : ι → K) :
    (cubeMeasure p).real {x | boolVector x - z ∈ W} ≤
      (1 - α) ^ (Fintype.card ι - Module.finrank K W) := by
  have h := affine_fiber_bound hα hα1 p hp W.mkQ (W.mkQ z)
  have hr : W.mkQ.range = ⊤ := LinearMap.range_eq_top.mpr W.mkQ_surjective
  rw [hr, finrank_top] at h
  have hd := W.finrank_quotient_add_finrank
  simp only [Module.finrank_pi] at hd
  have hdim : Module.finrank K ((ι → K) ⧸ W) = Fintype.card ι - Module.finrank K W := by omega
  rw [hdim] at h
  have hset : {x : ι → Bool | W.mkQ (boolVector x) = W.mkQ z} =
      {x | boolVector x - z ∈ W} := by
    ext x
    exact Submodule.Quotient.eq W
  rw [hset] at h
  exact h

theorem affine_matrix_fiber_bound {K ι κ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : ι → unitInterval) (hp : ∀ i, α ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ 1 - α)
    (M : Matrix κ ι K) (z : κ → K) :
    (cubeMeasure p).real {x | M.mulVec (boolVector x) = z} ≤ (1 - α) ^ M.rank := by
  exact affine_fiber_bound hα hα1 p hp M.mulVecLin z

end AdaptiveOrthogonalRigidity
