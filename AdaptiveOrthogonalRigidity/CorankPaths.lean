import AdaptiveOrthogonalRigidity.FiniteBounds
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

open scoped Classical

namespace AdaptiveOrthogonalRigidity

/-- Times whose old corank is at least `a` and whose corank does not decrease. -/
def highNondecreasingTimes (h : ℕ → ℕ) (a N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun i => a ≤ h i ∧ h i ≤ h (i + 1))

/-- A path with increments at most one cannot reach a large value without
paying for enough high nondecreasing steps. -/
theorem corank_path_count (h : ℕ → ℕ) (a N : ℕ) (hzero : h 0 ≤ a)
    (hstep : ∀ i < N, h (i + 1) ≤ h i + 1) :
    h N ≤ a + (highNondecreasingTimes h a N).card := by
  induction N with
  | zero => simpa [highNondecreasingTimes] using hzero
  | succ N ih =>
    have hprev := ih (fun i hi => hstep i (by omega))
    have hinc := hstep N (by omega)
    have hset : highNondecreasingTimes h a (N + 1) =
        if a ≤ h N ∧ h N ≤ h (N + 1) then insert N (highNondecreasingTimes h a N)
        else highNondecreasingTimes h a N := by
      simp [highNondecreasingTimes, Finset.range_add_one, Finset.filter_insert]
    have hnot : N ∉ highNondecreasingTimes h a N := by simp [highNondecreasingTimes]
    rw [hset]
    split_ifs with hh
    · rw [Finset.card_insert_of_notMem hnot]
      omega
    · push Not at hh
      by_cases hNa : a ≤ h N
      · have hdec := hh hNa
        omega
      · omega

/-- A deterministic finite set of `t - floor(t/2)` high nondecreasing times
exists whenever the terminal corank is at least `t`. -/
theorem corank_path_selected_steps (h : ℕ → ℕ) (N t : ℕ) (hzero : h 0 = 0)
    (hstep : ∀ i < N, h (i + 1) ≤ h i + 1) (hend : t ≤ h N) :
    ∃ S : Finset ℕ, S ⊆ Finset.range N ∧ S.card = t - t / 2 ∧
      ∀ i ∈ S, t / 2 ≤ h i ∧ h i ≤ h (i + 1) := by
  have hcount := corank_path_count h (t / 2) N (by omega) hstep
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq
    (show t - t / 2 ≤ (highNondecreasingTimes h (t / 2) N).card by omega)
  refine ⟨S, hS.trans (Finset.filter_subset _ _), hcard, ?_⟩
  intro i hi
  exact (Finset.mem_filter.mp (hS hi)).2

theorem corank_half_product_bound (t : ℕ) :
    ((t : ℝ) ^ 2 - 1) / 4 ≤ ((t / 2) * (t - t / 2) : ℕ) := by
  have he : t = 2 * (t / 2) + t % 2 := by omega
  have hr : t % 2 = 0 ∨ t % 2 = 1 := by omega
  have hdiv : (t - t / 2 : ℕ) = t / 2 + t % 2 := by omega
  rw [hdiv, Nat.cast_mul, Nat.cast_add]
  have het : (t : ℝ) = 2 * (t / 2 : ℕ) + (t % 2 : ℕ) := by exact_mod_cast he
  rcases hr with hr | hr <;> rw [hr] at het ⊢ <;> push_cast at het ⊢ <;> nlinarith

end AdaptiveOrthogonalRigidity
