import AdaptiveOrthogonalRigidity.SufficientBlockRange
import AdaptiveOrthogonalRigidity.AsymptoticMovementTheorem
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Exact manuscript endpoint contracts

Each declaration below is an actual proof of the fully quantified target type.
Both movement endpoints first compiled at checkpoint 033; their independent
semantic and axiom audit is tracked separately from successful local compilation.
-/

open Filter Asymptotics
open AdaptiveOrthogonalRigidity

namespace AdaptiveOrthogonalRigidity.TargetContracts

-- F1: manuscript thm:finite, full finite movement-rank bound.
theorem finite_movement : ∀ (α lam : ℝ) (n r R t : ℕ),
  0 < α → α ≤ 1 / 2 → 2 ≤ n → 1 ≤ r → 1 ≤ R → 2 ≤ t →
  max 1 (2 * coverEntropy n / coverRate α) ≤ lam →
  totalBoundary lam r R ≤ n - 2 → R * r ≤ n - totalBoundary lam r R →
  ∀ p : EdgeParameters n, Admissible α p →
    eventProbability p (movementEvent n r) ≤ finiteMovementBound α lam n r R t := by
  exact @finite_movement_bound

-- F2: proved by AdaptiveOrthogonalRigidity.finite_block_bound.
-- Manuscript thm:block-finite, including the geometric corollary.
theorem finite_block : ∀ (α : ℝ) (n b : ℕ),
  0 < α → α ≤ 1 / 2 → 2 ≤ b → 2 * b ≤ n →
  ∀ p : EdgeParameters n, Admissible α p →
    eventProbability p (blockEvent n b) ≤ finiteBlockSum α n b ∧
    (blockY α n b < 1 →
      eventProbability p (blockEvent n b) ≤ blockY α n b / (1 - blockY α n b)) := by
  exact @finite_block_bound

-- A1: manuscript thm:main. Both error sequences are selected before all edge arrays.
theorem asymptotic_movement : ∀ (α : ℝ) (r : ℕ → ℕ),
  0 < α → α ≤ 1 / 2 → (∀ n, 1 ≤ r n) →
  IsLittleO atTop (fun n => (r n : ℝ))
    (fun n => Real.sqrt ((n : ℝ) / Real.log n)) →
  (∃ (e : ℕ → ℝ) (N : ℕ),
    IsLittleO atTop e (fun n => (n : ℝ)) ∧
    ∀ n, N ≤ n → ∀ p : EdgeParameters n, Admissible α p →
      eventProbability p (movementEvent n (r n)) ≤
        (n : ℝ) ^ 4 * Real.exp
          (-coverRate α * n * Real.log n / (2 * (r n : ℝ) ^ 2)) +
        (gamma α) ^ n * Real.exp (e n)) ∧
  (∃ (w : ℕ → ℝ) (N : ℕ), Tendsto w atTop atTop ∧
    ∀ n, N ≤ n → ∀ p : EdgeParameters n, Admissible α p →
      eventProbability p (movementEvent n (r n)) ≤
        Real.exp (-w n * (Real.log n) ^ 2)) := by
  exact @asymptotic_movement_bound

-- A2: proved by asymptotic_block_bound; manuscript thm:blocks.
-- No assumption b_n tends to infinity is introduced.
theorem asymptotic_block : ∀ (α : ℝ) (b : ℕ → ℕ),
  0 < α → α ≤ 1 / 2 → (∀ n, 2 ≤ b n) →
  IsLittleO atTop
    (fun n => (b n : ℝ) ^ 3 * Real.log ((b n : ℝ) + 1) +
      (b n : ℝ) ^ 2 * Real.log n) (fun n => (n : ℝ)) →
  ∃ (e : ℕ → ℝ) (N : ℕ), Tendsto e atTop (nhds 0) ∧
    ∀ n, N ≤ n → ∀ p : EdgeParameters n, Admissible α p →
      eventProbability p (blockEvent n (b n)) ≤
        Real.exp (-((-Real.log (gamma α)) / 12 - e n) * n / (b n : ℝ)) := by
  exact @asymptotic_block_bound

-- Proved by sufficient_block_range, including bounded or oscillating sequences.
theorem sufficient_block : ∀ b : ℕ → ℕ, (∀ n, 2 ≤ b n) →
  IsLittleO atTop (fun n => (b n : ℝ))
    (fun n => ((n : ℝ) / Real.log n) ^ (1 / 3 : ℝ)) →
  IsLittleO atTop
    (fun n => (b n : ℝ) ^ 3 * Real.log ((b n : ℝ) + 1) +
      (b n : ℝ) ^ 2 * Real.log n) (fun n => (n : ℝ)) := by
  exact @sufficient_block_range

end AdaptiveOrthogonalRigidity.TargetContracts
