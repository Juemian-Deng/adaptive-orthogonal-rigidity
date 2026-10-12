import AdaptiveOrthogonalRigidity.FiniteMovementTheorem
import AdaptiveOrthogonalRigidity.MovementAsymptoticBounds

open Filter Asymptotics

namespace AdaptiveOrthogonalRigidity

/-- A1 (manuscript thm:main). Both error sequences and thresholds are selected
before every heterogeneous admissible edge array; no monotonicity or divergence
hypothesis on the movement-rank sequence is imposed. -/
theorem asymptotic_movement_bound (α : ℝ) (r : ℕ → ℕ)
    (hα : 0 < α) (hhalf : α ≤ 1 / 2) (hr : ∀ n, 1 ≤ r n)
    (hs : IsLittleO atTop (fun n => (r n : ℝ))
      (fun n => Real.sqrt ((n : ℝ) / Real.log n))) :
    (∃ (e : ℕ → ℝ) (N : ℕ), IsLittleO atTop e (fun n => (n : ℝ)) ∧
      ∀ n, N ≤ n → ∀ p : EdgeParameters n, Admissible α p →
        eventProbability p (movementEvent n (r n)) ≤
          (n : ℝ)^4 * Real.exp (-coverRate α * n * Real.log n / (2 * (r n : ℝ)^2)) +
            (gamma α)^n * Real.exp (e n)) ∧
    (∃ (w : ℕ → ℝ) (N : ℕ), Tendsto w atTop atTop ∧
      ∀ n, N ≤ n → ∀ p : EdgeParameters n, Admissible α p →
        eventProbability p (movementEvent n (r n)) ≤
          Real.exp (-w n * (Real.log n)^2)) := by
  obtain ⟨lam, R, t, e, w, N, he, hw, hN⟩ :=
    movement_asymptotic_parameters_and_bounds hα hhalf r hr hs
  have hprob : ∀ n, N ≤ n → ∀ p : EdgeParameters n, Admissible α p →
      eventProbability p (movementEvent n (r n)) ≤
        finiteMovementBound α (lam n) n (r n) (R n) (t n) := by
    intro n hn p hp
    obtain ⟨hn2, hR, ht, hl, hb, hbudget, _, _⟩ := hN n hn
    exact finite_movement_bound α (lam n) n (r n) (R n) (t n)
      hα hhalf hn2 (hr n) hR ht hl hb hbudget p hp
  constructor
  · refine ⟨e, N, he, ?_⟩
    intro n hn p hp
    exact (hprob n hn p hp).trans (hN n hn).2.2.2.2.2.2.1
  · refine ⟨w, N, hw, ?_⟩
    intro n hn p hp
    exact (hprob n hn p hp).trans (hN n hn).2.2.2.2.2.2.2

end AdaptiveOrthogonalRigidity
