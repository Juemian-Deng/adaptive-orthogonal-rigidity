import AdaptiveOrthogonalRigidity.ProductFibers
import AdaptiveOrthogonalRigidity.F3QuadraticAtom
import AdaptiveOrthogonalRigidity.RealQuadraticAtom

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

def cubeMatrix {ι κ R : Type*} [Zero R] [One R] (X : ι × κ → Bool) : Matrix ι κ R :=
  fun i j => bitValue (X (i, j))

theorem trace_gram_eq_sum_quadratic {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [CommRing R] (H : Matrix ι ι R) (M : Matrix ι κ R) :
    (H * (M * M.transpose)).trace = ∑ k, quadraticValue H (fun i => M i k) := by
  rw [Matrix.trace_mul_cycle']
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro k _
  simp [Matrix.mul_apply, quadraticValue, dotProduct, Matrix.mulVec, Matrix.transpose_apply,
    Finset.mul_sum]

theorem quadratic_gram_eq_sum_squares {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → ℝ) (M : Matrix ι κ ℝ) :
    quadraticValue (M * M.transpose) u = ∑ k, (u ⬝ᵥ (fun i => M i k)) ^ 2 := by
  unfold quadraticValue
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  simp [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    mul_comm, pow_two]

/-- Full nonempty Bernoulli-rectangle F3 Gram atom bound. -/
theorem f3_gram_atom {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Nonempty κ]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : ι × κ → unitInterval)
    (hp : ∀ e, α ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - α)
    (H : Matrix ι ι (ZMod 3)) (hsym : H.IsSymm) (hne : H ≠ 0) (z : ZMod 3) :
    (cubeMeasure p).real {X |
      (H * (cubeMatrix X * (cubeMatrix X).transpose)).trace = z} ≤ 1 - α ^ 2 := by
  obtain ⟨j⟩ := ‹Nonempty κ›
  have h := cube_column_sum_atom_le p j (cubeQuadratic H) (1 - α ^ 2)
    (fun w => f3_quadratic_atom hα hα1 (fun i => p (i, j)) (fun i => hp (i, j)) H hsym hne w) z
  simp only [trace_gram_eq_sum_quadratic]
  exact h

theorem modOneEq_add_iff (x c z : ℝ) : ModOneEq (x + c) z ↔ ModOneEq x (z - c) := by
  unfold ModOneEq
  have h : x + c - z = x - (z - c) := by ring
  rw [h]

/-- Convolution bound for arbitrary real residues under the original rectangle law. -/
theorem real_column_sum_mod_one_atom {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (p : ι × κ → unitInterval) (j : κ) (f : (ι → Bool) → ℝ) (C : ℝ)
    (hbound : ∀ z, (cubeMeasure (fun i => p (i, j))).real {x | ModOneEq (f x) z} ≤ C)
    (z : ℝ) :
    (cubeMeasure p).real {X | ModOneEq (∑ k, f (fun i => X (i, k))) z} ≤ C := by
  apply cube_event_le_of_split_bound p (columnIndexEquiv j) _ C
  intro r
  change (cubeMeasure (fun i => p (i, j))).real
    {x | ModOneEq (∑ k, f (fun i => splitAssignmentEquiv (columnIndexEquiv j) (x, r) (i, k))) z} ≤ C
  simpa only [split_column_sum, modOneEq_add_iff] using
    hbound (z - ∑ k : RemainingCoordinates j, f (fun i => r (i, k)))

/-- Full nonempty Bernoulli-rectangle real Gram atom bound modulo one. -/
theorem real_gram_mod_one_atom {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    {α : ℝ} (hα : 0 ≤ α) (p : ι × κ → unitInterval)
    (hp : ∀ e, α ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - α)
    (u : ι → ℝ) (hnorm : ∑ i, u i ^ 2 = 1) (hnon : ¬ IsSignedCoordinate u) (z : ℝ) :
    (cubeMeasure p).real {X |
      ModOneEq (quadraticValue (cubeMatrix X * (cubeMatrix X).transpose) u) z} ≤ 1 - α ^ 2 := by
  obtain ⟨j⟩ := ‹Nonempty κ›
  have h := real_column_sum_mod_one_atom p j (squaredProjection u) (1 - α ^ 2)
    (fun w => real_unit_quadratic_atom hα (fun i => p (i, j)) (fun i => hp (i, j)) u hnorm hnon w) z
  simp only [quadratic_gram_eq_sum_squares]
  exact h

theorem real_gram_integer_atom {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    {α : ℝ} (hα : 0 ≤ α) (p : ι × κ → unitInterval)
    (hp : ∀ e, α ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - α)
    (u : ι → ℝ) (hnorm : ∑ i, u i ^ 2 = 1) (hnon : ¬ IsSignedCoordinate u) :
    (cubeMeasure p).real {X |
      ∃ k : ℤ, quadraticValue (cubeMatrix X * (cubeMatrix X).transpose) u = k} ≤ 1 - α ^ 2 := by
  simpa only [ModOneEq, sub_zero] using real_gram_mod_one_atom hα p hp u hnorm hnon 0

end AdaptiveOrthogonalRigidity
