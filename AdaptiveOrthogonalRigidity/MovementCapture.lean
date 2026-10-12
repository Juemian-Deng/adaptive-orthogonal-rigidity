import AdaptiveOrthogonalRigidity.SymmetricInvariantEigenvector
import AdaptiveOrthogonalRigidity.CommutatorCapture
import AdaptiveOrthogonalRigidity.DotSubspaces

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Span of D, AD, ..., A^(a-1)D with all original output vectors. -/
def displacementOrbitSpan {n : ℕ} (A D : RealMatrix n) (a : ℕ) :
    Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ {w | ∃ j < a, ∃ x, (A.mulVecLin ^ j) (D.mulVec x) = w}

theorem symmetric_power_dot {n : ℕ} (A : RealMatrix n) (hA : A.IsSymm)
    (j : ℕ) (x y : Fin n → ℝ) :
    x ⬝ᵥ (A.mulVecLin ^ j) y = y ⬝ᵥ (A.mulVecLin ^ j) x := by
  have hpow : (A ^ j).mulVecLin = A.mulVecLin ^ j := Matrix.toLin'_pow A j
  rw [← hpow]
  change x ⬝ᵥ (A ^ j).mulVec y = y ⬝ᵥ (A ^ j).mulVec x
  simpa only [(hA.pow j).eq] using (dotProduct_transpose_mulVec (A ^ j) x y)

theorem displacement_annihilator_kernels {n : ℕ} (A D : RealMatrix n)
    (hA : A.IsSymm) (hD : D.IsSymm) (a : ℕ) (x : Fin n → ℝ)
    (hx : ∀ w ∈ displacementOrbitSpan A D a, x ⬝ᵥ w = 0) :
    ∀ j < a, D.mulVec ((A.mulVecLin ^ j) x) = 0 := by
  intro j hj
  let y := D.mulVec ((A.mulVecLin ^ j) x)
  have hy : (A.mulVecLin ^ j) (D.mulVec y) ∈ displacementOrbitSpan A D a :=
    Submodule.subset_span ⟨j, hj, y, rfl⟩
  have hzero := hx _ hy
  have heq : x ⬝ᵥ (A.mulVecLin ^ j) (D.mulVec y) = y ⬝ᵥ y := by
    calc
      _ = D.mulVec y ⬝ᵥ (A.mulVecLin ^ j) x := symmetric_power_dot A hA j x (D.mulVec y)
      _ = (A.mulVecLin ^ j) x ⬝ᵥ D.mulVec y := dotProduct_comm _ _
      _ = y ⬝ᵥ D.mulVec ((A.mulVecLin ^ j) x) := by
        simpa only [hD.eq] using (dotProduct_transpose_mulVec D ((A.mulVecLin ^ j) x) y)
      _ = y ⬝ᵥ y := rfl
  exact dotProduct_self_eq_zero.mp (heq.symm.trans hzero)

theorem movement_commutator {n : ℕ} (A Q : RealMatrix n) (hQ : Orthogonal Q)
    (x : Fin n → ℝ) :
    A.mulVec ((Q - 1).mulVec x) = (Q - 1).mulVec (A.mulVec x) +
      Q.mulVec ((conjugate A Q - A).mulVec x) := by
  have hc : Q * conjugate A Q = A * Q := by
    unfold conjugate
    simp only [← Matrix.mul_assoc, hQ.2, Matrix.one_mul]
  have hm : A * (Q - 1) = (Q - 1) * A + Q * (conjugate A Q - A) := by
    rw [mul_sub, mul_sub, sub_mul, Matrix.mul_one, Matrix.one_mul, hc]
    abel
  simpa only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec] using congrArg (fun M => M.mulVec x) hm

/-- A witness without invariant movement is captured by the first a actual
symmetric displacement iterates, a = rank(Q-I). -/
theorem invariant_free_movement_capture {n : ℕ} (A Q : RealMatrix n)
    (hA : A.IsSymm) (hQ : Orthogonal Q)
    (hno : ∀ W : Submodule ℝ (Fin n → ℝ), W ≤ (Q - 1).mulVecLin.range →
      (∀ v ∈ W, A.mulVec v ∈ W) → W = ⊥) :
    (Q - 1).mulVecLin.range ≤ displacementOrbitSpan A (conjugate A Q - A) (Q - 1).rank := by
  have hB : (conjugate A Q).IsSymm := by
    unfold Matrix.IsSymm conjugate
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hA.eq, Matrix.mul_assoc]
  have hD : (conjugate A Q - A).IsSymm := hB.sub hA
  intro u hu
  apply (mem_submodule_iff_dot_annihilator _ u).mpr
  intro x hx
  have hRx : (Q - 1).mulVec x = 0 := commutator_kernel_capture
    A.mulVecLin (Q - 1).mulVecLin Q.mulVecLin (conjugate A Q - A).mulVecLin
    (movement_commutator A Q hQ) hno x (displacement_annihilator_kernels A _ hA hD _ x hx)
  obtain ⟨v, rfl⟩ := hu
  change x ⬝ᵥ (Q - 1).mulVec v = 0
  rw [← dotProduct_transpose_mulVec (Q - 1) v x]
  rw [(movement_transpose_kernel_iff Q hQ x).mpr hRx, dotProduct_zero]

/-- Full same-target invariant removal and finite displacement capture. -/
theorem exists_same_target_captured_movement {n : ℕ} (A Q : RealMatrix n)
    (hA : A.IsSymm) (hQ : Orthogonal Q) :
    ∃ Q₀ : RealMatrix n, Orthogonal Q₀ ∧ conjugate A Q₀ = conjugate A Q ∧
      (Q₀ - 1).rank ≤ (Q - 1).rank ∧
      (∀ W : Submodule ℝ (Fin n → ℝ), W ≤ (Q₀ - 1).mulVecLin.range →
        (∀ v ∈ W, A.mulVec v ∈ W) → W = ⊥) ∧
      (Q₀ - 1).mulVecLin.range ≤
        displacementOrbitSpan A (conjugate A Q - A) (Q₀ - 1).rank := by
  obtain ⟨Q₀, hQ₀, ht, hr, hn⟩ := exists_same_target_no_invariant_movement A Q hA hQ
  refine ⟨Q₀, hQ₀, ht, hr, hn, ?_⟩
  rw [← ht]
  exact invariant_free_movement_capture A Q₀ hA hQ₀ hn

end AdaptiveOrthogonalRigidity
