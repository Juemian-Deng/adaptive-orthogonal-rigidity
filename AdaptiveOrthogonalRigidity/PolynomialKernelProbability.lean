import AdaptiveOrthogonalRigidity.SymmetricCorank
import AdaptiveOrthogonalRigidity.FieldGraphAlgebra
import AdaptiveOrthogonalRigidity.PolynomialRootFamily

open MeasureTheory Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Good simultaneous eigenspace bounds in one prescribed splitting field
control every original low-degree polynomial, including nonmonic ones. -/
theorem graph_polynomial_kernel_of_root_bounds {K : Type*} [Field K] [IsAlgClosed K]
    (f : ZMod 3 →+* K) (n d t : ℕ) (diag : Fin n → ZMod 3) (ω : GraphSample n)
    (hroot : ∀ c ∈ lowDegreeRoots f d,
      fieldGraphCorank K n (fun i => f (diag i) - c) ω ≤ t)
    (q : Polynomial (ZMod 3)) (hq : q ≠ 0) (hdeg : q.natDegree ≤ d) :
    Module.finrank (ZMod 3) (Polynomial.aeval (fieldGraphMatrix (ZMod 3) n diag ω) q).mulVecLin.ker
      ≤ d * t := by
  let M := fieldGraphMatrix (ZMod 3) n diag ω
  rw [← square_kernel_finrank_map_field f (Polynomial.aeval M q), matrix_aeval_map_field]
  have h := split_matrix_polynomial_kernel_bound (M.map f) (q.map f)
    (Polynomial.map_ne_zero hq) (IsAlgClosed.splits _) t (by
      intro c hc
      rw [show M.map f = fieldGraphMatrix K n (fun i => f (diag i)) ω from
        fieldGraphMatrix_map f n diag ω, fieldGraphMatrix_sub_scalar]
      exact hroot c (mem_lowDegreeRoots f d q hq hdeg hc))
  exact h.trans (Nat.mul_le_mul_right t ((Polynomial.natDegree_map f).trans_le hdeg))

noncomputable def polynomialKernelFailure (n d t : ℕ) (diag : Fin n → ZMod 3) : Set (GraphSample n) :=
  {ω | ∃ q : Polynomial (ZMod 3), q ≠ 0 ∧ q.natDegree ≤ d ∧
    d * t < Module.finrank (ZMod 3)
      (Polynomial.aeval (fieldGraphMatrix (ZMod 3) n diag ω) q).mulVecLin.ker}

/-- The complete polynomial-kernel exception bound, uniform over all nonzero
polynomials of degree at most d. The root family is independent of the sample. -/
theorem polynomial_kernel_bound (n d t : ℕ) (diag : Fin n → ZMod 3)
    {α : ℝ} (hα : 0 ≤ α) (hαhalf : α ≤ 1 / 2)
    (p : EdgeParameters n) (hp : Admissible α p) :
    eventProbability p (polynomialKernelFailure n d t diag) ≤
      (rootCount d : ℝ) * (2 : ℝ) ^ n * (beta α) ^ (((t : ℝ) ^ 2 - 1) / 4) := by
  let K := AlgebraicClosure (ZMod 3)
  let f : ZMod 3 →+* K := algebraMap (ZMod 3) K
  let J := lowDegreeRoots f d
  let E (c : J) : Set (GraphSample n) :=
    {ω | t ≤ fieldGraphCorank K n (fun i => f (diag i) - c.val) ω}
  let D := (2 : ℝ) ^ n * (beta α) ^ (((t : ℝ) ^ 2 - 1) / 4)
  have hD : 0 ≤ D := mul_nonneg (pow_nonneg (by norm_num) _)
    (Real.rpow_nonneg (by dsimp [beta]; linarith) _)
  have hsub : polynomialKernelFailure n d t diag ⊆ ⋃ c : J, E c := by
    rintro ω ⟨q, hq, hdeg, hbad⟩
    by_contra hω
    have hroot : ∀ c ∈ J, fieldGraphCorank K n (fun i => f (diag i) - c) ω ≤ t := by
      intro c hc
      have hnot : ¬ ω ∈ E ⟨c, hc⟩ := fun h => hω (Set.mem_iUnion.mpr ⟨⟨c, hc⟩, h⟩)
      exact (lt_of_not_ge hnot).le
    exact (not_lt_of_ge (graph_polynomial_kernel_of_root_bounds f n d t diag ω hroot q hq hdeg)) hbad
  have hc (c : J) : eventProbability p (E c) ≤ D :=
    symmetric_corank_bound n t (fun i => f (diag i) - c.val) hα hαhalf p hp
  calc
    _ ≤ eventProbability p (⋃ c : J, E c) := measureReal_mono hsub
    _ ≤ ∑ c : J, eventProbability p (E c) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _c : J, D := Finset.sum_le_sum (fun c _ => hc c)
    _ = (J.card : ℝ) * D := by simp
    _ ≤ (rootCount d : ℝ) * D := mul_le_mul_of_nonneg_right (by exact_mod_cast lowDegreeRoots_card f d) hD
    _ = _ := by simp only [D, mul_assoc]

end AdaptiveOrthogonalRigidity
