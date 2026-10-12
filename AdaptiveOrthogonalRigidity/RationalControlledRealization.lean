import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import AdaptiveOrthogonalRigidity.KrylovColumns
import Mathlib.Tactic.Abel

open Matrix Polynomial
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Iterating the controlled realization retains the input correction at every
power. No inverse of a polynomial in `C` is used. -/
theorem controlled_realization_power {K ι σ τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ]
    (C : Matrix ι ι K) (X : Matrix ι σ K) (M : Matrix σ σ K)
    (V : Matrix ι τ K) (F : Matrix τ σ K)
    (h : C * X = X * M + V * F) (n : ℕ) :
    C ^ n * X = X * M ^ n +
      ∑ a ∈ Finset.range n, C ^ (n - 1 - a) * V * F * M ^ a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, Matrix.mul_add, Matrix.mul_sum]
    have hfirst : C * (X * M ^ n) = X * M ^ (n + 1) + V * F * M ^ n := by
      rw [← Matrix.mul_assoc, h, Matrix.add_mul, Matrix.mul_assoc, ← pow_succ']
    rw [hfirst, Finset.sum_range_succ]
    have hs : (∑ a ∈ Finset.range n, C * (C ^ (n - 1 - a) * V * F * M ^ a)) =
        ∑ a ∈ Finset.range n, C ^ (n + 1 - 1 - a) * V * F * M ^ a := by
      apply Finset.sum_congr rfl
      intro a ha
      have han : a < n := Finset.mem_range.mp ha
      have hexp : n + 1 - 1 - a = (n - 1 - a) + 1 := by omega
      rw [hexp, pow_succ']
      simp only [Matrix.mul_assoc]
    rw [hs]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, Matrix.one_mul]
    abel

/-- The actual finite input-Krylov span. -/
def controlledKrylovSpan {K ι τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (k : ℕ) (C : Matrix ι ι K)
    (V : Matrix ι τ K) : Submodule K (ι → K) :=
  Submodule.span K (Set.range (krylovColumns k C V.col))

theorem controlledKrylovSpan_pow_input_mem {K ι τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype τ]
    (k : ℕ) (C : Matrix ι ι K) (V : Matrix ι τ K)
    (a : ℕ) (ha : a ≤ k) (u : τ → K) :
    (C ^ a * V).mulVec u ∈ controlledKrylovSpan k C V := by
  rw [Matrix.mulVec_eq_sum]
  apply Submodule.sum_mem
  intro t _
  rw [op_smul_eq_smul]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(⟨a, by omega⟩, t), by
    funext i
    rfl⟩

/-- The controlled realization satisfies its state annihilator modulo the
actual finite input-Krylov span. -/
theorem controlled_annihilator_mem_krylov {K ι σ τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ]
    (k : ℕ) (C : Matrix ι ι K) (X : Matrix ι σ K) (M : Matrix σ σ K)
    (V : Matrix ι τ K) (F : Matrix τ σ K)
    (h : C * X = X * M + V * F)
    (g : Polynomial K) (hg : g.natDegree ≤ k) (hz : Polynomial.aeval M g = 0)
    (v : σ → K) :
    (Polynomial.aeval C g * X).mulVec v ∈ controlledKrylovSpan k C V := by
  have hn (n : ℕ) (hn : n ≤ k) :
      ((C ^ n * X - X * M ^ n).mulVec v) ∈ controlledKrylovSpan k C V := by
    rw [controlled_realization_power C X M V F h, add_sub_cancel_left, Matrix.sum_mulVec]
    apply Submodule.sum_mem
    intro a ha
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact controlledKrylovSpan_pow_input_mem k C V (n - 1 - a) (by omega) _
  have heq : Polynomial.aeval C g * X - X * Polynomial.aeval M g =
      ∑ a ∈ Finset.range (k + 1), g.coeff a • (C ^ a * X - X * M ^ a) := by
    rw [Polynomial.aeval_eq_sum_range' (n := k + 1) (by omega),
      Polynomial.aeval_eq_sum_range' (n := k + 1) (by omega)]
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
      smul_sub, Finset.sum_sub_distrib]
  rw [hz, Matrix.mul_zero, sub_zero] at heq
  rw [heq, Matrix.sum_mulVec]
  apply Submodule.sum_mem
  intro a ha
  rw [Matrix.smul_mulVec]
  exact Submodule.smul_mem _ _ (hn a (by have := Finset.mem_range.mp ha; omega))

/-- A state annihilator supplies a polynomial filter for every output column.
The statement is a span membership, allowing the coefficients to be chosen
jointly afterwards. -/
theorem controlled_output_filter_mem_krylov {K ι σ τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ]
    (k : ℕ) (C : Matrix ι ι K) (X : Matrix ι σ K) (M : Matrix σ σ K)
    (V : Matrix ι τ K) (F : Matrix τ σ K)
    (h : C * X = X * M + V * F)
    (g : Polynomial K) (hg : g.natDegree ≤ k) (hz : Polynomial.aeval M g = 0)
    (l : σ → K) (u : τ → K) :
    (Polynomial.aeval C g).mulVec (X.mulVec l + V.mulVec u) ∈
      controlledKrylovSpan k C V := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  apply Submodule.add_mem
  · exact controlled_annihilator_mem_krylov k C X M V F h g hg hz l
  · rw [Polynomial.aeval_eq_sum_range' (n := k + 1) (by omega),
      Matrix.sum_mul, Matrix.sum_mulVec]
    apply Submodule.sum_mem
    intro a ha
    rw [Matrix.smul_mul, Matrix.smul_mulVec]
    exact Submodule.smul_mem _ _
      (controlledKrylovSpan_pow_input_mem k C V a (by have := Finset.mem_range.mp ha; omega) u)

/-- A vector in the actual degree-k Krylov span has a polynomial input
representation of degree at most k. -/
theorem controlledKrylovSpan_polynomial_representation {K ι τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype τ]
    (k : ℕ) (C : Matrix ι ι K) (V : Matrix ι τ K)
    (w : ι → K) (hw : w ∈ controlledKrylovSpan k C V) :
    ∃ P : τ → Polynomial K, (∀ t, (P t).natDegree ≤ k) ∧
      w = ∑ t, (Polynomial.aeval C (P t)).mulVec (V.col t) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hw
  let P : τ → Polynomial.degreeLT K (k + 1) := fun t =>
    (Polynomial.degreeLTEquiv K (k + 1)).symm (fun a => c (a, t))
  have hcoeff (t : τ) (a : Fin (k + 1)) : (P t).val.coeff a.val = c (a, t) :=
    congrFun ((Polynomial.degreeLTEquiv K (k + 1)).apply_symm_apply (fun a => c (a, t))) a
  have hdeg (t : τ) : (P t).val.natDegree ≤ k := by
    apply Polynomial.natDegree_le_of_degree_le
    apply Polynomial.mem_degreeLE.mp
    have hh := (P t).property
    simpa only [Polynomial.degreeLT_succ_eq_degreeLE] using hh
  refine ⟨fun t => (P t).val, hdeg, ?_⟩
  have heval (t : τ) : Polynomial.aeval C (P t).val =
      ∑ a : Fin (k + 1), c (a, t) • C ^ a.val := by
    rw [Polynomial.aeval_eq_sum_range' (n := k + 1) (by have := hdeg t; omega),
      ← Fin.sum_univ_eq_sum_range]
    simp only [hcoeff]
  rw [← hc, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [heval, Matrix.sum_mulVec, Matrix.smul_mulVec, krylovColumns]

/-- Cayley-Hamilton constructs a monic filter directly from the real or
arbitrary-field state realization, simultaneously for every output column. -/
theorem controlled_realization_monic_filter {K ι σ τ υ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ]
    (C : Matrix ι ι K) (X : Matrix ι σ K) (M : Matrix σ σ K)
    (V : Matrix ι τ K) (F : Matrix τ σ K)
    (L : Matrix σ υ K) (G : Matrix τ υ K)
    (h : C * X = X * M + V * F) :
    ∃ (g : Polynomial K) (P : τ → υ → Polynomial K),
      g.Monic ∧ g.natDegree = Fintype.card σ ∧
      (∀ t j, (P t j).natDegree ≤ Fintype.card σ) ∧
      ∀ j, (Polynomial.aeval C g).mulVec ((X * L + V * G).col j) =
        ∑ t, (Polynomial.aeval C (P t j)).mulVec (V.col t) := by
  have hm (j : υ) : (Polynomial.aeval C M.charpoly).mulVec ((X * L + V * G).col j) ∈
      controlledKrylovSpan (Fintype.card σ) C V := by
    have hh := controlled_output_filter_mem_krylov (Fintype.card σ) C X M V F h
      M.charpoly (by rw [Matrix.charpoly_natDegree_eq_dim]) M.aeval_self_charpoly (L.col j) (G.col j)
    exact hh
  choose P hd hp using fun j => controlledKrylovSpan_polynomial_representation
    (Fintype.card σ) C V _ (hm j)
  exact ⟨M.charpoly, fun t j => P j t, M.charpoly_monic, M.charpoly_natDegree_eq_dim,
    fun t j => hd j t, hp⟩

/-- The polynomial defect is supported on one fewer input-Krylov powers
than the degree of the polynomial. -/
theorem controlled_polynomial_defect_mem_krylov {K ι σ τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ]
    (k : ℕ) (C : Matrix ι ι K) (X : Matrix ι σ K) (M : Matrix σ σ K)
    (V : Matrix ι τ K) (F : Matrix τ σ K)
    (h : C * X = X * M + V * F)
    (g : Polynomial K) (hg : g.natDegree ≤ k + 1) (v : σ → K) :
    ((Polynomial.aeval C g * X - X * Polynomial.aeval M g).mulVec v) ∈
      controlledKrylovSpan k C V := by
  have hn (n : ℕ) (hn : n ≤ k + 1) :
      ((C ^ n * X - X * M ^ n).mulVec v) ∈ controlledKrylovSpan k C V := by
    rw [controlled_realization_power C X M V F h, add_sub_cancel_left, Matrix.sum_mulVec]
    apply Submodule.sum_mem
    intro a ha
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact controlledKrylovSpan_pow_input_mem k C V (n - 1 - a) (by omega) _
  have heq : Polynomial.aeval C g * X - X * Polynomial.aeval M g =
      ∑ a ∈ Finset.range (k + 2), g.coeff a • (C ^ a * X - X * M ^ a) := by
    rw [Polynomial.aeval_eq_sum_range' (n := k + 2) (by omega),
      Polynomial.aeval_eq_sum_range' (n := k + 2) (by omega)]
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
      smul_sub, Finset.sum_sub_distrib]
  rw [heq, Matrix.sum_mulVec]
  apply Submodule.sum_mem
  intro a ha
  rw [Matrix.smul_mulVec]
  exact Submodule.smul_mem _ _ (hn a (by have := Finset.mem_range.mp ha; omega))

end AdaptiveOrthogonalRigidity
