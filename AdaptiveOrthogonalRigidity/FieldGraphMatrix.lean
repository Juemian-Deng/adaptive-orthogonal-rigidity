import AdaptiveOrthogonalRigidity.GraphStarSplit

open Matrix
open scoped Classical

namespace AdaptiveOrthogonalRigidity

/-- The original graph bits embedded into a field, with an arbitrary prescribed
diagonal. Recursion exposes only the last original vertex star. -/
def fieldGraphMatrix (K : Type*) [Zero K] [One K] :
    (n : ℕ) → (Fin n → K) → GraphSample n → Matrix (Fin n) (Fin n) K
  | 0, _, _ => fun i => Fin.elim0 i
  | n + 1, diag, ω =>
    (borderMatrix (fieldGraphMatrix K n (fun i => diag i.castSucc) (graphDropLast ω))
      (boolVector (graphLastStar ω)) (diag (Fin.last n))).submatrix finSuccEquivLast finSuccEquivLast

theorem fieldGraphMatrix_diag {K : Type*} [Zero K] [One K]
    (n : ℕ) (diag : Fin n → K) (ω : GraphSample n) (i : Fin n) :
    fieldGraphMatrix K n diag ω i i = diag i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    induction i using Fin.lastCases with
    | last => simp [fieldGraphMatrix, Matrix.submatrix, borderMatrix]
    | cast i =>
      simpa [fieldGraphMatrix, Matrix.submatrix, borderMatrix] using
        (ih (fun i => diag i.castSucc) (graphDropLast ω) i)

theorem fieldGraphMatrix_isSymm {K : Type*} [Zero K] [One K]
    (n : ℕ) (diag : Fin n → K) (ω : GraphSample n) : (fieldGraphMatrix K n diag ω).IsSymm := by
  induction n with
  | zero => apply Matrix.IsSymm.ext; intro i; exact Fin.elim0 i
  | succ n ih =>
    exact (borderMatrix_isSymm _ (ih (fun i => diag i.castSucc) (graphDropLast ω)) _ _).submatrix _

theorem fieldGraphMatrix_upper {K : Type*} [Zero K] [One K]
    (n : ℕ) (diag : Fin n → K) (ω : GraphSample n) (i j : Fin n) (hij : i < j) :
    fieldGraphMatrix K n diag ω i j = bitValue (ω ⟨(i, j), hij⟩) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    induction j using Fin.lastCases with
    | last =>
      induction i using Fin.lastCases with
      | last => exact False.elim (lt_irrefl _ hij)
      | cast i =>
        simp [fieldGraphMatrix, Matrix.submatrix, borderMatrix, boolVector, graphLastStar, edgeToLast]
    | cast j =>
      induction i using Fin.lastCases with
      | last => exact False.elim (by have := j.isLt; change n < j.val at hij; omega)
      | cast i =>
        simp only [fieldGraphMatrix, Matrix.submatrix_apply, finSuccEquivLast_castSucc, borderMatrix]
        exact ih _ _ i j hij

/-- Over the reals with zero diagonal this is exactly the manuscript's
original adjacency matrix, not a substituted matrix model. -/
theorem fieldGraphMatrix_real_zero (n : ℕ) (ω : GraphSample n) :
    fieldGraphMatrix ℝ n (fun _ => 0) ω = adjacency ω := by
  ext i j
  by_cases hij : i < j
  · rw [fieldGraphMatrix_upper n _ ω i j hij]
    simp only [adjacency, dite_eq_left hij]
    rfl
  · by_cases hji : j < i
    · rw [← (fieldGraphMatrix_isSymm n (fun _ => (0 : ℝ)) ω).apply i j,
        fieldGraphMatrix_upper n _ ω j i hji]
      simp only [adjacency, dite_eq_right hij, dite_eq_left hji]
      rfl
    · have heq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      subst j
      rw [fieldGraphMatrix_diag]
      simp [adjacency]

theorem square_kernel_finrank_reindex {K ι κ : Type*} [Field K]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix ι ι K) (e : κ ≃ ι) :
    Module.finrank K (M.submatrix e e).mulVecLin.ker = Module.finrank K M.mulVecLin.ker := by
  have h1 := (M.submatrix e e).mulVecLin.finrank_range_add_finrank_ker
  have h2 := M.mulVecLin.finrank_range_add_finrank_ker
  change (M.submatrix e e).rank + _ = _ at h1
  change M.rank + _ = _ at h2
  rw [Matrix.rank_submatrix, Module.finrank_pi, Fintype.card_congr e] at h1
  rw [Module.finrank_pi] at h2
  omega

noncomputable def fieldGraphCorank (K : Type*) [Field K]
    (n : ℕ) (diag : Fin n → K) (ω : GraphSample n) : ℕ :=
  Module.finrank K (fieldGraphMatrix K n diag ω).mulVecLin.ker

theorem fieldGraphCorank_succ {K : Type*} [Field K] (n : ℕ)
    (diag : Fin (n + 1) → K) (ω : GraphSample (n + 1)) :
    fieldGraphCorank K (n + 1) diag ω = Module.finrank K
      (symmetricBorderMap (fieldGraphMatrix K n (fun i => diag i.castSucc) (graphDropLast ω))
        (boolVector (graphLastStar ω)) (diag (Fin.last n))).ker := by
  exact (square_kernel_finrank_reindex
    (borderMatrix (fieldGraphMatrix K n (fun i => diag i.castSucc) (graphDropLast ω))
      (boolVector (graphLastStar ω)) (diag (Fin.last n))) finSuccEquivLast).trans
        (borderMatrix_kernel_finrank _ _ _)

end AdaptiveOrthogonalRigidity
