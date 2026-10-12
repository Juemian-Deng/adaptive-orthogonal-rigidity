import AdaptiveOrthogonalRigidity.BoundaryRealKrylov
import AdaptiveOrthogonalRigidity.CanonicalTarget

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

theorem matrix_submatrix_pow_equiv {K ι ν : Type*} [Semiring K]
    [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
    (C : Matrix ι ι K) (e : ν ≃ ι) (a : ℕ) :
    (C.submatrix e e) ^ a = (C ^ a).submatrix e e := by
  induction a with
  | zero => simp only [pow_zero, Matrix.submatrix_one_equiv]
  | succ a ih => rw [pow_succ, ih, Matrix.submatrix_mul_equiv, pow_succ]

theorem krylov_columns_reindex {K ι ν τ : Type*} [Field K]
    [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
    (C : Matrix ι ι K) (V : τ → ι → K) (e : ν ≃ ι) (d : ℕ) :
    krylovColumns d (C.submatrix e e) (fun j i => V j (e i)) =
      fun j i => krylovColumns d C V j (e i) := by
  funext j
  rw [krylovColumns, matrix_submatrix_pow_equiv, Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_def, Equiv.apply_symm_apply]
  rfl

/-- Independence in enumerated bulk rows is exactly independence in the
original remaining vertex labels. -/
theorem krylov_independent_of_reindex {K ι ν τ : Type*} [Field K]
    [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
    (C : Matrix ι ι K) (V : τ → ι → K) (e : ν ≃ ι) (d : ℕ)
    (hI : LinearIndependent K (krylovColumns d (C.submatrix e e) (fun j i => V j (e i)))) :
    LinearIndependent K (krylovColumns d C V) := by
  rw [krylov_columns_reindex] at hI
  exact LinearIndependent.of_comp (LinearMap.funLeft K K e) hI

/-- The integer-minor real Krylov lift on the actual original complementary
vertex type, preserving the full constant mark and boundary column list. -/
theorem original_boundary_real_krylov_independent {n : ℕ}
    (S : Finset (Fin n)) (d : ℕ) (ω : GraphSample n)
    (hgood : ω ∉ fixedBoundaryKrylovFailure S d) :
    LinearIndependent ℝ (krylovColumns d
      ((adjacency ω).submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val))
      (augmentedColumns ((adjacency ω).submatrix (fun i : ↑Sᶜ => i.val) (fun j : S => j.val)))) := by
  apply krylov_independent_of_reindex _ _ (boundaryBulkEquiv S) d
  have hh := boundary_real_krylov_independent S d ω hgood
  have he : (fun j i => augmentedColumns
      ((adjacency ω).submatrix (fun i : ↑Sᶜ => i.val) (fun j : S => j.val)) j (boundaryBulkEquiv S i)) =
      (fun j : Option S => j.elim (fun _ => (1 : ℝ))
        (fun k i => adjacency ω (boundaryBulkEmbedding S i) k.val)) := by
    funext j
    cases j <;> rfl
  rw [he]
  exact hh

end AdaptiveOrthogonalRigidity
