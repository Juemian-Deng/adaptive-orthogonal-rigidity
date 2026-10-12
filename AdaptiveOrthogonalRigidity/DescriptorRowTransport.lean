import AdaptiveOrthogonalRigidity.DescriptorReindex
import AdaptiveOrthogonalRigidity.KrylovReindex
import Mathlib.Data.Matrix.ColumnRowPartitioned

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

theorem independent_columns_reindex_rows {K ι ν τ : Type*} [Field K]
    (X : Matrix ι τ K) (e : ν ≃ ι) (hX : LinearIndependent K X.col) :
    LinearIndependent K (X.submatrix e id).col := by
  have hinj : Function.Injective (LinearMap.funLeft K K e) := by
    intro x y h
    funext i
    have hh := congrFun h (e.symm i)
    change x (e (e.symm i)) = y (e (e.symm i)) at hh
    simpa only [Equiv.apply_symm_apply] using hh
  exact hX.map' (LinearMap.funLeft K K e) (LinearMap.ker_eq_bot.mpr hinj)

theorem independent_joint_columns_reindex_rows {K ι ν τ υ : Type*} [Field K]
    (X : Matrix ι τ K) (V : Matrix ι υ K) (e : ν ≃ ι)
    (hXV : LinearIndependent K (Matrix.fromCols X V).col) :
    LinearIndependent K (Matrix.fromCols (X.submatrix e id) (V.submatrix e id)).col := by
  have heq : Matrix.fromCols (X.submatrix e id) (V.submatrix e id) =
      (Matrix.fromCols X V).submatrix e id := by
    ext i j
    cases j <;> rfl
  rw [heq]
  exact independent_columns_reindex_rows _ e hXV

theorem krylov_input_independent {K ι τ : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι K) (V : τ → ι → K) (d : ℕ)
    (hI : LinearIndependent K (krylovColumns d C V)) : LinearIndependent K V := by
  let f : τ → Fin (d + 1) × τ := fun j => (⟨0, Nat.zero_lt_succ d⟩, j)
  have hh := hI.comp f (fun a b h => congrArg Prod.snd h)
  simpa only [f, Function.comp_def, krylovColumns, pow_zero, Matrix.one_mulVec] using hh

theorem matrix_mul_reindex_rows {K ι ν ξ η : Type*} [CommSemiring K] [Fintype ξ]
    (A : Matrix ι ξ K) (D : Matrix ξ η K) (e : ν ≃ ι) :
    A.submatrix e id * D = (A * D).submatrix e id := by
  simpa only [Equiv.coe_refl, Matrix.submatrix_id_id] using
    Matrix.submatrix_mul_equiv A D e (Equiv.refl _) id

/-- Restricting to an equivalent row type preserves the full descriptor
action and every output equation, with all coefficient matrices unchanged. -/
theorem descriptor_row_transport {K ι ν τ υ : Type*} [Field K]
    [Fintype ι] [Fintype ν] [Fintype τ] {k : ℕ}
    (e : ν ≃ ι) (C : Matrix ι ι K) (V : Matrix ι τ K)
    (Z : Matrix ι υ K) (X : Matrix ι (Fin k) K)
    (E M : Matrix (Fin k) (Fin k) K) (F B : Matrix τ (Fin k) K)
    (L : Matrix (Fin k) υ K) (G : Matrix τ υ K)
    (hact : C * (X * E + V * F) = X * M + V * B)
    (hout : Z = X * L + V * G) :
    C.submatrix e e * (X.submatrix e id * E + V.submatrix e id * F) =
      X.submatrix e id * M + V.submatrix e id * B ∧
    Z.submatrix e id = X.submatrix e id * L + V.submatrix e id * G := by
  constructor
  · simp only [matrix_mul_reindex_rows]
    change C.submatrix e e * ((X * E + V * F).submatrix e id) =
      (X * M + V * B).submatrix e id
    rw [Matrix.submatrix_mul_equiv, hact]
  · simp only [matrix_mul_reindex_rows]
    rw [hout]
    rfl

end AdaptiveOrthogonalRigidity
