import AdaptiveOrthogonalRigidity.SymmetricBordering

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

def optionCoordinates (K ι : Type*) [Field K] : (Option ι → K) ≃ₗ[K] ((ι → K) × K) where
  toFun v := (fun i => v (some i), v none)
  invFun v := fun o => match o with | none => v.2 | some i => v.1 i
  left_inv v := by funext i; cases i <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def borderMatrix {K ι : Type*} (A : Matrix ι ι K) (x : ι → K) (a : K) :
    Matrix (Option ι) (Option ι) K
  | none, none => a
  | none, some j => x j
  | some i, none => x i
  | some i, some j => A i j

theorem borderMatrix_isSymm {K ι : Type*} (A : Matrix ι ι K) (hA : A.IsSymm)
    (x : ι → K) (a : K) : (borderMatrix A x a).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  cases i <;> cases j <;> simp only [borderMatrix]
  exact hA.apply _ _

theorem borderMatrix_mulVec_coordinates {K ι : Type*} [Field K] [Fintype ι]
    (A : Matrix ι ι K) (x : ι → K) (a : K) (v : Option ι → K) :
    optionCoordinates K ι ((borderMatrix A x a).mulVec v) =
      symmetricBorderMap A x a (optionCoordinates K ι v) := by
  apply Prod.ext
  · funext i
    simp [optionCoordinates, symmetricBorderMap, Matrix.mulVec, dotProduct,
      Fintype.sum_option, borderMatrix, smul_eq_mul, mul_comm, add_comm]
  · simp [optionCoordinates, symmetricBorderMap, Matrix.mulVec, dotProduct,
      Fintype.sum_option, borderMatrix, add_comm]

theorem borderMatrix_kernel_finrank {K ι : Type*} [Field K] [Fintype ι]
    (A : Matrix ι ι K) (x : ι → K) (a : K) :
    Module.finrank K (borderMatrix A x a).mulVecLin.ker =
      Module.finrank K (symmetricBorderMap A x a).ker := by
  let e := optionCoordinates K ι
  let B := symmetricBorderMap A x a
  let M := (borderMatrix A x a).mulVecLin
  have hinter (v : Option ι → K) : e (M v) = B (e v) := borderMatrix_mulVec_coordinates A x a v
  let ke : M.ker ≃ₗ[K] B.ker := {
    toFun v := ⟨e v.val, by
      change B (e v.val) = 0
      rw [← hinter, v.property, map_zero]⟩
    invFun v := ⟨e.symm v.val, by
      apply e.injective
      rw [hinter, e.apply_symm_apply, v.property, map_zero]⟩
    left_inv v := Subtype.ext (e.symm_apply_apply v.val)
    right_inv v := Subtype.ext (e.apply_symm_apply v.val)
    map_add' v w := Subtype.ext (e.map_add v.val w.val)
    map_smul' c v := Subtype.ext (e.map_smul c v.val) }
  exact ke.finrank_eq

theorem borderMatrix_kernel_drop {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (hA : A.IsSymm) (x : ι → K) (a : K) (hx : x ∉ A.mulVecLin.range) :
    Module.finrank K (borderMatrix A x a).mulVecLin.ker + 1 = Module.finrank K A.mulVecLin.ker := by
  rw [borderMatrix_kernel_finrank]
  exact symmetric_border_kernel_drop A hA x a hx

theorem borderMatrix_kernel_growth {K ι : Type*} [Field K] [Fintype ι]
    (A : Matrix ι ι K) (x : ι → K) (a : K) :
    Module.finrank K (borderMatrix A x a).mulVecLin.ker ≤ Module.finrank K A.mulVecLin.ker + 1 := by
  rw [borderMatrix_kernel_finrank]
  exact symmetric_border_kernel_growth A x a

end AdaptiveOrthogonalRigidity
