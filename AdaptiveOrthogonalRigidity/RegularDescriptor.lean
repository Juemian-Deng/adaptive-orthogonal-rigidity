import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Regular square descriptor pencils

Regularity is polynomial nonvanishing. The leading coefficient E is never
assumed invertible. All column-independence statements concern actual matrices.
-/

open Matrix
open scoped BigOperators Classical
noncomputable section
namespace AdaptiveOrthogonalRigidity

/-- The affine polynomial pencil associated with the descriptor action. -/
def descriptorPencil {K ι : Type*} [CommRing K] (E M : Matrix ι ι K) : Matrix ι ι (Polynomial K) :=
  (Polynomial.X : Polynomial K) • E.map Polynomial.C - M.map Polynomial.C

/-- A square pencil is regular when its polynomial determinant is nonzero. -/
def regularPencil {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    (E M : Matrix ι ι K) : Prop := (descriptorPencil E M).det ≠ 0

/-- Regularity rules out a nonzero common constant kernel vector, even for singular E. -/
theorem regularPencil_common_kernel {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {E M : Matrix ι ι K} (hreg : regularPencil E M) (a : ι → K)
    (hE : E.mulVec a = 0) (hM : M.mulVec a = 0) : a = 0 := by
  have hmapE : (E.map Polynomial.C).mulVec (Polynomial.C ∘ a) = 0 := by
    funext i
    rw [← RingHom.map_mulVec, hE]
    simp
  have hmapM : (M.map Polynomial.C).mulVec (Polynomial.C ∘ a) = 0 := by
    funext i
    rw [← RingHom.map_mulVec, hM]
    simp
  have hz : (descriptorPencil E M).mulVec (Polynomial.C ∘ a) = 0 := by
    simp only [descriptorPencil, Matrix.sub_mulVec, Matrix.smul_mulVec, hmapE, hmapM,
      smul_zero, sub_zero]
  have ha := Matrix.mulVec_injective_of_det_ne_zero hreg
    (hz.trans (Matrix.mulVec_zero _).symm)
  funext i
  apply Polynomial.C_injective
  simpa only [Function.comp_apply, Pi.zero_apply, map_zero] using congrFun ha i

/-- Joint column independence separates the state and input coefficients. -/
theorem joint_columns_eq_zero {K ν ι π : Type*} [Field K]
    [Fintype ι] [Fintype π] {X : Matrix ν ι K} {V : Matrix ν π K}
    (hjoint : LinearIndependent K (Matrix.fromCols X V).col)
    (a : ι → K) (b : π → K) (h : X.mulVec a + V.mulVec b = 0) : a = 0 ∧ b = 0 := by
  have hi := Matrix.mulVec_injective_iff.mpr hjoint
  have hh : (Matrix.fromCols X V).mulVec (Sum.elim a b) =
      (Matrix.fromCols X V).mulVec 0 := by
    rw [Matrix.mulVec_zero]
    simpa only [Matrix.fromCols_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr] using h
  have he := hi hh
  exact ⟨funext (fun i => congrFun he (Sum.inl i)), funext (fun i => congrFun he (Sum.inr i))⟩

/-- Dynamic descriptor input has full column rank as a consequence, not a premise.
This uses only regularity and the actual joint state/input independence. -/
theorem regular_descriptor_dynamic_independent {K ν ι π : Type*} [Field K]
    [Fintype ν] [Fintype ι] [Fintype π] [DecidableEq ι]
    (C : Matrix ν ν K) (X : Matrix ν ι K) (V : Matrix ν π K)
    (E M : Matrix ι ι K) (F B : Matrix π ι K)
    (hjoint : LinearIndependent K (Matrix.fromCols X V).col)
    (hreg : regularPencil E M) (hact : C * (X * E + V * F) = X * M + V * B) :
    LinearIndependent K (X * E + V * F).col := by
  apply Matrix.mulVec_injective_iff.mp
  change Function.Injective (X * E + V * F).mulVecLin
  apply (LinearMap.ker_eq_bot.mp ?_)
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  change (X * E + V * F).mulVec a = 0 at ha
  have hEF : E.mulVec a = 0 ∧ F.mulVec a = 0 := by
    apply joint_columns_eq_zero hjoint
    simpa only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec] using ha
  have hMB : M.mulVec a = 0 ∧ B.mulVec a = 0 := by
    apply joint_columns_eq_zero hjoint
    have hh := congrArg (fun A : Matrix ν ι K => A.mulVec a) hact
    rw [← Matrix.mulVec_mulVec, ha, Matrix.mulVec_zero] at hh
    simpa only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec] using hh.symm
  exact regularPencil_common_kernel hreg a hEF.1 hMB.1

end AdaptiveOrthogonalRigidity
