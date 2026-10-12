import AdaptiveOrthogonalRigidity.RationalControlledSpan

open Matrix Polynomial
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Every finite-dimensional subspace has an actual ambient coordinate basis
matrix whose column range is exactly that subspace. -/
theorem controlled_subspace_basis_matrix {L ι : Type*} [Field L] [Fintype ι]
    (H : Submodule L (ι → L)) :
    ∃ X : Matrix ι (Fin (Module.finrank L H)) L, X.mulVecLin.range = H := by
  let b := Module.finBasis L H
  let X : Matrix ι (Fin (Module.finrank L H)) L := fun i j => (b j).val i
  have hc (j : Fin (Module.finrank L H)) : X.col j = (b j).val := rfl
  refine ⟨X, le_antisymm ?_ ?_⟩
  · rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact (b j).property
  · intro x hx
    refine ⟨fun j => b.repr ⟨x, hx⟩ j, ?_⟩
    have hh := congrArg (fun w : H => w.val) (b.sum_repr ⟨x, hx⟩)
    change X.mulVec _ = x
    rw [Matrix.mulVec_eq_sum]
    simpa only [op_smul_eq_smul, ← Matrix.col_def, hc,
      Submodule.coe_sum, Submodule.coe_smul] using hh

/-- Choose genuine state coefficients from a controlled subspace, retaining
all original output columns. -/
theorem controlled_subspace_realization {L ι τ υ : Type*} [Field L]
    [Fintype ι] [DecidableEq ι] [Fintype τ] [Fintype υ]
    (C : Matrix ι ι L) (V : Matrix ι τ L) (Z : Matrix ι υ L)
    (H : Submodule L (ι → L))
    (hC : ∀ w ∈ H, C.mulVec w ∈ H ⊔ V.mulVecLin.range)
    (hZ : Z.mulVecLin.range ≤ H ⊔ V.mulVecLin.range) :
    ∃ (X : Matrix ι (Fin (Module.finrank L H)) L)
      (M : Matrix (Fin (Module.finrank L H)) (Fin (Module.finrank L H)) L)
      (F : Matrix τ (Fin (Module.finrank L H)) L)
      (L₀ : Matrix (Fin (Module.finrank L H)) υ L) (G : Matrix τ υ L),
      X.mulVecLin.range = H ∧ C * X = X * M + V * F ∧ Z = X * L₀ + V * G := by
  obtain ⟨X, hX⟩ := controlled_subspace_basis_matrix H
  have hc (j : Fin (Module.finrank L H)) : X.col j ∈ H := by
    apply hX.le
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨j, rfl⟩
  have he (j : Fin (Module.finrank L H)) : ∃ m : Fin (Module.finrank L H) → L,
      ∃ f : τ → L, C.mulVec (X.col j) = X.mulVec m + V.mulVec f := by
    obtain ⟨x, hx, y, ⟨f, rfl⟩, hh⟩ := Submodule.mem_sup.mp (hC _ (hc j))
    rw [← hX] at hx
    obtain ⟨m, rfl⟩ := hx
    exact ⟨m, f, hh.symm⟩
  choose m f hmf using he
  have ho (j : υ) : ∃ l : Fin (Module.finrank L H) → L,
      ∃ g : τ → L, Z.col j = X.mulVec l + V.mulVec g := by
    have hzj : Z.col j ∈ Z.mulVecLin.range := by
      rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨x, hx, y, ⟨g, rfl⟩, hh⟩ := Submodule.mem_sup.mp (hZ hzj)
    rw [← hX] at hx
    obtain ⟨l, rfl⟩ := hx
    exact ⟨l, g, hh.symm⟩
  choose l g hlg using ho
  refine ⟨X, (fun i j => m j i), (fun t j => f j t), (fun i j => l j i),
    (fun t j => g j t), hX, ?_, ?_⟩
  · ext i j
    exact congrFun (hmf j) i
  · ext i j
    exact congrFun (hlg j) i

/-- Rational/base-field descent for an arbitrary controlled extension-field
subspace under the actual 2r input-Krylov independence hypothesis. The new
space is contained in the original space after scalar extension, has no larger
dimension, and retains every output column. -/
theorem rational_controlled_subspace_descent {K L ι τ υ : Type*}
    [Field K] [Field L] [Algebra K L]
    [Fintype ι] [DecidableEq ι] [Fintype τ] [Fintype υ]
    (C : Matrix ι ι K) (V : Matrix ι τ K) (Z : Matrix ι υ K)
    (r : ℕ) (H : Submodule L (ι → L))
    (hdim : Module.finrank L H ≤ r)
    (hI : LinearIndependent L (krylovColumns (2 * r)
      (C.map (algebraMap K L)) (V.map (algebraMap K L)).col))
    (hC : ∀ w ∈ H, (C.map (algebraMap K L)).mulVec w ∈
      H ⊔ (V.map (algebraMap K L)).mulVecLin.range)
    (hZ : (Z.map (algebraMap K L)).mulVecLin.range ≤
      H ⊔ (V.map (algebraMap K L)).mulVecLin.range) :
    ∃ S : Submodule K (ι → K),
      Module.finrank K S ≤ Module.finrank L H ∧
      (∀ w ∈ S, (fun i => algebraMap K L (w i)) ∈ H) ∧
      (∀ w ∈ S, C.mulVec w ∈ S ⊔ V.mulVecLin.range) ∧
      Z.mulVecLin.range ≤ S ⊔ V.mulVecLin.range := by
  obtain ⟨X, M, F, L₀, G, hX, hcontrol, hout⟩ := controlled_subspace_realization
    (C.map (algebraMap K L)) (V.map (algebraMap K L)) (Z.map (algebraMap K L)) H hC hZ
  have hi : LinearIndependent L (krylovColumns (2 * Fintype.card (Fin (Module.finrank L H)))
      (C.map (algebraMap K L)) (V.map (algebraMap K L)).col) := by
    rw [Fintype.card_fin]
    exact rational_krylov_independent_mono _ _ (by omega) hI
  exact controlled_realization_base_subspace C V Z X M F L₀ G hcontrol hout hi H hX.le

end AdaptiveOrthogonalRigidity
