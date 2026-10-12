import AdaptiveOrthogonalRigidity.RationalControlledSpace
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Order.ModularLattice

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- The actual joint-column matrix has exactly the sum of the two ranges. -/
theorem descriptor_fromCols_range {K ι α β : Type*} [Field K]
    [Fintype α] [Fintype β] (A : Matrix ι α K) (B : Matrix ι β K) :
    (Matrix.fromCols A B).mulVecLin.range = A.mulVecLin.range ⊔ B.mulVecLin.range := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    change (Matrix.fromCols A B).mulVec v ∈ _
    rw [Matrix.fromCols_mulVec]
    exact Submodule.mem_sup.mpr ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, rfl⟩
  · intro w hw
    obtain ⟨x, ⟨u, rfl⟩, y, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hw
    exact ⟨Sum.elim u v, Matrix.fromCols_mulVec_sumElim A B u v⟩

/-- Extend the actual independent input columns to a basis of an ambient
finite state-input space. The additional state dimension is exact. -/
theorem descriptor_complete_input_columns {K ι τ : Type*} [Field K]
    [Fintype ι] [Fintype τ]
    (T : Submodule K (ι → K)) (V : Matrix ι τ K)
    (hV : LinearIndependent K V.col) (hVT : V.mulVecLin.range ≤ T) :
    ∃ (k : ℕ) (X : Matrix ι (Fin k) K),
      k + Fintype.card τ = Module.finrank K T ∧
      LinearIndependent K (Matrix.fromCols X V).col ∧
      (Matrix.fromCols X V).mulVecLin.range = T := by
  obtain ⟨W, hdisj, hsup⟩ := IsModularLattice.exists_disjoint_and_sup_eq hVT
  obtain ⟨X, hX⟩ := controlled_subspace_basis_matrix W
  have hXI : LinearIndependent K X.col := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    change Fintype.card (Fin (Module.finrank K W)) =
      Module.finrank K (Submodule.span K (Set.range X.col))
    rw [← Matrix.range_mulVecLin, hX, Fintype.card_fin]
  have hdimV : Module.finrank K V.mulVecLin.range = Fintype.card τ := by
    rw [Matrix.range_mulVecLin]
    exact finrank_span_eq_card hV
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq V.mulVecLin.range W
  rw [hsup, hdisj.eq_bot, finrank_bot, add_zero, hdimV] at hdim
  refine ⟨Module.finrank K W, X, by omega, ?_, ?_⟩
  · have he : (Matrix.fromCols X V).col = Sum.elim X.col V.col := by
      funext j
      cases j <;> rfl
    rw [he]
    apply hXI.sum_type hV
    rw [← Matrix.range_mulVecLin, ← Matrix.range_mulVecLin, hX]
    exact hdisj.symm
  · rw [descriptor_fromCols_range, hX, sup_comm, hsup]

/-- Every column of a matrix in a joint state/input range has simultaneous
state and input coordinates, including arbitrary output column types. -/
theorem descriptor_joint_column_coordinates {K ι σ τ υ : Type*} [Field K]
    [Fintype σ] [Fintype τ] [Fintype υ] (X : Matrix ι σ K) (V : Matrix ι τ K) (D : Matrix ι υ K)
    (hD : D.mulVecLin.range ≤ (Matrix.fromCols X V).mulVecLin.range) :
    ∃ (E : Matrix σ υ K) (F : Matrix τ υ K), D = X * E + V * F := by
  have he (j : υ) : ∃ u : σ ⊕ τ → K, (Matrix.fromCols X V).mulVec u = D.col j := by
    apply hD
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨j, rfl⟩
  choose u hu using he
  refine ⟨(fun i j => u j (Sum.inl i)), (fun t j => u j (Sum.inr t)), ?_⟩
  ext i j
  have hh := hu j
  rw [Matrix.fromCols_mulVec] at hh
  exact (congrFun hh i).symm

end AdaptiveOrthogonalRigidity
