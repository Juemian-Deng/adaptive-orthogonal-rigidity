import AdaptiveOrthogonalRigidity.IntegralDescriptorSpan
import AdaptiveOrthogonalRigidity.IntegralDescriptorComplement

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Every integral vector in a saturated rational space has reduction in the
range of the reduced full lattice basis. -/
theorem descriptor_lattice_vector_reduction {K ι σ : Type*} [Field K]
    [Fintype σ] (T : Submodule ℚ (ι → ℚ))
    (b : Module.Basis σ ℤ (descriptorIntegerLattice T)) (v : ι → ℤ)
    (hv : (fun i => (v i : ℚ)) ∈ T) :
    (fun i => (v i : K)) ∈
      ((descriptorLatticeBasisMatrix b).map (Int.castRingHom K)).mulVecLin.range := by
  let v₀ : descriptorIntegerLattice T := ⟨v, hv⟩
  refine ⟨fun j => ((b.equivFun v₀ j : ℤ) : K), ?_⟩
  funext i
  exact (RingHom.map_mulVec (Int.castRingHom K) (descriptorLatticeBasisMatrix b)
    (b.equivFun v₀) i).symm.trans
      (congrArg (fun z : ι → ℤ => (z i : K)) (descriptor_lattice_basis_coordinates T b v₀))

/-- The simultaneous version preserves every original matrix column. -/
theorem descriptor_lattice_matrix_reduction {K ι σ υ : Type*} [Field K]
    [Fintype σ] [Fintype υ] (T : Submodule ℚ (ι → ℚ))
    (b : Module.Basis σ ℤ (descriptorIntegerLattice T)) (D : Matrix ι υ ℤ)
    (hD : ∀ j, (fun i => (D i j : ℚ)) ∈ T) :
    (D.map (Int.castRingHom K)).mulVecLin.range ≤
      ((descriptorLatticeBasisMatrix b).map (Int.castRingHom K)).mulVecLin.range := by
  rw [Matrix.range_mulVecLin]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact descriptor_lattice_vector_reduction (K := K) T b (D.col j) (hD j)

/-- Construct all modified-descriptor matrices over the reduction field from
an actual rational controlled space. This proves the two full-rank assertions
and retains all outputs; pencil regularity is a separate subsequent theorem.
The input integer lattice is not assumed saturated. -/
theorem integral_controlled_descriptor_data {K ι τ υ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype τ] [Fintype υ]
    (C : Matrix ι ι ℤ) (V : Matrix ι τ ℤ) (Z : Matrix ι υ ℤ)
    (H : Submodule ℚ (ι → ℚ))
    (hC : ∀ w ∈ H, (C.map (Int.castRingHom ℚ)).mulVec w ∈
      H ⊔ (V.map (Int.castRingHom ℚ)).mulVecLin.range)
    (hZ : (Z.map (Int.castRingHom ℚ)).mulVecLin.range ≤
      H ⊔ (V.map (Int.castRingHom ℚ)).mulVecLin.range)
    (hdisj : Disjoint H (V.map (Int.castRingHom ℚ)).mulVecLin.range)
    (hVQ : LinearIndependent ℚ (V.map (Int.castRingHom ℚ)).col)
    (hVK : LinearIndependent K (V.map (Int.castRingHom K)).col) :
    ∃ (k : ℕ) (X : Matrix ι (Fin k) K)
      (E M : Matrix (Fin k) (Fin k) K) (F B : Matrix τ (Fin k) K)
      (L₀ : Matrix (Fin k) υ K) (G : Matrix τ υ K),
      k = Module.finrank ℚ H ∧
      C.map (Int.castRingHom K) * (X * E + V.map (Int.castRingHom K) * F) =
        X * M + V.map (Int.castRingHom K) * B ∧
      Z.map (Int.castRingHom K) = X * L₀ + V.map (Int.castRingHom K) * G ∧
      LinearIndependent K (Matrix.fromCols X (V.map (Int.castRingHom K))).col ∧
      LinearIndependent K (X * E + V.map (Int.castRingHom K) * F).col := by
  let T := H ⊔ (V.map (Int.castRingHom ℚ)).mulVecLin.range
  obtain ⟨n, bH, hn, hUI⟩ := descriptor_integer_basis_exact_rank K H
  obtain ⟨m, bT, hm, hTI⟩ := descriptor_integer_basis_exact_rank K T
  let U := descriptorLatticeBasisMatrix bH
  let A := descriptorLatticeBasisMatrix bT
  have hUmem (j : Fin n) : (fun i => (U i j : ℚ)) ∈ H := (bH j).property
  have hUm : (U.map (Int.castRingHom K)).mulVecLin.range ≤ (A.map (Int.castRingHom K)).mulVecLin.range :=
    descriptor_lattice_matrix_reduction T bT U (fun j => Submodule.mem_sup_left (hUmem j))
  have hVm : (V.map (Int.castRingHom K)).mulVecLin.range ≤ (A.map (Int.castRingHom K)).mulVecLin.range := by
    apply descriptor_lattice_matrix_reduction T bT V
    intro j
    apply Submodule.mem_sup_right
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hCUm : ((C * U).map (Int.castRingHom K)).mulVecLin.range ≤
      (A.map (Int.castRingHom K)).mulVecLin.range := by
    apply descriptor_lattice_matrix_reduction T bT (C * U)
    intro j
    have he : (fun i => ((C * U) i j : ℚ)) =
        (C.map (Int.castRingHom ℚ)).mulVec (fun i => (U i j : ℚ)) := by
      funext i
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
        Int.cast_sum, Int.cast_mul, Int.coe_castRingHom]
    rw [he]
    exact hC _ (hUmem j)
  have hZm : (Z.map (Int.castRingHom K)).mulVecLin.range ≤ (A.map (Int.castRingHom K)).mulVecLin.range := by
    apply descriptor_lattice_matrix_reduction T bT Z
    intro j
    apply hZ
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hdimA : Module.finrank K (A.map (Int.castRingHom K)).mulVecLin.range = m := by
    rw [Matrix.range_mulVecLin]
    simpa only [Fintype.card_fin] using finrank_span_eq_card hTI
  have hdimV : Module.finrank ℚ (V.map (Int.castRingHom ℚ)).mulVecLin.range = Fintype.card τ := by
    rw [Matrix.range_mulVecLin]
    exact finrank_span_eq_card hVQ
  have hdimT : Module.finrank ℚ T = Module.finrank ℚ H + Fintype.card τ := by
    have hh := Submodule.finrank_sup_add_finrank_inf_eq H (V.map (Int.castRingHom ℚ)).mulVecLin.range
    rw [hdisj.eq_bot, finrank_bot, add_zero, hdimV] at hh
    exact hh
  obtain ⟨k, X, hk, hXI, hXA⟩ := descriptor_complete_input_columns
    (A.map (Int.castRingHom K)).mulVecLin.range (V.map (Int.castRingHom K)) hVK hVm
  have hkn : k = n := by rw [hdimA, hm, hdimT, ← hn] at hk; omega
  subst k
  have hUX : (U.map (Int.castRingHom K)).mulVecLin.range ≤
      (Matrix.fromCols X (V.map (Int.castRingHom K))).mulVecLin.range := by rw [hXA]; exact hUm
  have hCUX : (C.map (Int.castRingHom K) * U.map (Int.castRingHom K)).mulVecLin.range ≤
      (Matrix.fromCols X (V.map (Int.castRingHom K))).mulVecLin.range := by
    rw [hXA, ← Matrix.map_mul]
    exact hCUm
  have hZX : (Z.map (Int.castRingHom K)).mulVecLin.range ≤
      (Matrix.fromCols X (V.map (Int.castRingHom K))).mulVecLin.range := by rw [hXA]; exact hZm
  obtain ⟨E, F, hEF⟩ := descriptor_joint_column_coordinates X (V.map (Int.castRingHom K))
    (U.map (Int.castRingHom K)) hUX
  obtain ⟨M, B, hMB⟩ := descriptor_joint_column_coordinates X (V.map (Int.castRingHom K))
    (C.map (Int.castRingHom K) * U.map (Int.castRingHom K)) hCUX
  obtain ⟨L₀, G, hLG⟩ := descriptor_joint_column_coordinates X (V.map (Int.castRingHom K))
    (Z.map (Int.castRingHom K)) hZX
  refine ⟨n, X, E, M, F, B, L₀, G, hn, ?_, hLG, hXI, ?_⟩
  · rwa [← hEF]
  · rw [← hEF]
    exact hUI

end AdaptiveOrthogonalRigidity
