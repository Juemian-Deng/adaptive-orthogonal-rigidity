import AdaptiveOrthogonalRigidity.GraphBoundaryDescriptor
import AdaptiveOrthogonalRigidity.BoundaryEnlargement
import AdaptiveOrthogonalRigidity.DescriptorRowTransport
import AdaptiveOrthogonalRigidity.OrdinaryFieldData

/-!
# A descriptor step on the original graph boundary

The enlarged input consists of the actual original graph columns and the constant
column. Every old target column survives; newly exposed target columns agree with
original graph columns by the shared old principal block.
-/

open Matrix
open scoped BigOperators Classical
noncomputable section
namespace AdaptiveOrthogonalRigidity

/-- Delete actual old-bulk rows and retain a regular descriptor for the complete
new original target boundary, with the exact restricted-dynamic-rank bound. -/
theorem graph_boundary_descriptor_step {n k : ℕ} {S : Finset (Fin n)}
    {ω : GraphSample n} {Target : RealMatrix n}
    (D : GraphBoundaryDescriptor S ω Target k)
    (hshared : Target.submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val) =
      (adjacency ω).submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val))
    (T : Finset (↑Sᶜ))
    (hnew : LinearIndependent (ZMod 3)
      ((integerBoundaryInputs (enlargedBoundary S T) ω).map (Int.castRingHom (ZMod 3))).col) :
    ∃ (k' : ℕ) (_ : GraphBoundaryDescriptor (enlargedBoundary S T) ω Target k'),
      k' ≤ (D.dynamic.submatrix (fun i : ↑Tᶜ => i.val) id).rank := by
  let S' := enlargedBoundary S T
  let e := retainedBoundaryEquiv S T
  let A := ordinaryMatrixOver (ZMod 3) (adjacency ω)
  let Z := ordinaryMatrixOver (ZMod 3) Target
  let C := A.submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val)
  let V := augmentedColumnMatrix (A.submatrix (fun i : ↑Sᶜ => i.val) (fun j : S => j.val))
  let Vnew := augmentedColumnMatrix (A.submatrix (fun i : ↑S'ᶜ => i.val) (fun j : S' => j.val))
  let Vbar := Vnew.submatrix e.symm id
  let Zold := Z.submatrix (fun i : ↑Sᶜ => i.val) (fun j : S => j.val)
  have hC : (integerBoundaryBulk S ω).map (Int.castRingHom (ZMod 3)) = C := by
    rw [integerBoundaryBulk_cast, ← ordinaryMatrixOver_adjacency]
  have hV : (integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3)) = V :=
    integerBoundaryInputs_field S ω
  have hVnew : (integerBoundaryInputs S' ω).map (Int.castRingHom (ZMod 3)) = Vnew :=
    integerBoundaryInputs_field S' ω
  have hZ : (integerBoundaryOutputs S Target).map (Int.castRingHom (ZMod 3)) = Zold :=
    integerBoundaryOutputs_field S Target
  have hli : LinearIndependent (ZMod 3) Vbar.col := by
    apply independent_columns_reindex_rows Vnew e.symm
    rwa [hVnew] at hnew
  have hcontains : ∀ j, (V.submatrix (fun i : ↑Tᶜ => i.val) id).col j ∈ Vbar.mulVecLin.range := by
    intro j
    rw [Matrix.range_mulVecLin]
    apply Submodule.subset_span
    cases j with
    | none => exact ⟨none, rfl⟩
    | some j => exact ⟨some ⟨j.val, boundary_subset_enlarged S T j.property⟩, rfl⟩
  have hcross : ∀ j : ↑(Tᶜ)ᶜ,
      (C.submatrix (fun i : ↑Tᶜ => i.val) (fun j : ↑(Tᶜ)ᶜ => j.val)).col j ∈ Vbar.mulVecLin.range := by
    intro j
    rw [Matrix.range_mulVecLin]
    apply Submodule.subset_span
    have hj : j.val ∈ T := by simpa only [compl_compl] using j.property
    exact ⟨some ⟨j.val.val, deleted_mem_enlarged S T ⟨j.val, hj⟩⟩, rfl⟩
  have hact : C * (D.X * D.E + V * D.F) = D.X * D.M + V * D.B := by
    simpa only [hC, hV] using D.action
  have hout : Zold = D.X * D.L + V * D.G := by
    simpa only [hZ, hV] using D.output
  obtain ⟨r, g, Xr, Er, Mr, Fr, Br, Lr, Gr, hr, hir, hreg, hsel, har, hor, hproj⟩ :=
    regular_descriptor_joint_output_one_step C D.X V D.E D.M D.F D.B Zold D.L D.G
      D.regular hact hout Tᶜ Vbar hli hcontains hcross
  let Xnew := Xr.submatrix e id
  let Cret := C.submatrix (fun i : ↑Tᶜ => i.val) (fun j : ↑Tᶜ => j.val)
  let Zret := Zold.submatrix (fun i : ↑Tᶜ => i.val) id
  have hVtransport : Vbar.submatrix e id = Vnew := by
    ext i j
    simp only [Vbar, Matrix.submatrix_apply, id_eq, Equiv.symm_apply_apply]
  have hCtransport : Cret.submatrix e e =
      A.submatrix (fun i : ↑S'ᶜ => i.val) (fun j : ↑S'ᶜ => j.val) := rfl
  have hZtransport : Zret.submatrix e id =
      Z.submatrix (fun i : ↑S'ᶜ => i.val) (fun j : S => j.val) := rfl
  have hnewli : LinearIndependent (ZMod 3) (Matrix.fromCols Xnew Vnew).col := by
    have hh := independent_joint_columns_reindex_rows Xr Vbar e hir
    rwa [hVtransport] at hh
  obtain ⟨hnewact, hnewold⟩ := descriptor_row_transport e Cret Vbar Zret
    Xr Er Mr Fr Br Lr Gr har hor
  rw [hVtransport, hCtransport] at hnewact
  rw [hVtransport, hZtransport] at hnewold
  let W := (Matrix.fromCols Xnew Vnew).mulVecLin.range
  have hinput : Vnew.mulVecLin.range ≤ W := by
    rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change Vnew.col j ∈ (Matrix.fromCols Xnew Vnew).mulVecLin.range
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨Sum.inr j, rfl⟩
  have hold : (Z.submatrix (fun i : ↑S'ᶜ => i.val) (fun j : S => j.val)).mulVecLin.range ≤ W := by
    have hfactor : Z.submatrix (fun i : ↑S'ᶜ => i.val) (fun j : S => j.val) =
        Matrix.fromCols Xnew Vnew * Matrix.fromRows Lr Gr := by
      rw [Matrix.fromCols_mul_fromRows]
      exact hnewold
    rw [hfactor]
    rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨(Matrix.fromRows Lr Gr).col j, rfl⟩
  have hblock : Z.submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val) = C :=
    ordinary_shared_block_field (adjacency ω) Target Sᶜ hshared
  have hall := enlarged_retains_all_target_outputs A Z S S' (boundary_subset_enlarged S T)
    hblock W hinput hold
  have hmem (j : S') :
      (Z.submatrix (fun i : ↑S'ᶜ => i.val) (fun j : S' => j.val)).col j ∈ W := by
    apply hall
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨R, hR⟩ := descriptor_exists_right_factor (Matrix.fromCols Xnew Vnew)
    (Z.submatrix (fun i : ↑S'ᶜ => i.val) (fun j : S' => j.val)) hmem
  let Lnew := R.submatrix Sum.inl id
  let Gnew := R.submatrix Sum.inr id
  have hRsplit : R = Matrix.fromRows Lnew Gnew := by ext i j; cases i <;> rfl
  have hfullout : Z.submatrix (fun i : ↑S'ᶜ => i.val) (fun j : S' => j.val) =
      Xnew * Lnew + Vnew * Gnew := by
    rw [hR, hRsplit, Matrix.fromCols_mul_fromRows]
  refine ⟨r, ⟨Xnew, Er, Mr, Fr, Br, Lnew, Gnew, ?_, hreg, ?_, ?_⟩, ?_⟩
  · rwa [hVnew]
  · rw [hVnew, integerBoundaryBulk_cast, ← ordinaryMatrixOver_adjacency]
    exact hnewact
  · rw [hVnew, integerBoundaryOutputs_field]
    exact hfullout
  · simpa only [GraphBoundaryDescriptor.dynamic, hV] using hr

end AdaptiveOrthogonalRigidity
