import AdaptiveOrthogonalRigidity.BoundaryIntegerData

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- An ordinary real matrix has the same literal zero/one entries over any
coefficient ring; this is an entrywise binary encoding, not a map R→F3. -/
noncomputable def ordinaryMatrixOver (K : Type*) [Zero K] [One K] {n : ℕ}
    (B : RealMatrix n) : Matrix (Fin n) (Fin n) K :=
  fun i j => bitValue (decide (B i j = 1))

theorem ordinaryMatrixOver_real {n : ℕ} (B : RealMatrix n) (hB : Ordinary B) :
    ordinaryMatrixOver ℝ B = B := by
  ext i j
  rcases hB.2.2 i j with h | h <;> simp [ordinaryMatrixOver, h, bitValue]

theorem ordinaryMatrixOver_adjacency {K : Type*} [Zero K] [One K] {n : ℕ}
    (ω : GraphSample n) : ordinaryMatrixOver K (adjacency ω) = fieldGraphMatrix K n (fun _ => 0) ω := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [ordinaryMatrixOver, adjacency_diagonal, fieldGraphMatrix_diag]
    norm_num [bitValue]
  · have hne : i ≠ j := hij
    rw [fieldGraphMatrix_offdiag n (fun _ => (0 : K)) ω i j hne]
    have hr := adjacency_edgeOfDistinct ω i j hne
    rw [ordinaryMatrixOver, hr]
    cases ω (edgeOfDistinct i j hne) <;> norm_num [bitValue, bitReal]

theorem ordinary_shared_block_field {K : Type*} [Zero K] [One K] {n : ℕ}
    (A B : RealMatrix n) (U : Finset (Fin n))
    (h : B.submatrix (fun i : U => i.val) (fun j : U => j.val) =
      A.submatrix (fun i : U => i.val) (fun j : U => j.val)) :
    (ordinaryMatrixOver K B).submatrix (fun i : U => i.val) (fun j : U => j.val) =
      (ordinaryMatrixOver K A).submatrix (fun i : U => i.val) (fun j : U => j.val) := by
  ext i j
  have hh := congrFun (congrFun h i) j
  change B i.val j.val = A i.val j.val at hh
  simp only [Matrix.submatrix_apply, ordinaryMatrixOver, hh]

theorem integerBoundaryOutputs_field {K : Type*} [CommRing K] {n : ℕ}
    (S : Finset (Fin n)) (B : RealMatrix n) :
    (integerBoundaryOutputs S B).map (Int.castRingHom K) =
      (ordinaryMatrixOver K B).submatrix (fun i : ↑Sᶜ => i.val) (fun j : S => j.val) := by
  rw [integerBoundaryOutputs_cast]
  rfl

theorem integerBoundaryInputs_field {K : Type*} [CommRing K] {n : ℕ}
    (S : Finset (Fin n)) (ω : GraphSample n) :
    (integerBoundaryInputs S ω).map (Int.castRingHom K) = augmentedColumnMatrix
      ((ordinaryMatrixOver K (adjacency ω)).submatrix
        (fun i : ↑Sᶜ => i.val) (fun j : S => j.val)) := by
  rw [integerBoundaryInputs_cast, ordinaryMatrixOver_adjacency]
  ext i j
  cases j with
  | none => rfl
  | some j =>
    exact (fieldGraphMatrix_offdiag n (fun _ => (0 : K)) ω i.val j.val
      (boundaryCutDisjoint S i j)).symm

end AdaptiveOrthogonalRigidity
