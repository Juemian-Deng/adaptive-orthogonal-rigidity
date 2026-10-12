import AdaptiveOrthogonalRigidity.CanonicalColumnAlgebra

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Move a set of actual remaining vertices to the original boundary. -/
def enlargedBoundary {n : ℕ} (S : Finset (Fin n)) (T : Finset (↑Sᶜ)) : Finset (Fin n) :=
  S ∪ T.map ⟨Subtype.val, Subtype.val_injective⟩

theorem boundary_subset_enlarged {n : ℕ} (S : Finset (Fin n)) (T : Finset (↑Sᶜ)) :
    S ⊆ enlargedBoundary S T := Finset.subset_union_left

theorem deleted_mem_enlarged {n : ℕ} (S : Finset (Fin n)) (T : Finset (↑Sᶜ)) (i : T) :
    i.val.val ∈ enlargedBoundary S T :=
  Finset.mem_union_right _ (Finset.mem_map.mpr ⟨i.val, i.property, rfl⟩)

theorem enlarged_boundary_card {n : ℕ} (S : Finset (Fin n)) (T : Finset (↑Sᶜ)) :
    (enlargedBoundary S T).card = S.card + T.card := by
  have hd : Disjoint S (T.map ⟨Subtype.val, Subtype.val_injective⟩) := by
    apply Finset.disjoint_left.mpr
    intro i hi him
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp him
    exact (Finset.mem_compl.mp j.property) hi
  rw [enlargedBoundary, Finset.card_union_of_disjoint hd, Finset.card_map]

/-- Original remaining labels after enlargement are precisely the retained
rows of the old bulk. -/
def retainedBoundaryEquiv {n : ℕ} (S : Finset (Fin n)) (T : Finset (↑Sᶜ)) :
    ↑(enlargedBoundary S T)ᶜ ≃ ↑Tᶜ where
  toFun j := ⟨⟨j.val, Finset.mem_compl.mpr (fun hs =>
    (Finset.mem_compl.mp j.property) (boundary_subset_enlarged S T hs))⟩,
    Finset.mem_compl.mpr (fun ht => (Finset.mem_compl.mp j.property)
      (deleted_mem_enlarged S T ⟨_, ht⟩))⟩
  invFun i := ⟨i.val.val, Finset.mem_compl.mpr (by
    intro hi
    rcases Finset.mem_union.mp hi with hs | ht
    · exact (Finset.mem_compl.mp i.val.property) hs
    · obtain ⟨j, hj, he⟩ := Finset.mem_map.mp ht
      have heq : j = i.val := Subtype.ext he
      exact (Finset.mem_compl.mp i.property) (heq ▸ hj))⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem original_input_column_mem {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (S : Finset (Fin n)) (j : S) :
    (fun i : ↑Sᶜ => A i.val j.val) ∈
      (augmentedColumnMatrix (A.submatrix (fun i : ↑Sᶜ => i.val) (fun j : S => j.val))).mulVecLin.range := by
  rw [Matrix.range_mulVecLin]
  exact Submodule.subset_span ⟨some j, rfl⟩

/-- Every restricted old augmented input remains an actual enlarged input. -/
theorem enlarged_contains_original_inputs {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (S S' : Finset (Fin n)) (hSS : S ⊆ S') :
    (augmentedColumnMatrix (A.submatrix (fun i : ↑S'ᶜ => i.val) (fun j : S => j.val))).mulVecLin.range ≤
    (augmentedColumnMatrix (A.submatrix (fun i : ↑S'ᶜ => i.val) (fun j : S' => j.val))).mulVecLin.range := by
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  cases j with
  | none => exact Submodule.subset_span ⟨none, rfl⟩
  | some j => exact Submodule.subset_span ⟨some ⟨j.val, hSS j.property⟩, rfl⟩

/-- Deleted columns of the original bulk are among the enlarged original inputs. -/
theorem enlarged_contains_deleted_columns {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (S : Finset (Fin n)) (T : Finset (↑Sᶜ)) :
    (A.submatrix (fun i : ↑(enlargedBoundary S T)ᶜ => i.val) (fun j : T => j.val.val)).mulVecLin.range ≤
    (augmentedColumnMatrix (A.submatrix (fun i : ↑(enlargedBoundary S T)ᶜ => i.val)
      (fun j : enlargedBoundary S T => j.val))).mulVecLin.range := by
  rw [Matrix.range_mulVecLin]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact original_input_column_mem A _ ⟨j.val.val, deleted_mem_enlarged S T j⟩

/-- The original shared principal block persists after any boundary enlargement. -/
theorem shared_block_enlarged {K : Type*} {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) (S S' : Finset (Fin n)) (hSS : S ⊆ S')
    (hblock : B.submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val) =
      A.submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val)) :
    B.submatrix (fun i : ↑S'ᶜ => i.val) (fun j : ↑S'ᶜ => j.val) =
      A.submatrix (fun i : ↑S'ᶜ => i.val) (fun j : ↑S'ᶜ => j.val) := by
  ext i j
  have hi : i.val ∈ Sᶜ := Finset.mem_compl.mpr (fun h => (Finset.mem_compl.mp i.property) (hSS h))
  have hj : j.val ∈ Sᶜ := Finset.mem_compl.mpr (fun h => (Finset.mem_compl.mp j.property) (hSS h))
  exact congrFun (congrFun hblock ⟨i.val, hi⟩) ⟨j.val, hj⟩

/-- All newly added target columns are original input columns, so retaining
all old outputs modulo the enlarged inputs retains the entire new boundary. -/
theorem enlarged_retains_all_target_outputs {K : Type*} [Field K] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) (S S' : Finset (Fin n)) (hSS : S ⊆ S')
    (hblock : B.submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val) =
      A.submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val))
    (W : Submodule K (↑S'ᶜ → K))
    (hinput : (augmentedColumnMatrix (A.submatrix
      (fun i : ↑S'ᶜ => i.val) (fun j : S' => j.val))).mulVecLin.range ≤ W)
    (hold : (B.submatrix (fun i : ↑S'ᶜ => i.val) (fun j : S => j.val)).mulVecLin.range ≤ W) :
    (B.submatrix (fun i : ↑S'ᶜ => i.val) (fun j : S' => j.val)).mulVecLin.range ≤ W := by
  rw [Matrix.range_mulVecLin]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  by_cases hj : j.val ∈ S
  · apply hold
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨⟨j.val, hj⟩, rfl⟩
  · have heq : (B.submatrix (fun i : ↑S'ᶜ => i.val) (fun j : S' => j.val)).col j =
        (A.submatrix (fun i : ↑S'ᶜ => i.val) (fun j : S' => j.val)).col j := by
      funext i
      have hi : i.val ∈ Sᶜ := Finset.mem_compl.mpr
        (fun h => (Finset.mem_compl.mp i.property) (hSS h))
      exact congrFun (congrFun hblock ⟨i.val, hi⟩) ⟨j.val, Finset.mem_compl.mpr hj⟩
    rw [heq]
    exact hinput (original_input_column_mem A S' j)

end AdaptiveOrthogonalRigidity
