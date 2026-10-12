import AdaptiveOrthogonalRigidity.LocalizedCrossBlock
import AdaptiveOrthogonalRigidity.CanonicalColumnAlgebra

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

theorem boundary_input_le_augmented {n : ℕ} (A : RealMatrix n) (U : Finset (Fin n)) :
    boundaryInput A U ≤ Submodule.span ℝ (Set.range (augmentedColumns
      (A.submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val)))) := by
  rw [boundaryInput, Matrix.range_mulVecLin]
  apply Submodule.span_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨some j, rfl⟩

/-- The manuscript boundary-localization proposition with precisely V = [1,Y]. -/
theorem boundary_localization_augmented {n r : ℕ}
    (A Q : RealMatrix n) (U : Finset (Fin n))
    (hA : A.IsSymm) (hQ : Orthogonal Q) (hr : (Q - 1).rank ≤ r)
    (hblock : (conjugate A Q).submatrix (fun i : U => i.val) (fun j : U => j.val) =
      A.submatrix (fun i : U => i.val) (fun j : U => j.val))
    (hI : LinearIndependent ℝ (krylovColumns r (A.submatrix Subtype.val Subtype.val)
      (augmentedColumns (A.submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val)))))
    (hZ : boundaryInput (conjugate A Q) U ≤ Submodule.span ℝ (Set.range
      (augmentedColumns (A.submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val))))) :
    ∃ T : Matrix (↑Uᶜ) (↑Uᶜ) ℝ, T.transpose * T = 1 ∧ T * T.transpose = 1 ∧
      conjugate A (boundaryBlockMatrix U T) = conjugate A Q :=
  boundary_localization A Q U _ hA hQ hr hblock hI (boundary_input_le_augmented A U) hZ

theorem CanonicalRealColumn.mem_augmented_span {ι κ : Type*}
    {Y : Matrix ι κ ℝ} {z : ι → ℝ} (hz : CanonicalRealColumn Y z) :
    z ∈ Submodule.span ℝ (Set.range (augmentedColumns Y)) := by
  have h1 : (fun _ => (1 : ℝ)) ∈ Submodule.span ℝ (Set.range (augmentedColumns Y)) :=
    Submodule.subset_span ⟨none, rfl⟩
  have hc (j : κ) : Y.col j ∈ Submodule.span ℝ (Set.range (augmentedColumns Y)) :=
    Submodule.subset_span ⟨some j, rfl⟩
  rcases hz with rfl | rfl | ⟨j, rfl | rfl⟩
  · exact Submodule.zero_mem _
  · exact h1
  · exact hc j
  · exact Submodule.sub_mem _ h1 (hc j)

theorem canonical_boundary_input_le_augmented {n : ℕ} (A B : RealMatrix n)
    (U : Finset (Fin n))
    (hcan : ∀ j : ↑Uᶜ, CanonicalRealColumn
      (A.submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val))
      ((B.submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val)).col j)) :
    boundaryInput B U ≤ Submodule.span ℝ (Set.range (augmentedColumns
      (A.submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val)))) := by
  rw [boundaryInput, Matrix.range_mulVecLin]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact (hcan j).mem_augmented_span

/-- Exact canonical target corollary: an ordinary permutation fixing U
realizes the complete labelled target, including its U-complement block. -/
theorem canonical_columns_determine_target {n r : ℕ}
    (A Q : RealMatrix n) (U : Finset (Fin n))
    (hA : A.IsSymm) (hQ : Orthogonal Q) (hr : (Q - 1).rank ≤ r)
    (hblock : (conjugate A Q).submatrix (fun i : U => i.val) (fun j : U => j.val) =
      A.submatrix (fun i : U => i.val) (fun j : U => j.val))
    (hI : LinearIndependent ℝ (krylovColumns r (A.submatrix Subtype.val Subtype.val)
      (augmentedColumns (A.submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val)))))
    (hcan : ∀ j : ↑Uᶜ, CanonicalRealColumn
      (A.submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val))
      (((conjugate A Q).submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val)).col j)) :
    ∃ σ : Equiv.Perm (Fin n), (∀ i : U, σ i.val = i.val) ∧
      conjugate A Q = conjugate A (permutationMatrix σ) := by
  let Y := A.submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val)
  have hI0 : LinearIndependent ℝ (augmentedColumns Y) :=
    augmented_columns_independent_base _ Y r hI
  obtain ⟨Q₀, hQ₀, ht, _, hrow⟩ := exists_same_target_localized A Q U (augmentedColumns Y)
    hA hQ hr hblock hI (boundary_input_le_augmented A U)
      (canonical_boundary_input_le_augmented A _ U hcan)
  let T := Q₀.submatrix (fun i : ↑Uᶜ => i.val) (fun j : ↑Uᶜ => j.val)
  have hT : T.transpose * T = 1 := (orthogonal_boundary_restriction Q₀ hQ₀ U hrow).1
  have hcross : (conjugate A Q).submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val) = Y * T := by
    rw [← ht]
    exact fixed_rows_conjugate_cross A Q₀ hQ₀ U hrow
  have hcoord (j : ↑Uᶜ) : ∃ k : ↑Uᶜ, T.col j = Pi.single k 1 := by
    apply canonical_column_coefficients Y hI0 (T.col j) (left_orthogonal_columns_nonzero T hT j)
    have hh := hcan j
    rw [hcross] at hh
    exact hh
  have hfull : ∀ j, ∃ i, Q₀.col j = Pi.single i 1 := by
    intro j
    by_cases hj : j ∈ U
    · refine ⟨j, ?_⟩
      ext i
      have hh := orthogonal_fixed_rows_columns Q₀ hQ₀ U hrow ⟨j, hj⟩ i
      simpa [Matrix.col_apply, Matrix.one_apply, Pi.single_apply, eq_comm] using hh
    · obtain ⟨k, hk⟩ := hcoord ⟨j, Finset.mem_compl.mpr hj⟩
      refine ⟨k.val, ?_⟩
      ext i
      by_cases hi : i ∈ U
      · have hij : i ≠ j := fun e => hj (e ▸ hi)
        have hki : k.val ≠ i := fun e => (Finset.mem_compl.mp k.property) (e ▸ hi)
        simpa only [Matrix.col_apply, Pi.single_apply, ite_eq_right hki, ite_eq_right (Ne.symm hki), Matrix.one_apply,
          ite_eq_right hij] using hrow ⟨i, hi⟩ j
      · have hh := congrFun hk ⟨i, Finset.mem_compl.mpr hi⟩
        simpa only [T, Matrix.col_apply, Matrix.submatrix_apply, Pi.single_apply,
          Subtype.ext_iff] using hh
  obtain ⟨σ, hσ⟩ := orthogonal_coordinate_columns_permutation Q₀ hQ₀ hfull
  refine ⟨σ, ?_, ?_⟩
  · intro i
    have hh := hrow i i.val
    rw [hσ] at hh
    by_contra hn
    simp [permutationMatrix, hn] at hh
  · rw [← hσ]
    exact ht.symm

end AdaptiveOrthogonalRigidity
