import AdaptiveOrthogonalRigidity.BoundaryLocalization

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- An ordinary block diagonal extension, on the original vertex labels. -/
def boundaryBlockMatrix {n : ℕ} (U : Finset (Fin n)) (T : Matrix (↑Uᶜ) (↑Uᶜ) ℝ) :
    RealMatrix n := fun i j =>
  if hi : i ∈ U then (1 : RealMatrix n) i j
  else if hj : j ∈ U then 0 else T ⟨i, Finset.mem_compl.mpr hi⟩ ⟨j, Finset.mem_compl.mpr hj⟩

theorem orthogonal_fixed_rows_columns {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (U : Finset (Fin n))
    (hrow : ∀ (i : U) (j : Fin n), Q i.val j = (1 : RealMatrix n) i.val j) :
    ∀ (i : U) (j : Fin n), Q j i.val = (1 : RealMatrix n) j i.val := by
  intro i j
  have ht : (Q - 1).transpose.mulVec (Pi.single i.val 1) = 0 := by
    ext k
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.transpose_apply,
      Matrix.sub_apply, hrow i k, sub_self, Pi.zero_apply]
  have hc := (movement_transpose_kernel_iff Q hQ _).mp ht
  have he := congrFun hc j
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.sub_apply,
    Pi.zero_apply, sub_eq_zero] using he

theorem principal_mul_eq_of_left_cross_zero {K ι : Type*} [Semiring K]
    [Fintype ι] [DecidableEq ι] (M N : Matrix ι ι K) (S : Finset ι)
    (hcross : ∀ (i : S) (j : ↑Sᶜ), M i.val j.val = 0) :
    (M * N).submatrix (fun i : S => i.val) (fun j : S => j.val) =
      M.submatrix (fun i : S => i.val) (fun j : S => j.val) *
        N.submatrix (fun i : S => i.val) (fun j : S => j.val) := by
  ext i j
  change (∑ k, M i.val k * N k j.val) = ∑ k : S, M i.val k.val * N k.val j.val
  calc
    _ = ∑ k ∈ S, M i.val k * N k j.val := by
      symm
      apply Finset.sum_subset S.subset_univ
      intro k _ hk
      rw [hcross i ⟨k, Finset.mem_compl.mpr hk⟩, zero_mul]
    _ = _ := by rw [← Finset.sum_attach S]; rfl

theorem orthogonal_boundary_restriction {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (U : Finset (Fin n))
    (hrow : ∀ (i : U) (j : Fin n), Q i.val j = (1 : RealMatrix n) i.val j) :
    let T := Q.submatrix (fun i : ↑Uᶜ => i.val) (fun j : ↑Uᶜ => j.val)
    T.transpose * T = 1 ∧ T * T.transpose = 1 := by
  dsimp only
  have hcol := orthogonal_fixed_rows_columns Q hQ U hrow
  have hleft : ∀ (i : ↑Uᶜ) (j : ↑(Uᶜ)ᶜ), Q.transpose i.val j.val = 0 := by
    intro i j
    have hj : j.val ∈ U := by simpa only [compl_compl] using j.property
    have hij : j.val ≠ i.val := fun e => (Finset.mem_compl.mp i.property) (e ▸ hj)
    simp only [Matrix.transpose_apply, hrow ⟨j.val, hj⟩ i.val, Matrix.one_apply,
      ite_eq_right hij] 
  have hright : ∀ (i : ↑Uᶜ) (j : ↑(Uᶜ)ᶜ), Q i.val j.val = 0 := by
    intro i j
    have hj : j.val ∈ U := by simpa only [compl_compl] using j.property
    have hij : i.val ≠ j.val := fun e => (Finset.mem_compl.mp i.property) (e ▸ hj)
    simp only [hcol ⟨j.val, hj⟩ i.val, Matrix.one_apply, ite_eq_right hij]
  constructor
  · have hh := principal_mul_eq_of_left_cross_zero Q.transpose Q Uᶜ hleft
    rw [hQ.1, Matrix.submatrix_one _ Subtype.val_injective] at hh
    exact hh.symm
  · have hh := principal_mul_eq_of_left_cross_zero Q Q.transpose Uᶜ hright
    rw [hQ.2, Matrix.submatrix_one _ Subtype.val_injective] at hh
    exact hh.symm

theorem fixed_rows_eq_boundaryBlockMatrix {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (U : Finset (Fin n))
    (hrow : ∀ (i : U) (j : Fin n), Q i.val j = (1 : RealMatrix n) i.val j) :
    Q = boundaryBlockMatrix U (Q.submatrix (fun i : ↑Uᶜ => i.val) (fun j : ↑Uᶜ => j.val)) := by
  have hcol := orthogonal_fixed_rows_columns Q hQ U hrow
  ext i j
  by_cases hi : i ∈ U
  · simpa only [boundaryBlockMatrix, dite_eq_left hi] using hrow ⟨i, hi⟩ j
  · by_cases hj : j ∈ U
    · have hij : i ≠ j := fun e => hi (e ▸ hj)
      simpa only [boundaryBlockMatrix, dite_eq_right hi, dite_eq_left hj, Matrix.one_apply,
        ite_eq_right hij] using hcol ⟨j, hj⟩ i
    · simp only [boundaryBlockMatrix, dite_eq_right hi, dite_eq_right hj, Matrix.submatrix_apply]

/-- Boundary localization with an actual orthogonal matrix on U-complement,
and equality of the complete labelled conjugate. -/
theorem boundary_localization {n r : ℕ} {τ : Type*} [Fintype τ]
    (A Q : RealMatrix n) (U : Finset (Fin n)) (V : τ → U → ℝ)
    (hA : A.IsSymm) (hQ : Orthogonal Q) (hr : (Q - 1).rank ≤ r)
    (hblock : (conjugate A Q).submatrix (fun i : U => i.val) (fun j : U => j.val) =
      A.submatrix (fun i : U => i.val) (fun j : U => j.val))
    (hI : LinearIndependent ℝ (krylovColumns r (A.submatrix Subtype.val Subtype.val) V))
    (hY : boundaryInput A U ≤ Submodule.span ℝ (Set.range V))
    (hZ : boundaryInput (conjugate A Q) U ≤ Submodule.span ℝ (Set.range V)) :
    ∃ T : Matrix (↑Uᶜ) (↑Uᶜ) ℝ, T.transpose * T = 1 ∧ T * T.transpose = 1 ∧
      conjugate A (boundaryBlockMatrix U T) = conjugate A Q := by
  obtain ⟨Q₀, hQ₀, ht, _, hrow⟩ := exists_same_target_localized A Q U V hA hQ hr hblock hI hY hZ
  refine ⟨Q₀.submatrix (fun i : ↑Uᶜ => i.val) (fun j : ↑Uᶜ => j.val),
    (orthogonal_boundary_restriction Q₀ hQ₀ U hrow).1,
    (orthogonal_boundary_restriction Q₀ hQ₀ U hrow).2, ?_⟩
  rw [← fixed_rows_eq_boundaryBlockMatrix Q₀ hQ₀ U hrow]
  exact ht

end AdaptiveOrthogonalRigidity
