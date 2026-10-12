import AdaptiveOrthogonalRigidity.LocalizedOrthogonal

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- For the actual same-target localized witness the entire cross block is YT. -/
theorem fixed_rows_conjugate_cross {n : ℕ} (A Q : RealMatrix n) (hQ : Orthogonal Q)
    (U : Finset (Fin n))
    (hrow : ∀ (i : U) (j : Fin n), Q i.val j = (1 : RealMatrix n) i.val j) :
    (conjugate A Q).submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val) =
      A.submatrix (fun i : U => i.val) (fun j : ↑Uᶜ => j.val) *
        Q.submatrix (fun i : ↑Uᶜ => i.val) (fun j : ↑Uᶜ => j.val) := by
  have hcol := orthogonal_fixed_rows_columns Q hQ U hrow
  have hleft (i : U) (k : Fin n) : (Q.transpose * A) i.val k = A i.val k := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hcol i, Matrix.one_apply]
    simp
  ext i j
  change (∑ k, (Q.transpose * A) i.val k * Q k j.val) =
    ∑ k : ↑Uᶜ, A i.val k.val * Q k.val j.val
  simp only [hleft]
  calc
    _ = ∑ k ∈ Uᶜ, A i.val k * Q k j.val := by
      symm
      apply Finset.sum_subset (Finset.subset_univ Uᶜ)
      intro k _ hk
      have hkU : k ∈ U := by simpa only [Finset.mem_compl, not_not] using hk
      have hkj : k ≠ j.val := fun e => (Finset.mem_compl.mp j.property) (e ▸ hkU)
      rw [hrow ⟨k, hkU⟩ j.val]
      simp only [Matrix.one_apply, ite_eq_right hkj, mul_zero]
    _ = _ := by rw [← Finset.sum_attach Uᶜ]; rfl

theorem left_orthogonal_columns_nonzero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℝ) (hT : T.transpose * T = 1) (j : ι) : T.col j ≠ 0 := by
  intro hz
  have h : T.transpose.mulVec (T.mulVec (Pi.single j 1)) = Pi.single j 1 := by
    rw [Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]
  rw [Matrix.mulVec_single_one, hz, Matrix.mulVec_zero] at h
  have hh := congrFun h j
  simp at hh

/-- A full orthogonal matrix whose columns are positive coordinate vectors is
an ordinary permutation, with no sign choices or column multiplicities. -/
theorem orthogonal_coordinate_columns_permutation {n : ℕ} (Q : RealMatrix n)
    (hQ : Orthogonal Q) (hcol : ∀ j, ∃ i, Q.col j = Pi.single i 1) :
    ∃ σ : Equiv.Perm (Fin n), Q = permutationMatrix σ := by
  choose f hf using hcol
  have hQi : Function.Injective Q.mulVec := by
    intro x y hxy
    have h := congrArg Q.transpose.mulVec hxy
    simpa only [Matrix.mulVec_mulVec, hQ.1, Matrix.one_mulVec] using h
  have hfi : Function.Injective f := by
    intro i j hij
    have hs : Pi.single i (1 : ℝ) = Pi.single j 1 := hQi (by
      simp only [Matrix.mulVec_single_one, hf, hij])
    by_contra hn
    have hh := congrFun hs i
    simp [Pi.single_apply, hn, Ne.symm hn] at hh
  let e : Equiv.Perm (Fin n) := Equiv.ofBijective f ⟨hfi, (Finite.injective_iff_surjective).mp hfi⟩
  refine ⟨e.symm, ?_⟩
  ext i j
  have hh := congrFun (hf j) i
  change Q i j = _ at hh
  rw [hh]
  simp only [permutationMatrix, Pi.single_apply]
  have he : e.symm i = j ↔ i = f j := by
    rw [Equiv.symm_apply_eq]
    rfl
  simp only [he]

end AdaptiveOrthogonalRigidity
