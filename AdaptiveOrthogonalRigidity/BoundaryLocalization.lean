import AdaptiveOrthogonalRigidity.ProjectedKrylovCapture

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- The shared principal block and the complete target cross space put every
projected displacement column in the original input span. -/
theorem shared_block_displacement_input {n : ℕ} {τ : Type*}
    (A B : RealMatrix n) (U : Finset (Fin n)) (V : τ → U → ℝ)
    (hblock : B.submatrix (fun i : U => i.val) (fun j : U => j.val) =
      A.submatrix (fun i : U => i.val) (fun j : U => j.val))
    (hY : boundaryInput A U ≤ Submodule.span ℝ (Set.range V))
    (hZ : boundaryInput B U ≤ Submodule.span ℝ (Set.range V)) (x : Fin n → ℝ) :
    coordinateRestriction ℝ U ((B - A).mulVec x) ∈ Submodule.span ℝ (Set.range V) := by
  rw [Matrix.sub_mulVec, map_sub, coordinateRestriction_mulVec,
    coordinateRestriction_mulVec, hblock]
  have h := (Submodule.span ℝ (Set.range V)).sub_mem
    (hZ (show _ ∈ boundaryInput B U from ⟨coordinateRestriction ℝ Uᶜ x, rfl⟩))
    (hY (show _ ∈ boundaryInput A U from ⟨coordinateRestriction ℝ Uᶜ x, rfl⟩))
  simpa only [Matrix.mulVecLin_apply, add_sub_add_left_eq_sub] using h

theorem projected_movement_eq_bot_row {n : ℕ} (Q : RealMatrix n) (U : Finset (Fin n))
    (hH : projectedMovement Q U = ⊥) (i : U) (j : Fin n) : Q i.val j = (1 : RealMatrix n) i.val j := by
  have h : ((Q - 1).submatrix (fun i : U => i.val) id).mulVec (Pi.single j 1) ∈
      projectedMovement Q U := ⟨_, rfl⟩
  rw [hH] at h
  have hz := congrFun (show ((Q - 1).submatrix (fun i : U => i.val) id).mulVec (Pi.single j 1) = 0 from h) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.submatrix_apply, id_eq,
    Matrix.sub_apply, Pi.zero_apply, sub_eq_zero] using hz

/-- Full same-target localization in original coordinates. The witness fixes
all rows in U and retains the whole target, including the boundary block. -/
theorem exists_same_target_localized {n r : ℕ} {τ : Type*} [Fintype τ]
    (A Q : RealMatrix n) (U : Finset (Fin n)) (V : τ → U → ℝ)
    (hA : A.IsSymm) (hQ : Orthogonal Q) (hr : (Q - 1).rank ≤ r)
    (hblock : (conjugate A Q).submatrix (fun i : U => i.val) (fun j : U => j.val) =
      A.submatrix (fun i : U => i.val) (fun j : U => j.val))
    (hI : LinearIndependent ℝ (krylovColumns r (A.submatrix Subtype.val Subtype.val) V))
    (hY : boundaryInput A U ≤ Submodule.span ℝ (Set.range V))
    (hZ : boundaryInput (conjugate A Q) U ≤ Submodule.span ℝ (Set.range V)) :
    ∃ Q₀ : RealMatrix n, Orthogonal Q₀ ∧ conjugate A Q₀ = conjugate A Q ∧
      (Q₀ - 1).rank ≤ (Q - 1).rank ∧
      ∀ (i : U) (j : Fin n), Q₀ i.val j = (1 : RealMatrix n) i.val j := by
  obtain ⟨Q₀, hQ₀, ht, hr₀, _, hcap⟩ := exists_same_target_captured_movement A Q hA hQ
  refine ⟨Q₀, hQ₀, ht, hr₀, ?_⟩
  have hb₀ := hblock
  rw [← ht] at hb₀
  have hD : ∀ x, coordinateRestriction ℝ U ((conjugate A Q₀ - A).mulVec x) ∈
      Submodule.span ℝ (Set.range V) := by
    rw [ht]
    exact shared_block_displacement_input A _ U V hblock hY hZ
  rw [← ht] at hcap
  exact projected_movement_eq_bot_row Q₀ U
    (projected_captured_movement_eq_bot A Q₀ U V hQ₀ (hr₀.trans hr) hb₀ hI hY hD hcap)

end AdaptiveOrthogonalRigidity
