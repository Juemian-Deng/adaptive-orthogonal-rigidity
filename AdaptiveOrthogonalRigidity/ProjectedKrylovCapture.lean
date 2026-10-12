import AdaptiveOrthogonalRigidity.ProjectedTransport
import AdaptiveOrthogonalRigidity.MovementCapture
import AdaptiveOrthogonalRigidity.KrylovControlledSpace

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

theorem krylov_span_mono {K ι τ : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι K) (V : τ → ι → K) {a b : ℕ} (hab : a ≤ b) :
    Submodule.span K (Set.range (krylovColumns a C V)) ≤
      Submodule.span K (Set.range (krylovColumns b C V)) := by
  apply Submodule.span_mono
  rintro x ⟨ij, rfl⟩
  exact ⟨(⟨ij.1.val, lt_of_lt_of_le ij.1.isLt (Nat.add_le_add_right hab 1)⟩, ij.2), rfl⟩

theorem input_span_le_krylov {K ι τ : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι K) (V : τ → ι → K) (d : ℕ) :
    Submodule.span K (Set.range V) ≤ Submodule.span K (Set.range (krylovColumns d C V)) := by
  apply Submodule.span_mono
  rintro x ⟨t, rfl⟩
  refine ⟨(⟨0, Nat.zero_lt_succ d⟩, t), ?_⟩
  simp only [krylovColumns, pow_zero, Matrix.one_mulVec]

theorem mulVec_mem_krylov_succ {K ι τ : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι K) (V : τ → ι → K) (d : ℕ) (x : ι → K)
    (hx : x ∈ Submodule.span K (Set.range (krylovColumns d C V))) :
    C.mulVec x ∈ Submodule.span K (Set.range (krylovColumns (d + 1) C V)) := by
  have hle : Submodule.span K (Set.range (krylovColumns d C V)) ≤
      (Submodule.span K (Set.range (krylovColumns (d + 1) C V))).comap C.mulVecLin := by
    apply Submodule.span_le.mpr
    rintro _ ⟨ij, rfl⟩
    change C.mulVec (krylovColumns d C V ij) ∈
      Submodule.span K (Set.range (krylovColumns (d + 1) C V))
    apply Submodule.subset_span
    refine ⟨(⟨ij.1.val + 1, by have := ij.1.isLt; omega⟩, ij.2), ?_⟩
    simp only [krylovColumns, pow_succ', ← Matrix.mulVec_mulVec]
  exact hle hx

/-- Projected powers of the original A only introduce actual cross columns
at each step. -/
theorem projected_power_mem_krylov {n : ℕ} {τ : Type*} (A : RealMatrix n)
    (U : Finset (Fin n)) (V : τ → U → ℝ)
    (hY : boundaryInput A U ≤ Submodule.span ℝ (Set.range V))
    (v : Fin n → ℝ) (hv : coordinateRestriction ℝ U v ∈ Submodule.span ℝ (Set.range V))
    (j : ℕ) : coordinateRestriction ℝ U ((A.mulVecLin ^ j) v) ∈
      Submodule.span ℝ (Set.range (krylovColumns j (A.submatrix Subtype.val Subtype.val) V)) := by
  induction j with
  | zero =>
    simpa only [pow_zero, Module.End.one_apply] using (input_span_le_krylov _ V 0 hv)
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    change coordinateRestriction ℝ U (A.mulVec ((A.mulVecLin ^ j) v)) ∈ _
    rw [coordinateRestriction_mulVec]
    apply Submodule.add_mem
    · exact mulVec_mem_krylov_succ _ V j _ ih
    · apply input_span_le_krylov
      apply hY
      exact ⟨_, rfl⟩

theorem projected_displacement_orbit_le_krylov {n : ℕ} {τ : Type*}
    (A D : RealMatrix n) (U : Finset (Fin n)) (V : τ → U → ℝ) (a : ℕ)
    (hY : boundaryInput A U ≤ Submodule.span ℝ (Set.range V))
    (hD : ∀ x, coordinateRestriction ℝ U (D.mulVec x) ∈ Submodule.span ℝ (Set.range V)) :
    displacementOrbitSpan A D a ≤
      (Submodule.span ℝ (Set.range
        (krylovColumns (a - 1) (A.submatrix Subtype.val Subtype.val) V))).comap
          (coordinateRestriction ℝ U) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, hj, x, rfl⟩
  exact krylov_span_mono _ V (by omega : j ≤ a - 1)
    (projected_power_mem_krylov A U V hY (D.mulVec x) (hD x) j)

/-- The actual captured movement has no U projection under exactly the
Krylov window prescribed in boundary localization. -/
theorem projected_captured_movement_eq_bot {n r : ℕ} {τ : Type*} [Fintype τ]
    (A Q : RealMatrix n) (U : Finset (Fin n)) (V : τ → U → ℝ)
    (hQ : Orthogonal Q) (hr : (Q - 1).rank ≤ r)
    (hblock : (conjugate A Q).submatrix (fun i : U => i.val) (fun j : U => j.val) =
      A.submatrix (fun i : U => i.val) (fun j : U => j.val))
    (hI : LinearIndependent ℝ (krylovColumns r (A.submatrix Subtype.val Subtype.val) V))
    (hY : boundaryInput A U ≤ Submodule.span ℝ (Set.range V))
    (hD : ∀ x, coordinateRestriction ℝ U ((conjugate A Q - A).mulVec x) ∈
      Submodule.span ℝ (Set.range V))
    (hcap : (Q - 1).mulVecLin.range ≤
      displacementOrbitSpan A (conjugate A Q - A) (Q - 1).rank) :
    projectedMovement Q U = ⊥ := by
  by_cases ha : (Q - 1).rank = 0
  · have hz : Module.finrank ℝ (projectedMovement Q U) = 0 := by
      have h := projected_movement_rank_le Q U
      omega
    exact Submodule.finrank_eq_zero.mp hz
  · have hwindow : (Q - 1).rank - 1 + 1 ≤ r := by omega
    apply controlled_krylov_space_eq_bot ((Q - 1).rank - 1)
      (A.submatrix Subtype.val Subtype.val) V (projectedMovement Q U)
      (krylov_independent_mono _ V hwindow hI)
    · intro z hz
      apply krylov_span_polynomial_representation
      obtain ⟨x, rfl⟩ := hz
      exact projected_displacement_orbit_le_krylov A _ U V _ hY hD
        (hcap (show (Q - 1).mulVec x ∈ (Q - 1).mulVecLin.range from ⟨x, rfl⟩))
    · intro z hz
      have hs : projectedMovement Q U ⊔ boundaryInput A U ≤
          projectedMovement Q U ⊔ Submodule.span ℝ (Set.range V) := sup_le_sup_left hY _
      exact hs (projected_movement_action A Q hQ U hblock z hz)

end AdaptiveOrthogonalRigidity
