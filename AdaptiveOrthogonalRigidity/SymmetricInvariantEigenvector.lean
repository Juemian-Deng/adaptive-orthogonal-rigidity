import AdaptiveOrthogonalRigidity.HouseholderSameTarget
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Rayleigh

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Every nonzero invariant real subspace of a symmetric matrix contains a
nonzero real eigenvector. The Euclidean-space restriction is explicit. -/
theorem symmetric_invariant_subspace_eigenvector {n : ℕ} (A : RealMatrix n) (hA : A.IsSymm)
    (W : Submodule ℝ (Fin n → ℝ)) (hW : W ≠ ⊥)
    (hinv : ∀ x ∈ W, A.mulVec x ∈ W) :
    ∃ u ∈ W, u ≠ 0 ∧ ∃ μ : ℝ, A.mulVec u = μ • u := by
  let e := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
  let W' : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := W.comap e.toLinearMap
  have hinv' : ∀ x ∈ W', A.toEuclideanLin x ∈ W' := by
    intro x hx
    exact hinv (e x) hx
  have hW' : W' ≠ ⊥ := by
    intro hz
    apply hW
    apply le_antisymm
    · intro x hx
      have hm : e.symm x ∈ W' := by exact hx
      rw [hz] at hm
      have he0 := congrArg e (show e.symm x = 0 from hm)
      change x = 0
      simpa only [e.apply_symm_apply, map_zero] using he0
    · exact bot_le
  let : Nontrivial W' := Submodule.nontrivial_iff_ne_bot.mpr hW'
  have hs : A.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hA)
  have hs' := hs.restrict_invariant hinv'
  obtain ⟨v, hv⟩ := hs'.hasEigenvalue_iSup_of_finiteDimensional.exists_hasEigenvector
  refine ⟨e v.val, v.property, ?_, ?_⟩
  · intro hz
    apply hv.2
    apply Subtype.ext
    apply e.injective
    change e v.val = e (0 : EuclideanSpace ℝ (Fin n))
    rw [map_zero]
    exact hz
  · have hh := congrArg (fun w : W' => e w.val) hv.apply_eq_smul
    exact ⟨_, hh⟩

/-- The terminal same-target witness has no nonzero invariant movement
subspace, not just no eigenvectors. -/
theorem exists_same_target_no_invariant_movement {n : ℕ} (A Q : RealMatrix n)
    (hA : A.IsSymm) (hQ : Orthogonal Q) :
    ∃ Q₀ : RealMatrix n, Orthogonal Q₀ ∧ conjugate A Q₀ = conjugate A Q ∧
      (Q₀ - 1).rank ≤ (Q - 1).rank ∧
      ∀ W : Submodule ℝ (Fin n → ℝ), W ≤ (Q₀ - 1).mulVecLin.range →
        (∀ x ∈ W, A.mulVec x ∈ W) → W = ⊥ := by
  obtain ⟨Q₀, hQ₀, ht, hr, hn⟩ := exists_same_target_no_movement_eigenvector A Q hA hQ
  refine ⟨Q₀, hQ₀, ht, hr, ?_⟩
  intro W hle hinv
  by_contra hW
  obtain ⟨u, huW, hu, μ, heigen⟩ := symmetric_invariant_subspace_eigenvector A hA W hW hinv
  exact hu (hn u (hle huW) μ heigen)

end AdaptiveOrthogonalRigidity
