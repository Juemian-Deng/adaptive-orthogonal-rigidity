import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Coordinate annihilator duality for rectangular matrices. -/
theorem mem_rectangular_transpose_range_iff {K ι κ : Type*} [Field K]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ K) (x : κ → K) :
    x ∈ A.transpose.mulVecLin.range ↔ ∀ v, A.mulVec v = 0 → x ⬝ᵥ v = 0 := by
  constructor
  · rintro ⟨u, rfl⟩ v hv
    change A.transpose.mulVec u ⬝ᵥ v = 0
    rw [dotProduct_comm, dotProduct_transpose_mulVec, hv, dotProduct_zero]
  · intro h
    have hd : dotProductEquiv K κ x ∈ A.mulVecLin.ker.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro v hv
      exact h v hv
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hd
    obtain ⟨φ, hφ⟩ := hd
    let u := (dotProductEquiv K ι).symm φ
    refine ⟨u, ?_⟩
    apply (dotProductEquiv K κ).injective
    apply LinearMap.ext
    intro v
    have hfun := congrArg (fun ψ : Module.Dual K (κ → K) => ψ v) hφ
    have hu : φ = dotProductEquiv K ι u := (dotProductEquiv K ι).apply_symm_apply φ |>.symm
    rw [hu] at hfun
    change u ⬝ᵥ A.mulVec v = x ⬝ᵥ v at hfun
    change A.transpose.mulVec u ⬝ᵥ v = x ⬝ᵥ v
    rw [dotProduct_comm, dotProduct_transpose_mulVec]
    exact hfun

theorem mem_rectangular_range_iff {K ι κ : Type*} [Field K]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ K) (x : ι → K) :
    x ∈ A.mulVecLin.range ↔ ∀ v, A.transpose.mulVec v = 0 → x ⬝ᵥ v = 0 := by
  simpa only [Matrix.transpose_transpose] using mem_rectangular_transpose_range_iff A.transpose x

end AdaptiveOrthogonalRigidity
