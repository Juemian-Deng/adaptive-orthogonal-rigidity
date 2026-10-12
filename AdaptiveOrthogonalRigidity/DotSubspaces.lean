import AdaptiveOrthogonalRigidity.RectangularDuality

open Matrix

namespace AdaptiveOrthogonalRigidity

/-- Double annihilator membership for the ordinary coordinate dot product. -/
theorem mem_submodule_iff_dot_annihilator {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (W : Submodule K (ι → K)) (x : ι → K) :
    x ∈ W ↔ ∀ z : ι → K, (∀ w ∈ W, z ⬝ᵥ w = 0) → z ⬝ᵥ x = 0 := by
  constructor
  · intro hx z hz
    exact hz x hx
  · intro h
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := W)]
    apply (Submodule.mem_dualCoannihilator x).mpr
    intro φ hφ
    let z := (dotProductEquiv K ι).symm φ
    have hz : dotProductEquiv K ι z = φ := (dotProductEquiv K ι).apply_symm_apply φ
    have hh := h z (fun w hw => by
      have hzero := (Submodule.mem_dualAnnihilator φ).mp hφ w hw
      rw [← hz] at hzero
      exact hzero)
    rw [← hz]
    exact hh

end AdaptiveOrthogonalRigidity
