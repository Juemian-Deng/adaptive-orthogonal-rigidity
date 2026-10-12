import AdaptiveOrthogonalRigidity.FiniteOrbitInvariant

namespace AdaptiveOrthogonalRigidity

/-- The finite commutator argument uses only the actual movement range and
its dimension. No spectral or cyclicity hypothesis is hidden in the statement. -/
theorem commutator_kernel_capture {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T R J D : Module.End K V)
    (hcomm : ∀ v, T (R v) = R (T v) + J (D v))
    (hno : ∀ W : Submodule K V, W ≤ R.range → (∀ v ∈ W, T v ∈ W) → W = ⊥)
    (x : V) (hx : ∀ j < Module.finrank K R.range, D ((T ^ j) x) = 0) : R x = 0 := by
  let d := Module.finrank K R.range
  have horbit : ∀ j ≤ d, (T ^ j) (R x) = R ((T ^ j) x) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [pow_succ', Module.End.mul_apply, ih (by omega), hcomm, hx j (by omega),
        map_zero, add_zero, Module.End.mul_apply]
  by_contra hRx
  obtain ⟨W, hW, hle, hinv⟩ := finite_orbit_invariant_subspace T (R x) hRx R.range d le_rfl
    (fun j hj => by rw [horbit j hj]; exact ⟨_, rfl⟩)
  exact hW (hno W hle hinv)

end AdaptiveOrthogonalRigidity
