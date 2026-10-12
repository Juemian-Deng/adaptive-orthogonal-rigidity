import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open scoped BigOperators

namespace AdaptiveOrthogonalRigidity

/-- The first k iterates of a vector, with the original operator and vector. -/
def finiteOrbitSpan {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (v : V) (k : ℕ) : Submodule K V :=
  Submodule.span K {w | ∃ j < k, (T ^ j) v = w}

theorem finiteOrbitSpan_mono {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (v : V) {j k : ℕ} (hjk : j ≤ k) :
    finiteOrbitSpan T v j ≤ finiteOrbitSpan T v k := by
  apply Submodule.span_mono
  rintro w ⟨i, hi, rfl⟩
  exact ⟨i, hi.trans_le hjk, rfl⟩

theorem finiteOrbitSpan_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (v : V) (k : ℕ) (E : Submodule K V)
    (h : ∀ j < k, (T ^ j) v ∈ E) : finiteOrbitSpan T v k ≤ E := by
  apply Submodule.span_le.mpr
  rintro w ⟨j, hj, rfl⟩
  exact h j hj

theorem finiteOrbitSpan_stable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (v : V) (j : ℕ)
    (h : finiteOrbitSpan T v j = finiteOrbitSpan T v (j + 1)) :
    ∀ x ∈ finiteOrbitSpan T v j, T x ∈ finiteOrbitSpan T v j := by
  change finiteOrbitSpan T v j ≤ (finiteOrbitSpan T v j).comap T
  apply Submodule.span_le.mpr
  rintro w ⟨i, hi, rfl⟩
  change T ((T ^ i) v) ∈ finiteOrbitSpan T v j
  rw [h]
  apply Submodule.subset_span
  refine ⟨i + 1, by omega, ?_⟩
  rw [pow_succ']
  rfl

/-- A (d+1)-term orbit trapped in a d-dimensional space already contains a
nonzero invariant subspace, if its starting vector is nonzero. -/
theorem finite_orbit_invariant_subspace {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (v : V) (hv : v ≠ 0)
    (E : Submodule K V) (d : ℕ) (hd : Module.finrank K E ≤ d)
    (horbit : ∀ j ≤ d, (T ^ j) v ∈ E) :
    ∃ W : Submodule K V, W ≠ ⊥ ∧ W ≤ E ∧ ∀ x ∈ W, T x ∈ W := by
  have hstab : ∃ j ≤ d, finiteOrbitSpan T v j = finiteOrbitSpan T v (j + 1) := by
    by_contra! hnot
    have hdim : ∀ k ≤ d + 1, k ≤ Module.finrank K (finiteOrbitSpan T v k) := by
      intro k
      induction k with
      | zero => exact fun _ => Nat.zero_le _
      | succ k ih =>
        intro hk
        have hprev := ih (by omega)
        have hlt : finiteOrbitSpan T v k < finiteOrbitSpan T v (k + 1) :=
          lt_of_le_of_ne (finiteOrbitSpan_mono T v (Nat.le_succ k)) (hnot k (by omega))
        have hg := Submodule.finrank_lt_finrank_of_lt hlt
        omega
    have hlower := hdim (d + 1) le_rfl
    have hupper := Submodule.finrank_mono
      (finiteOrbitSpan_le T v (d + 1) E (fun j hj => horbit j (by omega)))
    omega
  obtain ⟨j, hj, hstab⟩ := hstab
  have hjpos : 0 < j := by
    by_contra hz
    have hj0 : j = 0 := by omega
    subst j
    have hv1 : v ∈ finiteOrbitSpan T v 1 := Submodule.subset_span ⟨0, by omega, by simp⟩
    rw [← hstab] at hv1
    have hempty : finiteOrbitSpan T v 0 = ⊥ := by
      simp [finiteOrbitSpan]
    rw [hempty] at hv1
    exact hv hv1
  refine ⟨finiteOrbitSpan T v j, ?_,
    finiteOrbitSpan_le T v j E (fun k hk => horbit k (by omega)),
    finiteOrbitSpan_stable T v j hstab⟩
  intro hz
  have hmem : v ∈ finiteOrbitSpan T v j := Submodule.subset_span ⟨0, hjpos, by simp⟩
  rw [hz] at hmem
  exact hv hmem

end AdaptiveOrthogonalRigidity
