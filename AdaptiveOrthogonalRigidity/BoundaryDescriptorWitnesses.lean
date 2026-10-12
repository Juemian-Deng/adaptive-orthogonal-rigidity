import AdaptiveOrthogonalRigidity.DescriptorReindex
import AdaptiveOrthogonalRigidity.BoundaryIntegerData

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

theorem integerBoundaryBulk_enumerated {K : Type*} [CommRing K] {n : ℕ}
    (S : Finset (Fin n)) (ω : GraphSample n) :
    ((integerBoundaryBulk S ω).map (Int.castRingHom K)).submatrix
      (boundaryBulkEquiv S) (boundaryBulkEquiv S) =
      fieldGraphMatrix K (n - S.card) (fun _ => 0)
        (fun e => ω (boundaryKrylovCoordinates S (Sum.inr e))) := by
  rw [integerBoundaryBulk_cast]
  exact (fieldGraphMatrix_induced (boundaryBulkEmbedding S) (fun _ => (0 : K)) ω).symm

theorem integerBoundaryInputs_enumerated {K : Type*} [CommRing K] {n : ℕ}
    (S : Finset (Fin n)) (ω : GraphSample n) :
    (fun j i => ((integerBoundaryInputs S ω).map (Int.castRingHom K)) (boundaryBulkEquiv S i) j) =
      (fun j : Option S => j.elim (fun _ => (1 : K))
        (fun s => boolVector (fun i => ω (boundaryKrylovCoordinates S (Sum.inl (i, s)))))) := by
  rw [integerBoundaryInputs_cast]
  funext j
  cases j <;> rfl

theorem integerBoundaryInputs_descriptor {n : ℕ} (S : Finset (Fin n)) (ω : GraphSample n) :
    ((integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3))).submatrix
      (boundaryBulkEquiv S) (descriptorInputEquiv S) =
      descriptorCutInputs (fun q => ω (boundaryKrylovCoordinates S (Sum.inl q))) := by
  ext i j
  change ((integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3)))
    (boundaryBulkEquiv S i) (descriptorInputEquiv S j) = _
  have hh := congrFun (congrFun (integerBoundaryInputs_enumerated (K := ZMod 3) S ω)
    (descriptorInputEquiv S j)) i
  cases he : descriptorInputEquiv S j <;> simpa [descriptorCutInputs, he, boolVector] using hh

/-- The original F3 good event is full independence for the actual integer
principal/input matrices reduced modulo three, on original remaining labels. -/
theorem integer_boundary_mod3_krylov_independent {n : ℕ}
    (S : Finset (Fin n)) (d : ℕ) (ω : GraphSample n)
    (hgood : ω ∉ fixedBoundaryKrylovFailure S d) :
    LinearIndependent (ZMod 3) (krylovColumns d
      ((integerBoundaryBulk S ω).map (Int.castRingHom (ZMod 3)))
      ((integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3))).col) := by
  apply krylov_independent_of_reindex _ _ (boundaryBulkEquiv S) d
  rw [integerBoundaryBulk_enumerated]
  change LinearIndependent (ZMod 3) (krylovColumns d _
    (fun j i => ((integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3)))
      (boundaryBulkEquiv S i) j))
  rw [integerBoundaryInputs_enumerated]
  exact Classical.not_not.mp hgood

/-- A genuine packed descriptor on the original remaining vertices belongs
to the exact event counted in D_n, after bijective row/input enumeration. -/
theorem original_boundary_descriptor_failure_of_packed {n k R : ℕ}
    (S : Finset (Fin n)) (ω : GraphSample n)
    (X : Matrix (↑Sᶜ) (Fin k) (ZMod 3))
    (E M : Matrix (Fin k) (Fin k) (ZMod 3))
    (F B : Matrix (Option S) (Fin k) (ZMod 3))
    (a : Fin k → ZMod 3) (q : Option S → ZMod 3) (z : ↑Sᶜ → Bool)
    (hact : (integerBoundaryBulk S ω).map (Int.castRingHom (ZMod 3)) *
      (X * E + (integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3)) * F) =
      X * M + (integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3)) * B)
    (hpk : DisjointRowBases (fun i =>
      (X * E + (integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3)) * F) i) R)
    (ha : a ≠ 0)
    (hz : boolVector z = X.mulVec a +
      ((integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3))).mulVec q) :
    ω ∈ fixedBoundaryDescriptorFailure S k R := by
  obtain ⟨X', E', M', F', B', a', q', z', hact', hpk', ha', hz'⟩ :=
    packed_descriptor_reindex (boundaryBulkEquiv S) (descriptorInputEquiv S)
      _ _ X E M F B a q z hact hpk ha hz
  rw [integerBoundaryBulk_enumerated, integerBoundaryInputs_descriptor] at hact'
  rw [integerBoundaryInputs_descriptor] at hpk' hz'
  exact ⟨X', E', M', F', B', a', q', z', hact', hpk', ha', hz'⟩

end AdaptiveOrthogonalRigidity
