import AdaptiveOrthogonalRigidity.BoundaryDescriptorWitnesses

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- On the actual descriptor good event, a packed descriptor has no nonzero
state coefficient for any of the original target's binary boundary columns. -/
theorem packed_boundary_outputs_in_input_of_good {n k R : ℕ}
    (S : Finset (Fin n)) (ω : GraphSample n) (Target : RealMatrix n)
    (hgood : ω ∉ fixedBoundaryDescriptorFailure S k R)
    (X : Matrix (↑Sᶜ) (Fin k) (ZMod 3))
    (E M : Matrix (Fin k) (Fin k) (ZMod 3))
    (F B : Matrix (Option S) (Fin k) (ZMod 3))
    (L : Matrix (Fin k) S (ZMod 3)) (G : Matrix (Option S) S (ZMod 3))
    (hact : (integerBoundaryBulk S ω).map (Int.castRingHom (ZMod 3)) *
      (X * E + (integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3)) * F) =
      X * M + (integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3)) * B)
    (hpk : DisjointRowBases (fun i =>
      (X * E + (integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3)) * F) i) R)
    (hout : (integerBoundaryOutputs S Target).map (Int.castRingHom (ZMod 3)) =
      X * L + (integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3)) * G) :
    ((integerBoundaryOutputs S Target).map (Int.castRingHom (ZMod 3))).mulVecLin.range ≤
      ((integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3))).mulVecLin.range := by
  have hL (j : S) : L.col j = 0 := by
    by_contra ha
    apply hgood
    apply original_boundary_descriptor_failure_of_packed S ω X E M F B
      (L.col j) (G.col j) (targetBoundaryBits Target S j) hact hpk ha
    rw [integerBoundaryOutputs_cast] at hout
    funext i
    exact congrFun (congrFun hout i) j
  rw [Matrix.range_mulVecLin]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  refine ⟨G.col j, ?_⟩
  have heq : ((integerBoundaryOutputs S Target).map (Int.castRingHom (ZMod 3))).col j =
      X.mulVec (L.col j) +
        ((integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3))).mulVec (G.col j) := by
    funext i
    exact congrFun (congrFun hout i) j
  rw [hL j, Matrix.mulVec_zero, zero_add] at heq
  exact heq.symm

/-- Membership of the entire reduced target space gives exactly the input
span premise used by the final original affine-cube closure. -/
theorem boundary_output_range_implies_cube_span {n : ℕ}
    (S : Finset (Fin n)) (ω : GraphSample n) (B : RealMatrix n)
    (hout : ((integerBoundaryOutputs S B).map (Int.castRingHom (ZMod 3))).mulVecLin.range ≤
      ((integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3))).mulVecLin.range) :
    ∀ j : S, boolVector (R := ZMod 3) (targetBoundaryBits B S j) ∈
      Set.range (augmentedCubeMatrix (boundaryBoolMatrix S ω)).mulVec := by
  intro j
  have hz : ((integerBoundaryOutputs S B).map (Int.castRingHom (ZMod 3))).col j ∈
      ((integerBoundaryOutputs S B).map (Int.castRingHom (ZMod 3))).mulVecLin.range := by
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hh := hout hz
  rw [integerBoundaryInputs_cast, integerBoundaryOutputs_cast] at hh
  exact hh

end AdaptiveOrthogonalRigidity
