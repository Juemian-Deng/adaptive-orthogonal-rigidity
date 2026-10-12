import AdaptiveOrthogonalRigidity.BoundaryCubeCanonical

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

noncomputable def integerBoundaryBulk {n : ℕ} (S : Finset (Fin n)) (ω : GraphSample n) :
    Matrix (↑Sᶜ) (↑Sᶜ) ℤ :=
  (fieldGraphMatrix ℤ n (fun _ => 0) ω).submatrix Subtype.val Subtype.val

noncomputable def integerBoundaryInputs {n : ℕ} (S : Finset (Fin n)) (ω : GraphSample n) :
    Matrix (↑Sᶜ) (Option S) ℤ :=
  fun i j => j.elim 1 (fun j => bitValue (boundaryBoolMatrix S ω i j))

noncomputable def integerBoundaryOutputs {n : ℕ} (S : Finset (Fin n)) (B : RealMatrix n) :
    Matrix (↑Sᶜ) S ℤ := fun i j => bitValue (targetBoundaryBits B S j i)

theorem integerBoundaryBulk_cast {K : Type*} [CommRing K] {n : ℕ}
    (S : Finset (Fin n)) (ω : GraphSample n) :
    (integerBoundaryBulk S ω).map (Int.castRingHom K) =
      (fieldGraphMatrix K n (fun _ => 0) ω).submatrix
        (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val) := by
  change ((fieldGraphMatrix ℤ n (fun _ => 0) ω).map (Int.castRingHom K)).submatrix
    (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val) = _
  rw [fieldGraphMatrix_intCast]
  simp only [Int.cast_zero]

theorem integerBoundaryInputs_cast {K : Type*} [CommRing K] {n : ℕ}
    (S : Finset (Fin n)) (ω : GraphSample n) :
    (integerBoundaryInputs S ω).map (Int.castRingHom K) =
      (fun i j => j.elim (1 : K) (fun j => bitValue (boundaryBoolMatrix S ω i j))) := by
  ext i j
  cases j with
  | none => simp [integerBoundaryInputs]
  | some j => exact bitValue_intCast _

theorem integerBoundaryBulk_real {n : ℕ} (S : Finset (Fin n)) (ω : GraphSample n) :
    (integerBoundaryBulk S ω).map (Int.castRingHom ℝ) =
      (adjacency ω).submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val) := by
  rw [integerBoundaryBulk_cast, fieldGraphMatrix_real_zero]

theorem integerBoundaryInputs_real {n : ℕ} (S : Finset (Fin n)) (ω : GraphSample n) :
    (integerBoundaryInputs S ω).map (Int.castRingHom ℝ) = augmentedColumnMatrix
      ((adjacency ω).submatrix (fun i : ↑Sᶜ => i.val) (fun j : S => j.val)) := by
  rw [integerBoundaryInputs_cast]
  have hh := boundary_bool_real S ω
  ext i j
  cases j with
  | none => rfl
  | some j => exact congrFun (congrFun hh i) j

theorem integerBoundaryOutputs_cast {K : Type*} [CommRing K] {n : ℕ}
    (S : Finset (Fin n)) (B : RealMatrix n) :
    (integerBoundaryOutputs S B).map (Int.castRingHom K) =
      (fun i j => bitValue (R := K) (targetBoundaryBits B S j i)) := by
  ext i j
  exact bitValue_intCast _

theorem integerBoundaryOutputs_real {n : ℕ} (S : Finset (Fin n)) (B : RealMatrix n)
    (hB : Ordinary B) :
    (integerBoundaryOutputs S B).map (Int.castRingHom ℝ) =
      B.submatrix (fun i : ↑Sᶜ => i.val) (fun j : S => j.val) := by
  ext i j
  change ((bitValue (R := ℤ) (targetBoundaryBits B S j i) : ℤ) : ℝ) = B i.val j.val
  rw [bitValue_intCast]
  exact congrFun (target_boundary_bits_real B hB S j) i

end AdaptiveOrthogonalRigidity
