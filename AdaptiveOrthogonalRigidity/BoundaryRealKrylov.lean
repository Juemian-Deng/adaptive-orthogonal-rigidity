import AdaptiveOrthogonalRigidity.BoundaryKrylov
import AdaptiveOrthogonalRigidity.IntegerColumnLift

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

theorem bitValue_intCast {R : Type*} [Ring R] (b : Bool) :
    ((bitValue (R := ℤ) b : ℤ) : R) = bitValue b := by cases b <;> simp [bitValue]

theorem fieldGraphMatrix_intCast {R : Type*} [CommRing R]
    (n : ℕ) (diag : Fin n → ℤ) (ω : GraphSample n) :
    (fieldGraphMatrix ℤ n diag ω).map (Int.castRingHom R) =
      fieldGraphMatrix R n (fun i => (diag i : R)) ω := by
  ext i j
  by_cases hij : i < j
  · simp only [Matrix.map_apply, fieldGraphMatrix_upper n _ ω i j hij]
    exact bitValue_intCast _
  · by_cases hji : j < i
    · rw [Matrix.map_apply, ← (fieldGraphMatrix_isSymm n diag ω).apply i j,
        ← (fieldGraphMatrix_isSymm n (fun i => (diag i : R)) ω).apply i j,
        fieldGraphMatrix_upper n _ ω j i hji, fieldGraphMatrix_upper n _ ω j i hji]
      exact bitValue_intCast _
    · have heq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      subst j
      simp only [Matrix.map_apply, fieldGraphMatrix_diag]
      rfl

noncomputable def boundaryIntegerBulk {n : ℕ} (S : Finset (Fin n)) (ω : GraphSample n) :
    Matrix (Fin (n - S.card)) (Fin (n - S.card)) ℤ :=
  fieldGraphMatrix ℤ (n - S.card) (fun _ => 0) (fun e => ω (boundaryKrylovCoordinates S (Sum.inr e)))

noncomputable def boundaryIntegerInputs {n : ℕ} (S : Finset (Fin n)) (ω : GraphSample n) :
    Option S → Fin (n - S.card) → ℤ :=
  fun j => j.elim (fun _ => 1) (fun k i => bitValue (ω (boundaryKrylovCoordinates S (Sum.inl (i, k)))))

theorem boundaryIntegerInputs_cast {R : Type*} [CommRing R] {n : ℕ}
    (S : Finset (Fin n)) (ω : GraphSample n) :
    (fun j i => (boundaryIntegerInputs S ω j i : R)) =
      fun j : Option S => j.elim (fun _ => (1 : R))
        (fun k => boolVector (fun i => ω (boundaryKrylovCoordinates S (Sum.inl (i, k))))) := by
  funext j i
  cases j with
  | none => simp [boundaryIntegerInputs]
  | some j => exact bitValue_intCast _

theorem boundaryIntegerBulk_real {n : ℕ} (S : Finset (Fin n)) (ω : GraphSample n) :
    (boundaryIntegerBulk S ω).map (Int.castRingHom ℝ) =
      (adjacency ω).submatrix (boundaryBulkEmbedding S) (boundaryBulkEmbedding S) := by
  rw [boundaryIntegerBulk, fieldGraphMatrix_intCast]
  simp only [Int.cast_zero]
  have h := fieldGraphMatrix_induced (K := ℝ) (boundaryBulkEmbedding S) (fun _ => 0) ω
  exact h.trans (congrArg (fun M : RealMatrix n =>
    M.submatrix (boundaryBulkEmbedding S) (boundaryBulkEmbedding S)) (fieldGraphMatrix_real_zero n ω))

theorem boundaryIntegerInputs_real {n : ℕ} (S : Finset (Fin n)) (ω : GraphSample n) :
    (fun j i => (boundaryIntegerInputs S ω j i : ℝ)) =
      fun j : Option S => j.elim (fun _ => (1 : ℝ))
        (fun k i => adjacency ω (boundaryBulkEmbedding S i) k.val) := by
  rw [boundaryIntegerInputs_cast]
  funext j i
  cases j with
  | none => rfl
  | some j =>
    exact (adjacency_edgeOfDistinct ω (boundaryBulkEmbedding S i) j.val (boundaryBulkDisjoint S i j)).symm

/-- Outside the exact F3 boundary failure, the actual real principal/cross
Krylov columns are independent by a nonzero integer minor. -/
theorem boundary_real_krylov_independent {n : ℕ} (S : Finset (Fin n)) (d : ℕ) (ω : GraphSample n)
    (hgood : ω ∉ fixedBoundaryKrylovFailure S d) :
    LinearIndependent ℝ (krylovColumns d
      ((adjacency ω).submatrix (boundaryBulkEmbedding S) (boundaryBulkEmbedding S))
      (fun j : Option S => j.elim (fun _ => (1 : ℝ))
        (fun k i => adjacency ω (boundaryBulkEmbedding S i) k.val))) := by
  have h3 : LinearIndependent (ZMod 3) (krylovColumns d
      ((boundaryIntegerBulk S ω).map (Int.castRingHom (ZMod 3)))
      (fun j i => (boundaryIntegerInputs S ω j i : ZMod 3))) := by
    rw [boundaryIntegerBulk, fieldGraphMatrix_intCast, boundaryIntegerInputs_cast]
    exact Classical.not_not.mp hgood
  have h := integer_krylov_real_independent d (boundaryIntegerBulk S ω) (boundaryIntegerInputs S ω) h3
  rw [boundaryIntegerBulk_real, boundaryIntegerInputs_real] at h
  exact h

end AdaptiveOrthogonalRigidity
