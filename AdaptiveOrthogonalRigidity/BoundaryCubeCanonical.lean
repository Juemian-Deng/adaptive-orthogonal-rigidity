import AdaptiveOrthogonalRigidity.KrylovReindex

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- The exact binary encoding of a real ordinary target column. -/
noncomputable def targetBoundaryBits {n : ℕ} (B : RealMatrix n) (S : Finset (Fin n)) (j : S) : ↑Sᶜ → Bool :=
  fun i => decide (B i.val j.val = 1)

theorem target_boundary_bits_real {n : ℕ} (B : RealMatrix n) (hB : Ordinary B)
    (S : Finset (Fin n)) (j : S) :
    boolVector (R := ℝ) (targetBoundaryBits B S j) =
      (B.submatrix (fun i : ↑Sᶜ => i.val) (fun j : S => j.val)).col j := by
  ext i
  rcases hB.2.2 i.val j.val with h | h <;>
    simp [boolVector, targetBoundaryBits, Matrix.col_apply, Matrix.submatrix_apply, h, bitValue]

theorem boundary_bool_real {n : ℕ} (S : Finset (Fin n)) (ω : GraphSample n) :
    (fun i j => bitValue (R := ℝ) (boundaryBoolMatrix S ω i j)) =
      (adjacency ω).submatrix (fun i : ↑Sᶜ => i.val) (fun j : S => j.val) := by
  ext i j
  exact (adjacency_edgeOfDistinct ω i.val j.val (boundaryCutDisjoint S i j)).symm

theorem CanonicalBoolColumn.real {ι κ : Type*} {Y : ι → κ → Bool} {z : ι → Bool}
    (hz : CanonicalBoolColumn Y z) :
    CanonicalRealColumn (fun i j => bitValue (R := ℝ) (Y i j)) (boolVector (R := ℝ) z) := by
  rcases hz with rfl | rfl | ⟨j, rfl | rfl⟩
  · exact Or.inl (by ext i; simp [boolVector, bitValue])
  · exact Or.inr (Or.inl (by ext i; simp [boolVector, bitValue]))
  · exact Or.inr (Or.inr ⟨j, Or.inl rfl⟩)
  · exact Or.inr (Or.inr ⟨j, Or.inr (by funext i; exact bitValue_not (Y i j))⟩)

/-- The original affine-cube good event identifies each actual target column
as exactly the same canonical real vector, without a field embedding F3→R. -/
theorem target_boundary_canonical_of_cube_good {n : ℕ} (S : Finset (Fin n))
    (ω : GraphSample n) (B : RealMatrix n) (hB : Ordinary B)
    (hgood : ω ∉ fixedBoundaryCubeFailure S)
    (hspan : ∀ j : S, boolVector (R := ZMod 3) (targetBoundaryBits B S j) ∈
      Set.range (augmentedCubeMatrix (boundaryBoolMatrix S ω)).mulVec) :
    ∀ j : S, CanonicalRealColumn
      ((adjacency ω).submatrix (fun i : ↑Sᶜ => i.val) (fun j : S => j.val))
      ((B.submatrix (fun i : ↑Sᶜ => i.val) (fun j : S => j.val)).col j) := by
  intro j
  have hc : CanonicalBoolColumn (boundaryBoolMatrix S ω) (targetBoundaryBits B S j) := by
    by_contra hn
    exact hgood ⟨_, hspan j, hn⟩
  have hh := hc.real
  rw [boundary_bool_real, target_boundary_bits_real B hB S j] at hh
  exact hh

/-- Final boundary closure: all original target columns lying in the F3 input
span, on the genuine cube and Krylov good events, force ordinary isomorphism. -/
theorem ordinarily_isomorphic_of_boundary_good {n r : ℕ} (S : Finset (Fin n))
    (ω : GraphSample n) (Q B : RealMatrix n)
    (hQ : Orthogonal Q) (hB : Ordinary B) (ht : B = conjugate (adjacency ω) Q)
    (hr : (Q - 1).rank ≤ r)
    (hblock : B.submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val) =
      (adjacency ω).submatrix (fun i : ↑Sᶜ => i.val) (fun j : ↑Sᶜ => j.val))
    (hk : ω ∉ fixedBoundaryKrylovFailure S (2 * r))
    (hc : ω ∉ fixedBoundaryCubeFailure S)
    (hspan : ∀ j : S, boolVector (R := ZMod 3) (targetBoundaryBits B S j) ∈
      Set.range (augmentedCubeMatrix (boundaryBoolMatrix S ω)).mulVec) :
    OrdinarilyIsomorphic (adjacency ω) B := by
  have hi := krylov_independent_mono _ _ (by omega : r ≤ 2 * r)
    (original_boundary_real_krylov_independent S (2 * r) ω hk)
  have hcan := target_boundary_canonical_of_cube_good S ω B hB hc hspan
  rw [ht] at hblock hcan
  generalize hU : Sᶜ = U at hblock hi hcan
  have hS : S = Uᶜ := by rw [← hU, compl_compl]
  subst S
  obtain ⟨σ, _, hσ⟩ := canonical_columns_determine_target (adjacency ω) Q U
    (by ext i j; exact adjacency_symmetric ω j i) hQ hr hblock hi hcan
  exact ⟨σ, ht.trans hσ⟩

end AdaptiveOrthogonalRigidity
