import AdaptiveOrthogonalRigidity.BoundaryDescriptorGood
import AdaptiveOrthogonalRigidity.RegularDescriptorReduction

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- A regular descriptor for the complete actual target boundary, with the
full original augmented input list and original remaining vertex labels. -/
structure GraphBoundaryDescriptor {n : ℕ} (S : Finset (Fin n)) (ω : GraphSample n)
    (Target : RealMatrix n) (k : ℕ) where
  X : Matrix (↑Sᶜ) (Fin k) (ZMod 3)
  E : Matrix (Fin k) (Fin k) (ZMod 3)
  M : Matrix (Fin k) (Fin k) (ZMod 3)
  F : Matrix (Option S) (Fin k) (ZMod 3)
  B : Matrix (Option S) (Fin k) (ZMod 3)
  L : Matrix (Fin k) S (ZMod 3)
  G : Matrix (Option S) S (ZMod 3)
  independent : LinearIndependent (ZMod 3)
    (Matrix.fromCols X ((integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3)))).col
  regular : regularPencil E M
  action : (integerBoundaryBulk S ω).map (Int.castRingHom (ZMod 3)) *
      (X * E + (integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3)) * F) =
    X * M + (integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3)) * B
  output : (integerBoundaryOutputs S Target).map (Int.castRingHom (ZMod 3)) =
    X * L + (integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3)) * G

noncomputable def GraphBoundaryDescriptor.dynamic {n k : ℕ} {S : Finset (Fin n)}
    {ω : GraphSample n} {Target : RealMatrix n} (D : GraphBoundaryDescriptor S ω Target k) :
    Matrix (↑Sᶜ) (Fin k) (ZMod 3) :=
  D.X * D.E + (integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3)) * D.F

theorem GraphBoundaryDescriptor.dynamic_independent {n k : ℕ} {S : Finset (Fin n)}
    {ω : GraphSample n} {Target : RealMatrix n} (D : GraphBoundaryDescriptor S ω Target k) :
    LinearIndependent (ZMod 3) D.dynamic.col :=
  regular_descriptor_dynamic_independent _ _ _ _ _ _ _ D.independent D.regular D.action

theorem GraphBoundaryDescriptor.dynamic_rank {n k : ℕ} {S : Finset (Fin n)}
    {ω : GraphSample n} {Target : RealMatrix n} (D : GraphBoundaryDescriptor S ω Target k) :
    D.dynamic.rank = k := by
  have h : LinearIndependent (ZMod 3) D.dynamic.transpose.row := D.dynamic_independent
  have hh := h.rank_matrix
  simpa only [Matrix.rank_transpose, Fintype.card_fin] using hh

theorem rowSetRank_eq_restriction_rank {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]
    [DecidableEq ι] (U : Matrix ι κ K) (S : Finset ι) :
    rowSetRank (K := K) U.row S = (U.submatrix (fun i : S => i.val) id).rank := by
  rw [Matrix.rank_eq_finrank_span_row]
  unfold rowSetRank
  rw [row_image_eq_range]
  rfl

/-- The genuine base-packing alternative is now expressed in actual rows of
the original boundary descriptor. -/
theorem GraphBoundaryDescriptor.packing_alternative {n k R : ℕ} {S : Finset (Fin n)}
    {ω : GraphSample n} {Target : RealMatrix n} (D : GraphBoundaryDescriptor S ω Target k)
    (hR : 1 ≤ R) :
    DisjointRowBases D.dynamic R ∨ ∃ T : Finset (↑Sᶜ),
      1 ≤ k - (D.dynamic.submatrix (fun i : ↑Tᶜ => i.val) id).rank ∧
      T.card < R * (k - (D.dynamic.submatrix (fun i : ↑Tᶜ => i.val) id).rank) := by
  have hspan : Submodule.span (ZMod 3) (Set.range D.dynamic.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, Module.finrank_fin_fun, D.dynamic_rank]
  rcases linear_base_packing_alternative D.dynamic hspan hR with hp | ⟨T, hj, ht⟩
  · exact Or.inl hp
  · have he : Finset.univ \ T = Tᶜ := by ext i; simp
    have hrank : rowSetRank (K := ZMod 3) D.dynamic (Finset.univ \ T) =
        (D.dynamic.submatrix (fun i : ↑Tᶜ => i.val) id).rank := by
      rw [he]
      exact rowSetRank_eq_restriction_rank D.dynamic Tᶜ
    rw [hrank] at hj ht
    exact Or.inr ⟨T, hj, ht⟩

/-- A packed node on the global descriptor good event has all target outputs
already in the original input span. -/
theorem GraphBoundaryDescriptor.packed_outputs {n k R : ℕ} {S : Finset (Fin n)}
    {ω : GraphSample n} {Target : RealMatrix n} (D : GraphBoundaryDescriptor S ω Target k)
    (hgood : ω ∉ fixedBoundaryDescriptorFailure S k R) (hpk : DisjointRowBases D.dynamic R) :
    ((integerBoundaryOutputs S Target).map (Int.castRingHom (ZMod 3))).mulVecLin.range ≤
      ((integerBoundaryInputs S ω).map (Int.castRingHom (ZMod 3))).mulVecLin.range :=
  packed_boundary_outputs_in_input_of_good S ω Target hgood
    D.X D.E D.M D.F D.B D.L D.G D.action hpk D.output

end AdaptiveOrthogonalRigidity
