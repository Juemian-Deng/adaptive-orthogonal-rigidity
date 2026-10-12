import AdaptiveOrthogonalRigidity.RegularDescriptor
import AdaptiveOrthogonalRigidity.CoordinatePivots
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Actual column-space coordinates for descriptor reduction

Independent inputs are retained in full and extended only by actual state columns.
All coefficient and left-inverse matrices are constructed over the original field.
-/

open Matrix
open scoped BigOperators Classical
noncomputable section
namespace AdaptiveOrthogonalRigidity

/-- Columnwise membership gives an actual matrix of coefficients. -/
theorem descriptor_exists_right_factor {K ν ι κ : Type*} [Field K] [Fintype ι]
    (A : Matrix ν ι K) (B : Matrix ν κ K)
    (h : ∀ j, B.col j ∈ A.mulVecLin.range) : ∃ F : Matrix ι κ K, B = A * F := by
  choose c hc using h
  refine ⟨fun i j => c j i, ?_⟩
  apply Matrix.ext
  intro i j
  exact (congrFun (hc j) i).symm

/-- Rank factorization over the original coefficient field, using a basis of the actual range. -/
theorem descriptor_rank_factorization {K ν ι : Type*} [Field K] [Fintype ν] [Fintype ι]
    (A : Matrix ν ι K) :
    ∃ (X : Matrix ν (Fin A.rank) K) (Y : Matrix (Fin A.rank) ι K), A = X * Y := by
  let b := Module.finBasis K A.mulVecLin.range
  have hc (j : ι) : A.col j ∈ A.mulVecLin.range := by
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨j, rfl⟩
  let X : Matrix ν (Fin A.rank) K := fun i a => (b a).val i
  let Y : Matrix (Fin A.rank) ι K := fun a j => b.repr ⟨A.col j, hc j⟩ a
  refine ⟨X, Y, ?_⟩
  apply Matrix.ext
  intro i j
  have hh := congrArg (fun x : A.mulVecLin.range => x.val i) (b.sum_repr ⟨A.col j, hc j⟩)
  change A.col j i = ∑ a, (b a).val i * (b.repr ⟨A.col j, hc j⟩) a
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, X, Y, Matrix.mul_apply, mul_comm] using hh.symm

/-- Mapping the field coefficients into another coefficient ring cannot increase matrix rank. -/
theorem descriptor_rank_map_le {K L ν ι : Type*} [Field K] [CommRing L] [StrongRankCondition L]
    [Fintype ν] [Fintype ι] (f : K →+* L) (A : Matrix ν ι K) : (A.map f).rank ≤ A.rank := by
  obtain ⟨X, Y, hXY⟩ := descriptor_rank_factorization A
  have hm := congrArg (fun B : Matrix ν ι K => B.map f) hXY
  rw [Matrix.map_mul] at hm
  rw [hm]
  exact (Matrix.rank_mul_le_left _ _).trans (by simpa using (X.map f).rank_le_card_width)

/-- Extend an independent input column family by actual state columns, retaining
all input columns and spanning the complete original joint column space. -/
theorem descriptor_extend_input_columns {K ν ι π : Type*} [Field K]
    [Fintype ι] [Fintype π] [DecidableEq ι] [DecidableEq π]
    (X : Matrix ν ι K) (V : Matrix ν π K) (hV : LinearIndependent K V.col) :
    ∃ (k' : ℕ) (f : Fin k' ↪ ι),
      LinearIndependent K (Matrix.fromCols (X.submatrix id f) V).col ∧
      Submodule.span K (Set.range (Matrix.fromCols (X.submatrix id f) V).col) =
        Submodule.span K (Set.range (Matrix.fromCols X V).col) := by
  let A := Matrix.fromCols X V
  have h0 : LinearIndepOn K A.col (Set.range (Sum.inr : π → ι ⊕ π)) := by
    apply (linearIndepOn_range_iff Sum.inr_injective A.col).mpr
    exact hV
  obtain ⟨J, _, hJin, hsp, hJ⟩ := exists_linearIndepOn_extension h0 (Set.subset_univ _)
  let S : Finset ι := Finset.univ.filter (fun i => Sum.inl i ∈ J)
  let e : Fin S.card ≃ S := Fintype.equivOfCardEq (by simp)
  let f : Fin S.card ↪ ι := e.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  let g : Fin S.card ⊕ π → J := fun a =>
    match a with
    | Sum.inl i => ⟨Sum.inl (f i), (Finset.mem_filter.mp (e i).property).2⟩
    | Sum.inr i => ⟨Sum.inr i, hJin ⟨i, rfl⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · intro a b h
      have hh := congrArg Subtype.val h
      cases a <;> cases b
      · exact congrArg Sum.inl (f.injective (Sum.inl.inj hh))
      · simp [g] at hh
      · simp [g] at hh
      · exact congrArg Sum.inr (Sum.inr.inj hh)
    · intro a
      rcases a with ⟨a, ha⟩
      cases a with
      | inl i =>
        have hi : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
        obtain ⟨b, hb⟩ := e.surjective ⟨i, hi⟩
        refine ⟨Sum.inl b, Subtype.ext ?_⟩
        exact congrArg Sum.inl (congrArg Subtype.val hb)
      | inr i => exact ⟨Sum.inr i, rfl⟩
  let B := Matrix.fromCols (X.submatrix id f) V
  have hBg : B.col = (fun a : J => A.col a.val) ∘ g := by
    funext a
    cases a <;> rfl
  have hBli : LinearIndependent K B.col := by
    rw [hBg]
    exact hJ.linearIndependent.comp g hg.1
  refine ⟨S.card, f, hBli, ?_⟩
  have hBimage : Set.range B.col = A.col '' J := by
    rw [hBg, Set.range_comp, hg.2.range_eq]
    simp only [Set.image_univ]
    exact (Set.image_eq_range A.col J).symm
  rw [hBimage]
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_subset_range _ _)
  · apply Submodule.span_le.mpr
    simpa only [Set.image_univ] using hsp

/-- An independent finite column matrix has a matrix left inverse. -/
theorem descriptor_matrix_left_inverse {K ν ι : Type*} [Field K]
    [Fintype ν] [Fintype ι] [DecidableEq ν] [DecidableEq ι]
    (A : Matrix ν ι K) (hA : LinearIndependent K A.col) :
    ∃ B : Matrix ι ν K, B * A = 1 := by
  have hinj : Function.Injective A.mulVecLin := Matrix.mulVec_injective_iff.mpr hA
  obtain ⟨L, hL⟩ := A.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  refine ⟨LinearMap.toMatrix' L, ?_⟩
  have hh := congrArg LinearMap.toMatrix' hL
  have hmat : LinearMap.toMatrix' A.mulVecLin = A := LinearMap.toMatrix'.apply_symm_apply A
  simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, hmat] using hh


/-- Choose actual state columns modulo the full independent input family, and
construct coefficient and projection matrices over the original field. -/
theorem descriptor_state_coordinates {K ν ι π : Type*} [Field K]
    [Fintype ν] [Fintype ι] [Fintype π] [DecidableEq ν] [DecidableEq ι] [DecidableEq π]
    (X : Matrix ν ι K) (V : Matrix ν π K) (hV : LinearIndependent K V.col) :
    ∃ (k' : ℕ) (f : Fin k' ↪ ι) (P : Matrix (Fin k') ι K)
      (H : Matrix π ι K) (Q : Matrix (Fin k') ν K),
      LinearIndependent K (Matrix.fromCols (X.submatrix id f) V).col ∧
      X = X.submatrix id f * P + V * H ∧
      Q * X.submatrix id f = 1 ∧ Q * V = 0 ∧ Q * X = P ∧ P.submatrix id f = 1 := by
  obtain ⟨k', f, hli, hspan⟩ := descriptor_extend_input_columns X V hV
  let A := Matrix.fromCols (X.submatrix id f) V
  have hmem (j : ι) : X.col j ∈ A.mulVecLin.range := by
    rw [Matrix.range_mulVecLin, hspan]
    exact Submodule.subset_span ⟨Sum.inl j, rfl⟩
  obtain ⟨R, hR⟩ := descriptor_exists_right_factor A X hmem
  let P := R.submatrix Sum.inl id
  let H := R.submatrix Sum.inr id
  have hRH : R = Matrix.fromRows P H := by
    apply Matrix.ext
    intro i j
    cases i <;> rfl
  have hX : X = X.submatrix id f * P + V * H := by
    calc
      X = A * R := hR
      _ = A * Matrix.fromRows P H := congrArg (fun B => A * B) hRH
      _ = _ := Matrix.fromCols_mul_fromRows (X.submatrix id f) V P H
  obtain ⟨Ainv, hinv⟩ := descriptor_matrix_left_inverse A hli
  let Q := Ainv.submatrix Sum.inl id
  have hQX : Q * X.submatrix id f = 1 := by
    apply Matrix.ext
    intro i j
    have hh := congrFun (congrFun hinv (Sum.inl i)) (Sum.inl j)
    simpa only [A, Q, Matrix.mul_apply, Matrix.submatrix_apply, id_eq,
      Matrix.fromCols_apply_inl, Matrix.one_apply, Sum.inl.injEq] using hh
  have hQV : Q * V = 0 := by
    apply Matrix.ext
    intro i j
    have hh := congrFun (congrFun hinv (Sum.inl i)) (Sum.inr j)
    simpa only [A, Q, Matrix.mul_apply, Matrix.submatrix_apply, id_eq,
      Matrix.fromCols_apply_inr, Matrix.one_apply, Sum.inl_ne_inr, ite_false,
      Matrix.zero_apply] using hh
  have hQP : Q * X = P := by
    rw [hX, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQX, hQV,
      Matrix.one_mul, Matrix.zero_mul, add_zero]
  have hPf : P.submatrix id f = 1 := by
    rw [← hQP, Matrix.submatrix_mul _ _ id id f Function.bijective_id]
    simpa only [Matrix.submatrix_id_id] using hQX
  exact ⟨k', f, P, H, Q, hli, hX, hQX, hQV, hQP, hPf⟩

end AdaptiveOrthogonalRigidity
