import AdaptiveOrthogonalRigidity.CompatibleCover

open scoped BigOperators Classical
noncomputable section
namespace AdaptiveOrthogonalRigidity

/-- Nonzero real matrices have genuinely positive real-linear rank. -/
theorem cover_matrix_rank_pos {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (hM : M ≠ 0) : 0 < M.rank := by
  by_contra hn
  have hz : M.rank = 0 := by omega
  have hspan : Submodule.span ℝ (Set.range M.row) = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    rw [← M.rank_eq_finrank_span_row]
    exact hz
  apply hM
  apply Matrix.ext
  intro i j
  have hi : M.row i ∈ Submodule.span ℝ (Set.range M.row) := Submodule.subset_span ⟨i, rfl⟩
  rw [hspan] at hi
  exact congrFun hi j

/-- Changing only labels preserves the minimum-relative-rank property. -/
theorem RelativeRankMinimal.reindex {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {M : Matrix ι ι K}
    (hM : RelativeRankMinimal M) (e : κ ≃ ι) :
    RelativeRankMinimal (M.submatrix e e) := by
  intro T
  let U := T.map e.toEmbedding
  have hcard : U.card = T.card := Finset.card_map e.toEmbedding
  have hrank : (principalSubmatrix M U).rank =
      (principalSubmatrix (M.submatrix e e) T).rank := by
    exact (Matrix.rank_submatrix (principalSubmatrix M U)
      (Finset.equivMap e.toEmbedding T) (Finset.equivMap e.toEmbedding T)).symm
  have h := hM U
  rw [hcard, hrank] at h
  rw [Matrix.rank_submatrix, Fintype.card_congr e]
  exact h

/-- Every allowed real ternary matrix is represented by the explicit finite alphabet. -/
theorem exists_coverMatrix_encoding {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : ∀ i j, M i j = -1 ∨ M i j = 0 ∨ M i j = 1) :
    ∃ N : CoverMatrix m, coverMatrixReal N = M := by
  have hh (i j : Fin m) := exists_coverValue (hM i j)
  choose N hN using hh
  exact ⟨N, by funext i j; exact hN i j⟩

/-- Only the inequalities actually needed in the uniform triple union. -/
def CoverTripleAdmissible (n : ℕ) (lam : ℝ) (m j s : ℕ) : Prop :=
  0 < m ∧ m ≤ n ∧ 0 < j ∧ j ≤ n ∧ 0 < s ∧ s ≤ n ^ 2 ∧
    lam * j ≤ m ∧ m ^ 2 ≤ j * s

/-- Finite candidates with actual determining skeletons and prescribed support. -/
abbrev CoverCandidates (m j s : ℕ) :=
  {N : CoverMatrix m // HasSparseCoverSkeleton N j (2 * j * s / m) ∧
    matrixSupportSize (coverMatrixReal N) = s}

/-- Dropping consistency conditions only enlarges the finite skeleton count. -/
theorem coverCandidates_card_le (m j s : ℕ) :
    Fintype.card (CoverCandidates m j s) ≤ m ^ (2 * j) * (1 + 4 * m * j) ^ (2 * j * s / m) := by
  let f : CoverCandidates m j s → {N : CoverMatrix m // HasSparseCoverSkeleton N j (2 * j * s / m)} :=
    fun N => ⟨N.val, N.property.1⟩
  have hf : Function.Injective f := by
    intro N P h
    apply Subtype.ext
    exact congrArg (fun X : {N : CoverMatrix m // HasSparseCoverSkeleton N j (2 * j * s / m)} => X.val) h
  exact (Fintype.card_le_of_injective f hf).trans (sparse_cover_matrix_count m j _)

/-- An actual large support matching supplies one of the counted original-edge
rectangles. Every choice is made inside the event; no deterministic witness is imposed. -/
theorem extract_counted_cover_rectangle {n k : ℕ} {lam : ℝ}
    (hlam : 1 ≤ lam) (D : RealMatrix n) (hD : D ≠ 0)
    (hternary : ∀ i j, D i j = -1 ∨ D i j = 0 ∨ D i j = 1)
    (hk : lam * D.rank ≤ k) (hmatch : HasSupportMatching D k) :
    ∃ m j s, CoverTripleAdmissible n lam m j s ∧
      ∃ (e : CoverEndpoints n m) (N : CoverCandidates m j s),
        ∀ i l, coverValue (N.val i l) = D (e.left i) (e.right l) := by
  have hd : 0 < D.rank := cover_matrix_rank_pos D hD
  have hlam0 : 0 < lam := lt_of_lt_of_le (by norm_num) hlam
  have hkp : 0 < k := by
    have hd' : (0 : ℝ) < D.rank := by exact_mod_cast hd
    have : (0 : ℝ) < k := (mul_pos hlam0 hd').trans_le hk
    exact_mod_cast this
  letI : Nonempty (Fin k) := ⟨⟨0, hkp⟩⟩
  obtain ⟨e, he⟩ := hmatch
  let M : Matrix (Fin k) (Fin k) ℝ := D.submatrix e.left e.right
  have hMrank : M.rank ≤ D.rank := D.rank_submatrix_le e.left e.right
  obtain ⟨S, hS, hmin, hratio⟩ := exists_relativeRankMinimal M
  let m := S.card
  have hm : 0 < m := Finset.card_pos.mpr hS
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  letI : Nonempty S := hS.to_subtype
  let u : Fin m ≃ S := Fintype.equivOfCardEq (by simp [m])
  let v : Fin m ↪ Fin k := u.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  let e' : CoverEndpoints n m :=
    ⟨(fun i => e.left (v i), fun i => e.right (v i)),
      e.left.injective.comp v.injective, e.right.injective.comp v.injective,
      fun i l => e.disjoint (v i) (v l)⟩
  let T := (principalSubmatrix M S).submatrix u u
  have hT : T = D.submatrix e'.left e'.right := rfl
  have hTmin : RelativeRankMinimal T := hmin.reindex u
  have hTdiag : ∀ i, T i i ≠ 0 := fun i => he (v i)
  have hTternary : ∀ i l, T i l = -1 ∨ T i l = 0 ∨ T i l = 1 :=
    fun i l => hternary (e'.left i) (e'.right l)
  obtain ⟨N, hN⟩ := exists_coverMatrix_encoding T hTternary
  let j := T.rank
  let s := matrixSupportSize T
  have hsupp : m ^ 2 ≤ j * s := by
    simpa only [Fintype.card_fin] using relativeRankMinimal_support_lower hTmin hTdiag
  have hj : 0 < j := by
    by_contra hn
    have hz : j = 0 := by omega
    rw [hz, zero_mul] at hsupp
    have : 0 < m ^ 2 := Nat.pow_pos hm
    omega
  have hs : 0 < s := by
    by_contra hn
    have hz : s = 0 := by omega
    rw [hz, mul_zero] at hsupp
    have : 0 < m ^ 2 := Nat.pow_pos hm
    omega
  have hmn : m ≤ n := e'.order_le
  have hjm : j ≤ m := by simpa [j] using T.rank_le_card_width
  have hjn : j ≤ n := hjm.trans hmn
  have hsm : s ≤ m ^ 2 := by simpa only [Fintype.card_fin] using matrixSupportSize_le_square T
  have hsn : s ≤ n ^ 2 := hsm.trans (Nat.pow_le_pow_left hmn 2)
  have hTrank : T.rank = (principalSubmatrix M S).rank := Matrix.rank_submatrix _ u u
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hk' : (0 : ℝ) < k := by exact_mod_cast hkp
  have hd' : (0 : ℝ) < D.rank := by exact_mod_cast hd
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hcross : (j : ℝ) * k ≤ (D.rank : ℝ) * m := by
    have hh : (j : ℝ) / m ≤ (M.rank : ℝ) / k := by
      simpa only [Fintype.card_fin, ← hTrank] using hratio
    have hh' := (div_le_div_iff₀ hm' hk').mp hh
    have hM' : (M.rank : ℝ) ≤ D.rank := by exact_mod_cast hMrank
    exact hh'.trans (mul_le_mul_of_nonneg_right hM' hm'.le)
  have hjratio : lam * j ≤ m := by
    apply (mul_le_mul_iff_left₀ hd').mp
    calc
      lam * j * D.rank = (lam * D.rank) * j := by ring
      _ ≤ (k : ℝ) * j := mul_le_mul_of_nonneg_right hk hj0
      _ ≤ (D.rank : ℝ) * m := by nlinarith
      _ = (m : ℝ) * D.rank := by ring
  have hskel : HasSparseCoverSkeleton N j (2 * j * s / m) := by
    have hh := relativeRankMinimal_has_sparseCoverSkeleton hm N (hN.symm ▸ hTmin)
    simpa only [hN] using hh
  refine ⟨m, j, s, ⟨hm, hmn, hj, hjn, hs, hsn, hjratio, hsupp⟩,
    e', ⟨N, hskel, by rw [hN]⟩, ?_⟩
  intro i l
  exact congrFun (congrFun hN i) l

/-- The bad event is contained in the finite original-edge rectangle union. -/
theorem compatibleCoverBadEvent_subset_rectangles {n : ℕ} {lam : ℝ} (hlam : 1 ≤ lam) :
    compatibleCoverBadEvent n lam ⊆
      {ω | ∃ m j s, CoverTripleAdmissible n lam m j s ∧
        ∃ (e : CoverEndpoints n m) (N : CoverCandidates m j s), ω ∈ coverRectangleEvent e N.val} := by
  rintro ω ⟨D, hD, hcomp, k, hk, hmatch⟩
  obtain ⟨m, j, s, htriple, e, N, hN⟩ :=
    extract_counted_cover_rectangle hlam D hD hcomp.2.2.1 hk hmatch
  refine ⟨m, j, s, htriple, e, N, ?_⟩
  intro i l
  rw [hN]
  exact hcomp.2.2.2.2.2 (e.left i) (e.right l)

end AdaptiveOrthogonalRigidity
