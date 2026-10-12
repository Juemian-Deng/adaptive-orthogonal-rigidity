import AdaptiveOrthogonalRigidity.LinearBasePacking
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Sparse actual determining bases

The low-weight basis lemma is proved by partitioning labelled copies of the
original elements. No greedy-basis theorem or optimization result is assumed.
-/

open scoped BigOperators Classical

noncomputable section
namespace AdaptiveOrthogonalRigidity
namespace FiniteRank

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- Pull back a finite rank along a map, retaining parallel copies as distinct elements. -/
def pullback (r : FiniteRank ι) (f : κ → ι) : FiniteRank κ where
  rank S := r (S.image f)
  empty := by simp
  mono h := r.mono (Finset.image_subset_image h)
  card_le S := (r.card_le _).trans (Finset.card_image_le)
  submod S T := by
    have h := r.submod (S.image f) (T.image f)
    rw [← Finset.image_union] at h
    exact (Nat.add_le_add_left (r.mono (Finset.image_inter_subset _ _ _)) _).trans h

@[simp] theorem pullback_apply (r : FiniteRank ι) (f : κ → ι) (S : Finset κ) :
    r.pullback f S = r (S.image f) := rfl

/-- Parallel copies cannot both occur in an independent part. -/
theorem image_card_eq_of_independent (r : FiniteRank ι) (f : κ → ι) (S : Finset κ)
    (hS : r.pullback f S = S.card) : (S.image f).card = S.card := by
  have h := r.card_le (S.image f)
  change r (S.image f) = S.card at hS
  exact Nat.le_antisymm Finset.card_image_le (hS ▸ h)

end FiniteRank

namespace RankPartition
variable {ι α : Type*} [DecidableEq ι] [Fintype α]
    {r : α → FiniteRank ι} {E : Finset ι}

/-- A partition preserves the total weight, as well as the total cardinality. -/
theorem sum_weight (P : RankPartition r E) (w : ι → ℕ) :
    ∑ a, ∑ i ∈ P.parts a, w i = ∑ i ∈ E, w i := by
  classical
  have hU : Finset.univ.biUnion P.parts = E := by
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨fun ⟨a, ha⟩ => P.subset a ha, P.covers e⟩
  calc
    _ = ∑ i ∈ Finset.univ.biUnion P.parts, w i :=
      (Finset.sum_biUnion (fun a _ b _ hab => P.disjoint hab)).symm
    _ = _ := congrArg (fun S => ∑ i ∈ S, w i) hU

end RankPartition

namespace FiniteRank
variable {ι : Type*} [DecidableEq ι]

/-- In a uniformly dense finite rank, some actual basis has at most its
proportional share of any nonnegative integral weight. -/
theorem exists_low_weight_basis (r : FiniteRank ι) (E : Finset ι)
    (hE : E.Nonempty) (j : ℕ) (hr : r E = j)
    (hdense : ∀ T ⊆ E, j * T.card ≤ E.card * r T) (w : ι → ℕ) :
    ∃ B : Finset ι, B ⊆ E ∧ r B = B.card ∧ B.card = j ∧
      E.card * (∑ i ∈ B, w i) ≤ j * (∑ i ∈ E, w i) := by
  classical
  by_cases hj : j = 0
  · refine ⟨∅, Finset.empty_subset _, by simp, by simp [hj], by simp [hj]⟩
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj
  let C : Finset (ι × Fin j) := E ×ˢ Finset.univ
  let r' : FiniteRank (ι × Fin j) := r.pullback Prod.fst
  have hproj : C.image Prod.fst = E := by
    ext i
    simp only [C, Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true,
      Prod.exists, exists_and_right, exists_eq_right]
    exact ⟨fun ⟨_, hi⟩ => hi, fun hi => ⟨⟨0, hjpos⟩, hi⟩⟩
  have hC : r' C = j := by simp only [r', pullback_apply, hproj, hr]
  have hpart : ∀ S ⊆ C, S.card ≤ ∑ _a : Fin E.card, r' S := by
    intro S hS
    have hs : S.image Prod.fst ⊆ E := by
      intro i hi
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_product.mp (hS hx)).1
    have hsub : S ⊆ S.image Prod.fst ×ˢ (Finset.univ : Finset (Fin j)) := by
      intro x hx
      exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩, Finset.mem_univ _⟩
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hc
    have hd := hdense _ hs
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      r', pullback_apply] using hc.trans (by simpa [Nat.mul_comm] using hd)
  obtain ⟨P⟩ := exists_rankPartition C (fun _ : Fin E.card => r') hpart
  have htight : C.card = ∑ _a : Fin E.card, r' C := by
    simp [C, hC]
  have hcard (a : Fin E.card) : (P.parts a).card = j := by
    rw [← P.independent a, P.rank_eq_on_tight htight a, hC]
  have hw : (∑ a, ∑ x ∈ P.parts a, w x.1) = j * (∑ i ∈ E, w i) := by
    rw [P.sum_weight]
    simp [C, Finset.sum_product, Finset.mul_sum, Nat.mul_comm]
  have hex : ∃ a : Fin E.card,
      E.card * (∑ x ∈ P.parts a, w x.1) ≤ j * (∑ i ∈ E, w i) := by
    by_contra hn
    push Not at hn
    have hlt := Finset.sum_lt_sum_of_nonempty
      (show (Finset.univ : Finset (Fin E.card)).Nonempty from
        ⟨⟨0, Finset.card_pos.mpr hE⟩, Finset.mem_univ _⟩)
      (fun a _ => hn a)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      ← Finset.mul_sum, hw] at hlt
    exact (lt_irrefl _ hlt)
  obtain ⟨a, ha⟩ := hex
  let B := (P.parts a).image Prod.fst
  have hB : B.card = (P.parts a).card :=
    r.image_card_eq_of_independent Prod.fst _ (P.independent a)
  have hinj : Set.InjOn (Prod.fst : ι × Fin j → ι) (↑(P.parts a) : Set (ι × Fin j)) :=
    Finset.card_image_iff.mp hB
  refine ⟨B, ?_, ?_, hB.trans (hcard a), ?_⟩
  · intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_product.mp (P.subset a hx)).1
  · change r ((P.parts a).image Prod.fst) = B.card
    exact (P.independent a).trans hB.symm
  · simpa only [B, Finset.sum_image hinj] using ha

end FiniteRank

section MatrixBases
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- Actual principal restriction, with its original finite set as index type. -/
def principalSubmatrix (M : Matrix ι ι K) (S : Finset ι) : Matrix S S K :=
  M.submatrix Subtype.val Subtype.val

/-- Minimal relative rank supplies both row- and column-density inequalities. -/
def RelativeRankMinimal (M : Matrix ι ι K) : Prop :=
  ∀ T : Finset ι, M.rank * T.card ≤ Fintype.card ι * (principalSubmatrix M T).rank

@[simp] theorem principalSubmatrix_univ_rank (M : Matrix ι ι K) :
    (principalSubmatrix M Finset.univ).rank = M.rank := by
  let e : (Finset.univ : Finset ι) ≃ ι :=
    ⟨Subtype.val, fun i => ⟨i, Finset.mem_univ i⟩, fun _ => rfl, fun _ => rfl⟩
  exact Matrix.rank_submatrix M e e

/-- A nonempty principal submatrix with minimum rank/order exists among the
actual principal restrictions; its relative rank is no greater than the original. -/
theorem exists_relativeRankMinimal [Nonempty ι] (M : Matrix ι ι K) :
    ∃ S : Finset ι, S.Nonempty ∧ RelativeRankMinimal (principalSubmatrix M S) ∧
      ((principalSubmatrix M S).rank : ℝ) / S.card ≤
        (M.rank : ℝ) / Fintype.card ι := by
  let candidates := (Finset.univ : Finset ι).powerset.erase ∅
  have hmem : (Finset.univ : Finset ι) ∈ candidates := by
    simp [candidates, Finset.univ_nonempty.ne_empty]
  obtain ⟨S, hS, hmin⟩ := candidates.exists_min_image
    (fun S => ((principalSubmatrix M S).rank : ℝ) / S.card) ⟨_, hmem⟩
  have hSn : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1
  have hmpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hSn
  refine ⟨S, hSn, ?_, ?_⟩
  · intro T
    let f : S ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
    let U := T.map f
    have hcard : U.card = T.card := Finset.card_map f
    have hrank : (principalSubmatrix M U).rank =
        (principalSubmatrix (principalSubmatrix M S) T).rank := by
      have hh := Matrix.rank_submatrix (principalSubmatrix M U)
        (Finset.equivMap f T) (Finset.equivMap f T)
      exact hh.symm
    by_cases hT : T = ∅
    · simp [hT]
    have hUn : U ≠ ∅ := by simpa [U] using hT
    have hUm : U ∈ candidates := by simp [candidates, hUn]
    have hmin' := hmin U hUm
    rw [hcard, hrank] at hmin'
    have htpos : (0 : ℝ) < T.card := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT)
    have hcross := (div_le_div_iff₀ hmpos htpos).mp hmin'
    simp only [Fintype.card_coe]
    have hcross' : (principalSubmatrix M S).rank * T.card ≤
        (principalSubmatrix (principalSubmatrix M S) T).rank * S.card := by
      exact_mod_cast hcross
    simpa [Nat.mul_comm] using hcross'
  · simpa only [principalSubmatrix_univ_rank, Finset.card_univ] using hmin _ hmem

/-- Row support size; the total support counts matrix positions, not unordered edges. -/
def rowSupportWeight (M : Matrix ι ι K) (i : ι) : ℕ :=
  (Finset.univ.filter (fun j => M i j ≠ 0)).card

def matrixSupportSize (M : Matrix ι ι K) : ℕ := ∑ i, rowSupportWeight M i

/-- A selected family is an actual row basis of the row space, not a change of coordinates. -/
def ActualRowBasis (M : Matrix ι ι K) (I : Finset ι) : Prop :=
  LinearIndependent K (fun i : I => M i) ∧
    Submodule.span K (M.row '' (I : Set ι)) = Submodule.span K (Set.range M.row)

/-- The finite row-rank definition agrees with matrix row restriction rank. -/
theorem rowSetRank_eq_submatrix_rank (M : Matrix ι ι K) (I : Finset ι) :
    rowSetRank (K := K) M.row I = (M.submatrix (fun i : I => i.val) id).rank := by
  rw [Matrix.rank_eq_finrank_span_row]
  unfold rowSetRank
  rw [row_image_eq_range]
  rfl

/-- The copied-element partition theorem yields the manuscript's sparse row basis. -/
theorem exists_sparse_actual_row_basis (M : Matrix ι ι K)
    [Nonempty ι] (hmin : RelativeRankMinimal M) :
    ∃ I : Finset ι, ActualRowBasis M I ∧ I.card = M.rank ∧
      Fintype.card ι * (∑ i ∈ I, rowSupportWeight M i) ≤ M.rank * matrixSupportSize M := by
  have hr : rowFiniteRank (K := K) M.row (Finset.univ : Finset ι) = M.rank := by
    change Module.finrank K (Submodule.span K (M.row '' (↑(Finset.univ : Finset ι) : Set ι))) = _
    rw [Finset.coe_univ, Set.image_univ]
    exact M.rank_eq_finrank_span_row.symm
  have hdense : ∀ (T : Finset ι), T ⊆ Finset.univ →
      M.rank * T.card ≤ (Finset.univ : Finset ι).card * rowFiniteRank (K := K) M.row T := by
    intro T _
    have hle : (principalSubmatrix M T).rank ≤ rowSetRank (K := K) M.row T := by
      rw [rowSetRank_eq_submatrix_rank]
      exact (M.submatrix (fun i : T => i.val) id).rank_submatrix_le id
        (fun i : T => i.val)
    exact (hmin T).trans (by simpa using Nat.mul_le_mul_left (Fintype.card ι) hle)
  obtain ⟨I, hI, hi, hc, hw⟩ := (rowFiniteRank (K := K) M.row).exists_low_weight_basis
    Finset.univ Finset.univ_nonempty M.rank hr hdense (rowSupportWeight M)
  refine ⟨I, ⟨(rowSetRank_eq_card_iff M.row I).mp hi, ?_⟩, hc, ?_⟩
  · apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_mono (Set.image_subset_range _ _)
    · change rowSetRank (K := K) M.row I = _
      rw [show rowSetRank (K := K) M.row I = I.card from hi, hc]
      exact M.rank_eq_finrank_span_row
  · simpa only [Finset.card_univ, matrixSupportSize] using hw

/-- Transposition preserves relative rank minimality. -/
theorem RelativeRankMinimal.transpose {M : Matrix ι ι K}
    (h : RelativeRankMinimal M) : RelativeRankMinimal M.transpose := by
  intro T
  have ht : principalSubmatrix M.transpose T = (principalSubmatrix M T).transpose := rfl
  simpa only [Matrix.rank_transpose, ht] using h T

/-- Transposition preserves support size. -/
theorem matrixSupportSize_transpose (M : Matrix ι ι K) :
    matrixSupportSize M.transpose = matrixSupportSize M := by
  change (∑ i, (Finset.univ.filter (fun j => M.row j i ≠ 0)).card) =
    ∑ i, (Finset.univ.filter (fun j => M.row i j ≠ 0)).card
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun i j : ι => if M.row j i ≠ 0 then (1 : ℕ) else 0)

/-- Each actual row basis touches every nonzero column. -/
theorem ActualRowBasis.touches_column {M : Matrix ι ι K} {I : Finset ι}
    (hI : ActualRowBasis M I) (j : ι) (hcol : ∃ i, M i j ≠ 0) :
    ∃ i ∈ I, M i j ≠ 0 := by
  by_contra hn
  push Not at hn
  obtain ⟨i, hi⟩ := hcol
  have hmem : M i ∈ Submodule.span K (M.row '' (I : Set ι)) := by
    rw [hI.2]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hz : ∀ x ∈ Submodule.span K (M.row '' (I : Set ι)), x j = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact hn i hi
    | zero => rfl
    | add x y hx hy ihx ihy => simp only [Pi.add_apply, ihx, ihy, add_zero]
    | smul a x hx ih => simp only [Pi.smul_apply, ih, smul_zero]
  exact hi (hz _ hmem)

/-- A nonzero diagonal forces every actual row basis to contain at least one
nonzero entry in each original column. -/
theorem ActualRowBasis.support_ge_order {M : Matrix ι ι K} {I : Finset ι}
    (hI : ActualRowBasis M I) (hdiag : ∀ i, M i i ≠ 0) :
    Fintype.card ι ≤ ∑ i ∈ I, rowSupportWeight M i := by
  let supports : ι → Finset ι := fun i => Finset.univ.filter (fun j => M i j ≠ 0)
  have hU : I.biUnion supports = Finset.univ := by
    ext j
    simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
    obtain ⟨i, hi, hij⟩ := hI.touches_column j ⟨j, hdiag j⟩
    exact ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hij⟩⟩
  calc
    _ = (I.biUnion supports).card := by rw [hU, Finset.card_univ]
    _ ≤ ∑ i ∈ I, (supports i).card := Finset.card_biUnion_le
    _ = _ := rfl

/-- The support lower bound needed for cover rectangles. This statement applies
to a minimum-relative-rank matrix; no Frobenius or projector assumption is used. -/
theorem relativeRankMinimal_support_lower [Nonempty ι] {M : Matrix ι ι K}
    (hmin : RelativeRankMinimal M) (hdiag : ∀ i, M i i ≠ 0) :
    Fintype.card ι ^ 2 ≤ M.rank * matrixSupportSize M := by
  obtain ⟨I, hI, _, hw⟩ := exists_sparse_actual_row_basis M hmin
  have hlow := hI.support_ge_order hdiag
  calc
    _ = Fintype.card ι * Fintype.card ι := pow_two _
    _ ≤ Fintype.card ι * ∑ i ∈ I, rowSupportWeight M i := Nat.mul_le_mul_left _ hlow
    _ ≤ _ := hw

/-- Simultaneous sparse determining rows and columns, each using actual indices. -/
theorem exists_sparse_actual_bases [Nonempty ι] (M : Matrix ι ι K)
    (hmin : RelativeRankMinimal M) :
    ∃ I J : Finset ι, ActualRowBasis M I ∧ ActualRowBasis M.transpose J ∧
      I.card = M.rank ∧ J.card = M.rank ∧
      Fintype.card ι * (∑ i ∈ I, rowSupportWeight M i) ≤ M.rank * matrixSupportSize M ∧
      Fintype.card ι * (∑ j ∈ J, rowSupportWeight M.transpose j) ≤ M.rank * matrixSupportSize M := by
  obtain ⟨I, hI, hi, hwI⟩ := exists_sparse_actual_row_basis M hmin
  obtain ⟨J, hJ, hj, hwJ⟩ := exists_sparse_actual_row_basis M.transpose hmin.transpose
  exact ⟨I, J, hI, hJ, hi, by simpa using hj, hwI, by simpa [matrixSupportSize_transpose] using hwJ⟩

/-- Restriction to an actual column basis is injective on the row space. -/
theorem row_span_restriction_injective {M : Matrix ι ι K} {J : Finset ι}
    (hJ : ActualRowBasis M.transpose J) {x : ι → K}
    (hx : x ∈ Submodule.span K (Set.range M.row)) (hz : ∀ j ∈ J, x j = 0) :
    x = 0 := by
  have hx' : x ∈ LinearMap.range M.vecMulLinear := by
    rw [range_vecMulLinear]
    exact hx
  obtain ⟨c, rfl⟩ := hx'
  let L : (ι → K) →ₗ[K] K := dotProductBilin K K c
  have hle : Submodule.span K (M.col '' (J : Set ι)) ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro z ⟨j, hj, rfl⟩
    exact hz j hj
  have hspan : Submodule.span K (M.col '' (J : Set ι)) =
      Submodule.span K (Set.range M.col) := hJ.2
  funext j
  have hj : M.col j ∈ Submodule.span K (M.col '' (J : Set ι)) := by
    rw [hspan]
    exact Submodule.subset_span ⟨j, rfl⟩
  exact hle hj

/-- The arrays on actual spanning rows and columns determine the whole matrix.
No nonsingular principal minor of the original matrix is presumed. -/
theorem actual_bases_determine_matrix {M N : Matrix ι ι K} {I J : Finset ι}
    (hMI : ActualRowBasis M I) (hMJ : ActualRowBasis M.transpose J)
    (hNI : ActualRowBasis N I)
    (hrows : ∀ i ∈ I, ∀ j, M i j = N i j)
    (hcols : ∀ j ∈ J, ∀ i, M i j = N i j) : M = N := by
  have himage : M.row '' (I : Set ι) = N.row '' (I : Set ι) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, funext (fun j => (hrows i hi j).symm)⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, funext (fun j => hrows i hi j)⟩
  have hspan : Submodule.span K (Set.range M.row) =
      Submodule.span K (Set.range N.row) := by rw [← hMI.2, himage, hNI.2]
  ext i j
  have hm : M.row i ∈ Submodule.span K (Set.range M.row) := Submodule.subset_span ⟨i, rfl⟩
  have hn : N.row i ∈ Submodule.span K (Set.range M.row) := by
    rw [hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hz := row_span_restriction_injective hMJ (Submodule.sub_mem _ hm hn)
    (fun k hk => sub_eq_zero.mpr (hcols k hk i))
  exact sub_eq_zero.mp (congrFun hz j)

/-- Matrix support is the number of nonzero labelled positions. -/
theorem matrixSupportSize_eq_card (M : Matrix ι ι K) :
    matrixSupportSize M =
      (Finset.univ.filter (fun q : ι × ι => M q.1 q.2 ≠ 0)).card := by
  unfold matrixSupportSize rowSupportWeight
  rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- At most all square positions can be nonzero. -/
theorem matrixSupportSize_le_square (M : Matrix ι ι K) :
    matrixSupportSize M ≤ Fintype.card ι ^ 2 := by
  rw [matrixSupportSize_eq_card]
  simpa [Fintype.card_prod, pow_two] using
    (Finset.card_le_univ (Finset.univ.filter (fun q : ι × ι => M q.1 q.2 ≠ 0)))

end MatrixBases
end AdaptiveOrthogonalRigidity
