import AdaptiveOrthogonalRigidity.SparseDeterminingBases
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite sparse skeleton counting

All counts are of finite explicit alphabets. The sparse-array bound is obtained
by injecting the signed support into subsets of labelled positions, followed by
a finite binomial-sum estimate.
-/

open scoped BigOperators Classical
noncomputable section
namespace AdaptiveOrthogonalRigidity

/-- Three distinct displacement values, with the empty symbol denoting zero. -/
abbrev CoverSymbol := Option Bool

def coverValue : CoverSymbol → ℝ
  | none => 0
  | some false => -1
  | some true => 1

@[simp] theorem coverValue_eq_zero_iff (a : CoverSymbol) : coverValue a = 0 ↔ a = none := by
  cases a with
  | none => simp [coverValue]
  | some b => cases b <;> norm_num [coverValue]

theorem coverValue_injective : Function.Injective coverValue := by
  intro a b h
  cases a with
  | none => exact ((coverValue_eq_zero_iff b).mp h.symm).symm
  | some a =>
    cases b with
    | none => exact ((coverValue_eq_zero_iff (some a)).mp h)
    | some b => cases a <;> cases b <;> first | rfl | (norm_num [coverValue] at h)

theorem coverValue_ternary (a : CoverSymbol) :
    coverValue a = -1 ∨ coverValue a = 0 ∨ coverValue a = 1 := by
  cases a with
  | none => simp [coverValue]
  | some b => cases b <;> simp [coverValue]

theorem exists_coverValue {x : ℝ} (hx : x = -1 ∨ x = 0 ∨ x = 1) :
    ∃ a : CoverSymbol, coverValue a = x := by
  rcases hx with rfl | rfl | rfl
  · exact ⟨some false, rfl⟩
  · exact ⟨none, rfl⟩
  · exact ⟨some true, rfl⟩

/-- The elementary finite bound underlying the padded sparse-list encoding. -/
theorem sum_choose_le_add_one_pow (N q : ℕ) :
    ∑ k ∈ Finset.range (q + 1), N.choose k ≤ (1 + N) ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ]
    have hp := Nat.pow_le_pow_left (Nat.le_add_left N 1) q
    calc
      _ ≤ (1 + N) ^ q + N ^ (q + 1) := Nat.add_le_add ih (Nat.choose_le_pow N _)
      _ ≤ (1 + N) ^ q + (1 + N) ^ q * N := by
        rw [pow_succ]
        exact Nat.add_le_add_left (Nat.mul_le_mul_right N hp) _
      _ = (1 + N) ^ (q + 1) := by rw [pow_succ, Nat.mul_add, Nat.mul_one]

/-- At most q elements of an N-element alphabet require at most (1+N)^q codes. -/
theorem small_finsets_card_le {ι : Type*} [Fintype ι] (q : ℕ) :
    Fintype.card {S : Finset ι // S.card ≤ q} ≤ (1 + Fintype.card ι) ^ q := by
  classical
  let C : Finset (Finset ι) := Finset.univ.filter (fun S => S.card ≤ q)
  have hsub : C ⊆ (Finset.range (q + 1)).biUnion
      (fun k => (Finset.univ : Finset ι).powersetCard k) := by
    intro S hS
    apply Finset.mem_biUnion.mpr
    exact ⟨S.card, Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hS).2),
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩
  have heq : Fintype.card {S : Finset ι // S.card ≤ q} = C.card := by
    exact Fintype.card_subtype _
  rw [heq]
  calc
    _ ≤ ((Finset.range (q + 1)).biUnion
        (fun k => (Finset.univ : Finset ι).powersetCard k)).card := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range (q + 1), ((Finset.univ : Finset ι).powersetCard k).card :=
      Finset.card_biUnion_le
    _ = ∑ k ∈ Finset.range (q + 1), (Fintype.card ι).choose k := by simp
    _ ≤ _ := sum_choose_le_add_one_pow _ _

/-- The signed support records exactly each occupied position and its sign. -/
def signedCoverSupport {ι : Type*} [Fintype ι] (f : ι → CoverSymbol) : Finset (ι × Bool) :=
  Finset.univ.filter (fun p => f p.1 = some p.2)

theorem signedCoverSupport_injective {ι : Type*} [Fintype ι] :
    Function.Injective (signedCoverSupport (ι := ι)) := by
  classical
  intro f g h
  funext i
  have he (b : Bool) : f i = some b ↔ g i = some b := by
    have hh := congrArg (fun S => (i, b) ∈ S) h
    simpa [signedCoverSupport] using hh
  cases hf : f i with
  | some b => exact (he b).mp hf |>.symm
  | none =>
    cases hg : g i with
    | none => rfl
    | some b => have := (he b).mpr hg; simp [hf] at this

theorem signedCoverSupport_card {ι : Type*} [Fintype ι] (f : ι → CoverSymbol) :
    (signedCoverSupport f).card = (Finset.univ.filter (fun i => f i ≠ none)).card := by
  classical
  unfold signedCoverSupport
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ b : Bool, if f i = some b then (1 : ℕ) else 0) =
    (if f i ≠ none then (1 : ℕ) else 0)
  cases h : f i with
  | none => simp [h]
  | some b => cases b <;> simp [h, Fintype.sum_bool]

abbrev SparseCoverArray (ι : Type*) [Fintype ι] (q : ℕ) :=
  {f : ι → CoverSymbol // (Finset.univ.filter (fun i => f i ≠ none)).card ≤ q}

/-- A ternary array on L labelled slots with at most q nonzeros has at most
(1+2L)^q possibilities. The zero symbol and both signs are counted explicitly. -/
theorem sparseCoverArray_card_le {ι : Type*} [Fintype ι] (q : ℕ) :
    Nat.card (SparseCoverArray ι q) ≤ (1 + 2 * Fintype.card ι) ^ q := by
  classical
  rw [Nat.card_eq_fintype_card]
  let code : SparseCoverArray ι q → {S : Finset (ι × Bool) // S.card ≤ q} :=
    fun f => ⟨signedCoverSupport f.val, by rw [signedCoverSupport_card]; exact f.property⟩
  have hinj : Function.Injective code := by
    intro f g h
    apply Subtype.ext
    exact signedCoverSupport_injective (congrArg Subtype.val h)
  calc
    _ ≤ Fintype.card {S : Finset (ι × Bool) // S.card ≤ q} := Fintype.card_le_of_injective code hinj
    _ ≤ (1 + Fintype.card (ι × Bool)) ^ q := small_finsets_card_le q
    _ = _ := by simp [Nat.mul_comm]


abbrev CoverMatrix (m : ℕ) := Matrix (Fin m) (Fin m) CoverSymbol

def coverMatrixReal {m : ℕ} (N : CoverMatrix m) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => coverValue (N i j)

abbrev CoverSkeletonSlots (m j : ℕ) := (Fin j × Fin m) ⊕ (Fin j × Fin m)

/-- Both row and column arrays, with their overlap deliberately recorded twice. -/
def coverSkeleton {m j : ℕ} (N : CoverMatrix m) (f g : Fin j → Fin m) :
    CoverSkeletonSlots m j → CoverSymbol
  | Sum.inl p => N (f p.1) p.2
  | Sum.inr p => N p.2 (g p.1)

/-- Only consistency and the actual-basis property enter the candidate set. -/
def HasSparseCoverSkeleton {m : ℕ} (N : CoverMatrix m) (j q : ℕ) : Prop :=
  ∃ f g : Fin j → Fin m,
    ActualRowBasis (coverMatrixReal N) (Finset.univ.image f) ∧
    ActualRowBasis (coverMatrixReal N).transpose (Finset.univ.image g) ∧
    (Finset.univ.filter (fun a => coverSkeleton N f g a ≠ none)).card ≤ q

set_option maxHeartbeats 600000 in
/-- Distinct candidate matrices inject into their finite determining skeletons. -/
theorem exists_cover_skeleton_encoding (m j q : ℕ) :
    Nonempty ({N : CoverMatrix m // HasSparseCoverSkeleton N j q} ↪
      ((Fin j → Fin m) × (Fin j → Fin m)) × SparseCoverArray (CoverSkeletonSlots m j) q) := by
  let C := {N : CoverMatrix m // HasSparseCoverSkeleton N j q}
  have hchoose (N : C) := N.property
  choose f g hfg using hchoose
  let code : C → ((Fin j → Fin m) × (Fin j → Fin m)) × SparseCoverArray (CoverSkeletonSlots m j) q :=
    fun N => ((f N, g N), ⟨coverSkeleton N.val (f N) (g N), (hfg N).2.2⟩)
  have hinj : Function.Injective code := by
    intro N P h
    have hf : f N = f P := congrArg (fun z => z.1.1) h
    have hg : g N = g P := congrArg (fun z => z.1.2) h
    have ha : coverSkeleton N.val (f N) (g N) = coverSkeleton P.val (f P) (g P) :=
      congrArg (fun z => z.2.val) h
    have hreal : coverMatrixReal N.val = coverMatrixReal P.val := by
      apply actual_bases_determine_matrix (hfg N).1 (hfg N).2.1
        (by simpa only [hf] using (hfg P).1)
      · intro i hi k
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
        have hh := congrFun ha (Sum.inl (a, k))
        simpa only [coverMatrixReal, coverSkeleton, hf] using congrArg coverValue hh
      · intro k hk i
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hk
        have hh := congrFun ha (Sum.inr (a, i))
        simpa only [coverMatrixReal, coverSkeleton, hg] using congrArg coverValue hh
    apply Subtype.ext
    apply Matrix.ext
    intro i k
    exact coverValue_injective (congrFun (congrFun hreal i) k)
  exact ⟨⟨code, hinj⟩⟩

/-- A sparse, determining skeleton has exactly the advertised finite count. -/
theorem sparse_cover_matrix_count (m j q : ℕ) :
    Fintype.card {N : CoverMatrix m // HasSparseCoverSkeleton N j q} ≤
      m ^ (2 * j) * (1 + 4 * m * j) ^ q := by
  obtain ⟨code⟩ := exists_cover_skeleton_encoding m j q
  calc
    _ ≤ Fintype.card (((Fin j → Fin m) × (Fin j → Fin m)) ×
        SparseCoverArray (CoverSkeletonSlots m j) q) := Fintype.card_le_of_injective code code.injective
    _ = (m ^ j * m ^ j) * Nat.card (SparseCoverArray (CoverSkeletonSlots m j) q) := by
      rw [Nat.card_eq_fintype_card]
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    _ ≤ (m ^ j * m ^ j) * (1 + 2 * Fintype.card (CoverSkeletonSlots m j)) ^ q :=
      Nat.mul_le_mul_left (m ^ j * m ^ j) (sparseCoverArray_card_le (ι := CoverSkeletonSlots m j) q)
    _ = _ := by
      simp only [CoverSkeletonSlots, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
        ← pow_add, ← two_mul]
      congr 2
      ring

/-- Enumerate an actual finite basis without changing any of its vectors. -/
theorem exists_enumeration_of_card {ι : Type*} [DecidableEq ι] (I : Finset ι)
    {j : ℕ} (hcard : I.card = j) :
    ∃ f : Fin j → ι, Function.Injective f ∧ Finset.univ.image f = I ∧
      ∀ w : ι → ℕ, (∑ a, w (f a)) = ∑ i ∈ I, w i := by
  let e : Fin j ≃ I := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let f : Fin j → ι := fun a => (e a).val
  refine ⟨f, Subtype.val_injective.comp e.injective, ?_, ?_⟩
  · ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      exact (e a).property
    · intro hi
      obtain ⟨a, ha⟩ := e.surjective ⟨i, hi⟩
      exact ⟨a, congrArg Subtype.val ha⟩
  · intro w
    calc
      _ = ∑ i : I, w i.val := Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = _ := (Finset.sum_subtype I (fun _ => Iff.rfl) w).symm

theorem coverSymbol_support_indicator (a : CoverSymbol) :
    (if a ≠ none then (1 : ℕ) else 0) = (if coverValue a ≠ 0 then (1 : ℕ) else 0) := by
  cases a with
  | none => norm_num [coverValue]
  | some b => cases b <;> norm_num [coverValue]

/-- The support weight of the two arrays is the sum of the selected row and
column weights, with duplicated intersection entries included in that sum. -/
theorem coverSkeleton_support {m j : ℕ} (N : CoverMatrix m) (f g : Fin j → Fin m) :
    (Finset.univ.filter (fun a => coverSkeleton N f g a ≠ none)).card =
      (∑ a, rowSupportWeight (coverMatrixReal N) (f a)) +
        ∑ a, rowSupportWeight (coverMatrixReal N).transpose (g a) := by
  classical
  change (Finset.univ.filter (fun a : (Fin j × Fin m) ⊕ (Fin j × Fin m) =>
    coverSkeleton N f g a ≠ none)).card = _
  rw [Finset.card_filter]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    unfold rowSupportWeight
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i _
    change (if N.row (f a) i ≠ none then (1 : ℕ) else 0) =
      (if coverValue (N.row (f a) i) ≠ 0 then (1 : ℕ) else 0)
    exact coverSymbol_support_indicator _
  · apply Finset.sum_congr rfl
    intro a _
    unfold rowSupportWeight
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i _
    change (if N.row i (g a) ≠ none then (1 : ℕ) else 0) =
      (if coverValue (N.row i (g a)) ≠ 0 then (1 : ℕ) else 0)
    exact coverSymbol_support_indicator _

/-- The sparse-bases construction supplies a counted skeleton; sparsity is
proved rather than added as a premise of the probability theorem. -/
theorem relativeRankMinimal_has_sparseCoverSkeleton {m : ℕ} (hm : 0 < m)
    (N : CoverMatrix m) (hmin : RelativeRankMinimal (coverMatrixReal N)) :
    HasSparseCoverSkeleton N (coverMatrixReal N).rank
      (2 * (coverMatrixReal N).rank * matrixSupportSize (coverMatrixReal N) / m) := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨I, J, hI, hJ, hci, hcj, hwI, hwJ⟩ :=
    exists_sparse_actual_bases (coverMatrixReal N) hmin
  obtain ⟨f, _, hf, hwf⟩ := exists_enumeration_of_card I hci
  obtain ⟨g, _, hg, hwg⟩ := exists_enumeration_of_card J hcj
  refine ⟨f, g, hf.symm ▸ hI, hg.symm ▸ hJ, ?_⟩
  rw [coverSkeleton_support, hwf, hwg]
  apply (Nat.le_div_iff_mul_le hm).mpr
  simp only [Fintype.card_fin] at hwI hwJ
  nlinarith

end AdaptiveOrthogonalRigidity
