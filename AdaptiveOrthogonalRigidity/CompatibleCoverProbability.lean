import AdaptiveOrthogonalRigidity.CompatibleCoverExtraction
import AdaptiveOrthogonalRigidity.CompatibleCoverArithmetic
import AdaptiveOrthogonalRigidity.AffineFibers
import AdaptiveOrthogonalRigidity.BoundArithmetic

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace AdaptiveOrthogonalRigidity

/-- Each nonzero displacement sign fixes one original graph bit. -/
def forcedCoverBit (a : CoverSymbol) : Bool := if a = some false then true else false

theorem cover_compatibility_forces_bit (a : CoverSymbol) (b : Bool)
    (ha : a ≠ none) (h : bitValue (R := ℝ) b + coverValue a = 0 ∨
      bitValue (R := ℝ) b + coverValue a = 1) : b = forcedCoverBit a := by
  cases a with
  | none => exact (ha rfl).elim
  | some s => cases s <;> cases b <;> first | rfl | (norm_num [bitValue, coverValue, forcedCoverBit] at h)

/-- Compatibility is measured in the original graph product law. The selected
support coordinates are injective original unordered edges, not fresh proxy bits. -/
theorem original_cover_rectangle_probability {n m : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (p : EdgeParameters n) (hp : Admissible α p)
    (e : CoverEndpoints n m) (N : CoverMatrix m) :
    eventProbability p (coverRectangleEvent e N) ≤
      (1 - α) ^ matrixSupportSize (coverMatrixReal N) := by
  let S := {q : Fin m × Fin m // N q.1 q.2 ≠ none}
  let f : S ↪ Edge n :=
    (Function.Embedding.subtype (fun q : Fin m × Fin m => N q.1 q.2 ≠ none)).trans
      (cutEdgeEmbedding e.left e.right e.disjoint)
  let target : S → Bool := fun q => forcedCoverBit (N q.val.1 q.val.2)
  have hsub : coverRectangleEvent e N ⊆ {ω | (fun q => ω (f q)) ∈ ({target} : Set (S → Bool))} := by
    intro ω hω
    apply Set.mem_singleton_iff.mpr
    funext q
    apply cover_compatibility_forces_bit _ _ q.property
    have h := hω q.val.1 q.val.2
    rw [adjacency_edgeOfDistinct ω (e.left q.val.1) (e.right q.val.2)
      (e.disjoint q.val.1 q.val.2)] at h
    exact h
  have hcard : Fintype.card S = matrixSupportSize (coverMatrixReal N) := by
    rw [matrixSupportSize_eq_card]
    rw [Fintype.card_subtype]
    congr 1
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (N.row q.1 q.2 ≠ none) ↔ coverValue (N.row q.1 q.2) ≠ 0
    exact (not_congr (coverValue_eq_zero_iff _)).symm
  calc
    _ ≤ eventProbability p {ω | (fun q => ω (f q)) ∈ ({target} : Set (S → Bool))} :=
      measureReal_mono hsub
    _ = (cubeMeasure (fun q => p (f q))).real {target} :=
      cube_injective_projection_probability p f {target}
    _ ≤ (1 - α) ^ Fintype.card S := cube_singleton_le hα _ (fun q => hp (f q)) target
    _ = _ := by rw [hcard]


/-- Union over every labelled endpoint choice and every consistent sparse matrix. -/
def coverFixedTripleEvent (n m j s : ℕ) : Set (GraphSample n) :=
  ⋃ c : CoverEndpoints n m × CoverCandidates m j s, coverRectangleEvent c.1 c.2.val

/-- A complete fixed-parameter union bound on the original graph law. -/
theorem coverFixedTriple_probability_le {n m j s : ℕ} {α : ℝ}
    (hα : 0 < α) (hhalf : α ≤ 1 / 2) (p : EdgeParameters n) (hp : Admissible α p) :
    eventProbability p (coverFixedTripleEvent n m j s) ≤
      ((n ^ (2 * m) * (m ^ (2 * j) * (1 + 4 * m * j) ^ (2 * j * s / m)) : ℕ) : ℝ) *
        (beta α) ^ s := by
  let C := CoverEndpoints n m × CoverCandidates m j s
  have hprob (c : C) : eventProbability p (coverRectangleEvent c.1 c.2.val) ≤ (beta α) ^ s := by
    have hh := original_cover_rectangle_probability hα.le p hp c.1 c.2.val
    simpa only [c.2.property.2, beta] using hh
  have hcard : Fintype.card C ≤ n ^ (2 * m) *
      (m ^ (2 * j) * (1 + 4 * m * j) ^ (2 * j * s / m)) := by
    rw [Fintype.card_prod]
    exact Nat.mul_le_mul (coverEndpoints_card_le n m) (coverCandidates_card_le m j s)
  calc
    _ ≤ ∑ c : C, eventProbability p (coverRectangleEvent c.1 c.2.val) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _c : C, (beta α) ^ s := Finset.sum_le_sum (fun c _ => hprob c)
    _ = (Fintype.card C : ℝ) * (beta α) ^ s := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg (beta_pos hα hhalf).le _)

/-- Each admissible parameter triple contributes at most the same half-rate tail. -/
theorem coverFixedTriple_probability_exp {n m j s : ℕ} {α lam : ℝ}
    (hα : 0 < α) (hhalf : α ≤ 1 / 2) (hn : 2 ≤ n)
    (hlam : max 1 (2 * coverEntropy n / coverRate α) ≤ lam)
    (p : EdgeParameters n) (hp : Admissible α p)
    (htriple : CoverTripleAdmissible n lam m j s) :
    eventProbability p (coverFixedTripleEvent n m j s) ≤
      Real.exp (-coverRate α * lam ^ 2 / 2) := by
  obtain ⟨hm, hmn, hj, hjn, _, _, hratio, hsupport⟩ := htriple
  exact (coverFixedTriple_probability_le hα hhalf p hp).trans
    (cover_count_times_compatibility_le hα hhalf hn hlam hm hmn hj hjn hratio hsupport)

/-- The positive parameter ranges contain exactly n*n*n^2 possible triples. -/
abbrev CoverTripleIndex (n : ℕ) :=
  (Finset.Icc 1 n) × (Finset.Icc 1 n) × (Finset.Icc 1 (n ^ 2))

theorem coverTripleIndex_card (n : ℕ) : Fintype.card (CoverTripleIndex n) = n ^ 4 := by
  simp only [CoverTripleIndex, Fintype.card_prod, Fintype.card_coe, Nat.card_Icc,
    Nat.add_sub_cancel]
  ring

/-- Invalid triples contribute the empty event; no condition is put on the graph sample. -/
def coverIndexedEvent (n : ℕ) (lam : ℝ) (t : CoverTripleIndex n) : Set (GraphSample n) :=
  if CoverTripleAdmissible n lam t.1.val t.2.1.val t.2.2.val then
    coverFixedTripleEvent n t.1.val t.2.1.val t.2.2.val else ∅

theorem compatibleCoverBadEvent_subset_finite_union {n : ℕ} {lam : ℝ} (hlam : 1 ≤ lam) :
    compatibleCoverBadEvent n lam ⊆ ⋃ t : CoverTripleIndex n, coverIndexedEvent n lam t := by
  intro ω hω
  obtain ⟨m, j, s, htriple, e, N, hN⟩ := compatibleCoverBadEvent_subset_rectangles hlam hω
  have htriple' := htriple
  obtain ⟨hm, hmn, hj, hjn, hs, hsn, _, _⟩ := htriple
  let t : CoverTripleIndex n :=
    (⟨m, Finset.mem_Icc.mpr ⟨hm, hmn⟩⟩,
      ⟨j, Finset.mem_Icc.mpr ⟨hj, hjn⟩⟩, ⟨s, Finset.mem_Icc.mpr ⟨hs, hsn⟩⟩)
  apply Set.mem_iUnion.mpr
  refine ⟨t, ?_⟩
  simp only [coverIndexedEvent, t, ite_eq_left htriple']
  exact Set.mem_iUnion.mpr ⟨(e, N), hN⟩

/-- Proposition cover: the fully adaptive compatible-displacement event,
measured under the genuine heterogeneous original-edge product law. -/
theorem compatible_displacement_cover_probability {n : ℕ} {α lam : ℝ}
    (hn : 2 ≤ n) (hα : 0 < α) (hhalf : α ≤ 1 / 2)
    (hlam : max 1 (2 * coverEntropy n / coverRate α) ≤ lam)
    (p : EdgeParameters n) (hp : Admissible α p) :
    eventProbability p (compatibleCoverBadEvent n lam) ≤
      (n : ℝ) ^ 4 * Real.exp (-coverRate α * lam ^ 2 / 2) := by
  have hbound (t : CoverTripleIndex n) : eventProbability p (coverIndexedEvent n lam t) ≤
      Real.exp (-coverRate α * lam ^ 2 / 2) := by
    unfold coverIndexedEvent
    split_ifs with ht
    · exact coverFixedTriple_probability_exp hα hhalf hn hlam p hp ht
    · simp only [eventProbability, measureReal_empty]
      exact (Real.exp_pos _).le
  calc
    _ ≤ eventProbability p (⋃ t : CoverTripleIndex n, coverIndexedEvent n lam t) :=
      measureReal_mono (compatibleCoverBadEvent_subset_finite_union ((le_max_left _ _).trans hlam))
    _ ≤ ∑ t : CoverTripleIndex n, eventProbability p (coverIndexedEvent n lam t) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _t : CoverTripleIndex n, Real.exp (-coverRate α * lam ^ 2 / 2) :=
      Finset.sum_le_sum (fun t _ => hbound t)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, coverTripleIndex_card, Nat.cast_pow]

/-- The deterministic good event gives the initial boundary used in F1 when
the displacement rank is at most twice the movement rank. -/
theorem initial_boundary_of_cover_good {n r : ℕ} {lam : ℝ} {ω : GraphSample n}
    (hlam : 0 ≤ lam) (hgood : ω ∉ compatibleCoverBadEvent n lam)
    (D : RealMatrix n) (hD : D ≠ 0) (hcomp : CompatibleDisplacement (adjacency ω) D)
    (hrank : D.rank ≤ 2 * r) :
    ∃ S : Finset (Fin n), S.card ≤ initialBoundary lam r ∧
      ∀ i ∉ S, ∀ j ∉ S, D i j = 0 := by
  obtain ⟨S, hS, hsupport⟩ := support_cover_of_not_bad hgood D hD hcomp
  refine ⟨S, ?_, hsupport⟩
  have hr : (D.rank : ℝ) ≤ 2 * r := by exact_mod_cast hrank
  have hh : (S.card : ℝ) ≤ 4 * lam * r := by
    have := mul_le_mul_of_nonneg_left hr (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlam)
    nlinarith
  have hc : (S.card : ℝ) ≤ (initialBoundary lam r : ℝ) := hh.trans (Nat.le_ceil _)
  exact_mod_cast hc

end AdaptiveOrthogonalRigidity
