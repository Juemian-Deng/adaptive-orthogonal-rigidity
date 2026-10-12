import AdaptiveOrthogonalRigidity.PartitionCuts

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

namespace AdaptiveOrthogonalRigidity

def leftTestingEvent {ι σ τ : Type*} [Fintype ι]
    (ρ : σ → Type*) (κ : τ → Type*) [∀ s, Fintype (ρ s)] [∀ t, Fintype (κ t)]
    (b : ℕ) : Set ((ι × ((Σ t, κ t) ⊕ (Σ s, ρ s))) → Bool) :=
  {X | ∃ u : ι → ℝ, (∑ i, u i ^ 2 = 1) ∧ ¬ IsSignedCoordinate u ∧
    (∀ s, ∃ m : ℕ, m ≤ b ∧
      quadraticValue (gramSymmetric (R := ℝ) (fun e => X (e.1, Sum.inr ⟨s, e.2⟩))).val u = m) ∧
    ∀ t, ∃ k : ℤ,
      quadraticValue (gramSymmetric (R := ℝ) (fun e => X (e.1, Sum.inl ⟨t, e.2⟩))).val u = k}

theorem leftTestingEvent_bound {ι σ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    (ρ : σ → Type*) (κ : τ → Type*)
    [∀ s, Fintype (ρ s)] [∀ s, DecidableEq (ρ s)] [∀ s, Nonempty (ρ s)]
    [∀ t, Fintype (κ t)] [∀ t, DecidableEq (κ t)] [∀ t, Nonempty (κ t)]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (b : ℕ)
    (p : (ι × ((Σ t, κ t) ⊕ (Σ s, ρ s))) → unitInterval)
    (hp : ∀ e, α ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - α) :
    (cubeMeasure p).real (leftTestingEvent ρ κ b) ≤
      (3 : ℝ) ^ symmetricDimension (Fintype.card ι) * (gamma α) ^ Fintype.card σ +
        (b + 1 : ℝ) ^ symmetricDimension (Fintype.card ι) * (gamma α) ^ Fintype.card τ := by
  let e := rectangleSplitIndexEquiv (ι := ι) ρ κ
  let E : Set (((Σ t, ι × κ t) ⊕ (Σ s, ι × ρ s)) → Bool) :=
    {X | ∃ u : ι → ℝ, (∑ i, u i ^ 2 = 1) ∧ ¬ IsSignedCoordinate u ∧
      (∀ s, ∃ m : ℕ, m ≤ b ∧
        quadraticValue (gramSymmetric (R := ℝ) (fun q => X (Sum.inr ⟨s, q⟩))).val u = m) ∧
      ∀ t, ∃ k : ℤ,
        quadraticValue (gramSymmetric (R := ℝ) (fun q => X (Sum.inl ⟨t, q⟩))).val u = k}
  have hb := adaptive_rectangle_training_testing ρ κ hα hα1 b (fun q => p (e q)) (fun q => hp (e q))
  change (cubeMeasure (fun q => p (e q))).real E ≤ _ at hb
  exact (cube_injective_projection_probability p e.toEmbedding E).trans_le hb

/-- Selected nontrivial left classes and disjoint right classes supply the
whole left events used by independence. The same u serves all its right tests. -/
theorem fixedSetoidGramEvent_subset_left_tests {n b : ℕ} {η σ τ : Type*}
    [Fintype η] [Fintype σ] [Fintype τ] [DecidableEq η] [DecidableEq σ] [DecidableEq τ]
    (s : Setoid (Fin n)) (hcap : ∀ i, Nat.card {j : Fin n // s.r i j} ≤ b)
    (left : η ↪ PartIndex s) (right : (τ ⊕ σ) ↪ PartIndex s)
    (hleft : ∀ a, 2 ≤ (left a).val.card) (hdisj : ∀ i j, left i ≠ right j) :
    fixedSetoidGramEvent s ⊆ {ω | ∀ a,
      (fun q => ω (familyCutEdgeEmbedding (fun a => ClassRows s (left a))
        (classFamilyVertexEmbedding s left) (classSplitVertexEmbedding s right)
        (class_families_disjoint s left right hdisj) ⟨a, q⟩)) ∈
        leftTestingEvent (fun c => ClassRows s (right (Sum.inr c)))
          (fun t => ClassRows s (right (Sum.inl t))) b} := by
  intro ω hω a
  let f := familyCutEdgeEmbedding (fun a => ClassRows s (left a))
    (classFamilyVertexEmbedding s left) (classSplitVertexEmbedding s right)
    (class_families_disjoint s left right hdisj)
  have ha : 2 ≤ Nat.card {j : Fin n // s.r (classRepresentative s (left a)) j} := by
    rw [Nat.card_eq_fintype_card]
    exact (classRows_card s (left a)) ▸ hleft a
  obtain ⟨u, hu, hnon, hnorms⟩ := hω (classRepresentative s (left a)) ha
  refine ⟨u, hu, hnon, ?_, ?_⟩
  · intro c
    obtain ⟨m, hm, hvalue⟩ := hnorms (classRepresentative s (right (Sum.inr c)))
    have hbound : Fintype.card (ClassRows s (right (Sum.inr c))) ≤ b := by
      simpa only [Nat.card_eq_fintype_card] using hcap (classRepresentative s (right (Sum.inr c)))
    refine ⟨m, hm.trans hbound, ?_⟩
    have hmatrix : cubeMatrix (R := ℝ) (fun e => ω (f ⟨a, e.1, Sum.inr ⟨c, e.2⟩⟩)) =
        blockSubmatrix (adjacency ω) s (classRepresentative s (left a))
          (classRepresentative s (right (Sum.inr c))) := by
      ext i j
      exact (adjacency_edgeOfDistinct ω i.val j.val
        (class_families_disjoint s left right hdisj ⟨a, i⟩ (Sum.inr ⟨c, j⟩))).symm
    change quadraticValue (cubeMatrix _ * (cubeMatrix _).transpose) u = m
    rw [hmatrix]
    exact hvalue
  · intro t
    obtain ⟨m, _, hvalue⟩ := hnorms (classRepresentative s (right (Sum.inl t)))
    refine ⟨(m : ℤ), ?_⟩
    have hmatrix : cubeMatrix (R := ℝ) (fun e => ω (f ⟨a, e.1, Sum.inl ⟨t, e.2⟩⟩)) =
        blockSubmatrix (adjacency ω) s (classRepresentative s (left a))
          (classRepresentative s (right (Sum.inl t))) := by
      ext i j
      exact (adjacency_edgeOfDistinct ω i.val j.val
        (class_families_disjoint s left right hdisj ⟨a, i⟩ (Sum.inl ⟨t, j⟩))).symm
    change quadraticValue (cubeMatrix _ * (cubeMatrix _).transpose) u = (m : ℤ)
    rw [hmatrix]
    exact_mod_cast hvalue

/-- The probability cost multiplies across selected left blocks. All bounds
are for whole existential events on disjoint original edge cuts. -/
theorem fixedSetoidGramEvent_bound_of_split {n b : ℕ} {η σ τ : Type*}
    [Fintype η] [Fintype σ] [Fintype τ] [DecidableEq η] [DecidableEq σ] [DecidableEq τ]
    {α : ℝ} (hα : 0 < α) (hαhalf : α ≤ 1 / 2) (hb : 2 ≤ b)
    (p : EdgeParameters n) (hp : Admissible α p)
    (s : Setoid (Fin n)) (hcap : ∀ i, Nat.card {j : Fin n // s.r i j} ≤ b)
    (left : η ↪ PartIndex s) (right : (τ ⊕ σ) ↪ PartIndex s)
    (hleft : ∀ a, 2 ≤ (left a).val.card) (hdisj : ∀ i j, left i ≠ right j)
    (hlt : Fintype.card σ ≤ Fintype.card τ)
    (hl : (n : ℝ) / (4 * b) - 1 ≤ (Fintype.card σ : ℝ)) :
    eventProbability p (fixedSetoidGramEvent s) ≤
      (min 1 (blockEpsilon α n b)) ^ Fintype.card η := by
  let rows := fun a => ClassRows s (left a)
  let cols := ((Σ t, ClassRows s (right (Sum.inl t))) ⊕ (Σ c, ClassRows s (right (Sum.inr c))))
  let Vleft := classFamilyVertexEmbedding s left
  let Vright := classSplitVertexEmbedding s right
  let disj := class_families_disjoint s left right hdisj
  let f := familyCutEdgeEmbedding rows Vleft Vright disj
  let E : ∀ a, Set (rows a × cols → Bool) := fun _ =>
    leftTestingEvent (fun c => ClassRows s (right (Sum.inr c)))
      (fun t => ClassRows s (right (Sum.inl t))) b
  have hE (a : η) :
      (cubeMeasure (fun e => p (f ⟨a, e⟩))).real (E a) ≤ min 1 (blockEpsilon α n b) := by
    apply le_min measureReal_le_one
    have hprob := leftTestingEvent_bound
      (fun c => ClassRows s (right (Sum.inr c))) (fun t => ClassRows s (right (Sum.inl t)))
      hα.le (by linarith : α ≤ 1) b (fun e => p (f ⟨a, e⟩)) (fun e => hp (f ⟨a, e⟩))
    have hsize : Fintype.card (rows a) ≤ b := by
      simpa only [Nat.card_eq_fintype_card] using hcap (classRepresentative s (left a))
    exact hprob.trans (training_bound_le_blockEpsilon hα hαhalf hb hsize hlt hl)
  calc
    _ ≤ eventProbability p {ω | ∀ a, (fun e => ω (f ⟨a, e⟩)) ∈ E a} :=
      measureReal_mono (fixedSetoidGramEvent_subset_left_tests s hcap left right hleft hdisj)
    _ = ∏ a, (cubeMeasure (fun e => p (f ⟨a, e⟩))).real (E a) :=
      original_left_block_events_independent rows p Vleft Vright disj E
    _ ≤ ∏ _a : η, min 1 (blockEpsilon α n b) := by
      apply Finset.prod_le_prod₀
      · intro a _; exact measureReal_nonneg
      · intro a _; exact hE a
    _ = _ := by simp

theorem nontrivial_index_card {n : ℕ} (s : Setoid (Fin n)) :
    (Finset.univ.filter (fun I : PartIndex s => 2 ≤ I.val.card)).card =
      (nontrivialParts (setoidPartition s)).card := by
  let e : (Finset.univ.filter (fun I : PartIndex s => 2 ≤ I.val.card)) ≃
      nontrivialParts (setoidPartition s) := {
    toFun I := ⟨I.val.val, Finset.mem_filter.mpr ⟨I.val.property, (Finset.mem_filter.mp I.property).2⟩⟩
    invFun I := ⟨⟨I.val, (Finset.mem_filter.mp I.property).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp I.property).2⟩⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  simpa only [Fintype.card_coe] using Fintype.card_congr e

/-- Every valid physical partition admits the required left/right and training/
testing split, including q=1. No split remains as an endpoint hypothesis. -/
theorem fixedSetoidGramEvent_bound {n b : ℕ}
    {α : ℝ} (hα : 0 < α) (hαhalf : α ≤ 1 / 2) (hb : 2 ≤ b) (hn : 2 * b ≤ n)
    (p : EdgeParameters n) (hp : Admissible α p)
    (s : Setoid (Fin n)) (hcap : ∀ i, Nat.card {j : Fin n // s.r i j} ≤ b)
    (hq : 1 ≤ (nontrivialParts (setoidPartition s)).card) :
    eventProbability p (fixedSetoidGramEvent s) ≤
      (min 1 (blockEpsilon α n b)) ^ leftBlockCount (nontrivialParts (setoidPartition s)).card := by
  let q := (nontrivialParts (setoidPartition s)).card
  let N := Finset.univ.filter (fun I : PartIndex s => 2 ≤ I.val.card)
  have hN : N.card = q := nontrivial_index_card s
  obtain ⟨L, hLN, hLcard⟩ := Finset.exists_subset_card_eq
    (show leftBlockCount q ≤ N.card by rw [hN]; exact leftBlockCount_le hq)
  let R := (Finset.univ : Finset (PartIndex s)) \ L
  obtain ⟨T, hTR, hTcard⟩ := Finset.exists_subset_card_eq (show R.card / 2 ≤ R.card by omega)
  let U := R \ T
  let left : L ↪ PartIndex s := ⟨Subtype.val, Subtype.val_injective⟩
  let right : (U ⊕ T) ↪ PartIndex s :=
    { toFun := Sum.elim Subtype.val Subtype.val
      inj' := by
        intro a b h
        rcases a with a | a <;> rcases b with b | b
        · exact congrArg Sum.inl (Subtype.ext h)
        · change a.val = b.val at h
          exact False.elim ((Finset.mem_sdiff.mp a.property).2 (h.symm ▸ b.property))
        · change a.val = b.val at h
          exact False.elim ((Finset.mem_sdiff.mp b.property).2 (h ▸ a.property))
        · exact congrArg Sum.inr (Subtype.ext h) }
  have hleft (a : L) : 2 ≤ (left a).val.card := (Finset.mem_filter.mp (hLN a.property)).2
  have hdisj (a : L) (j : U ⊕ T) : left a ≠ right j := by
    intro h
    rcases j with j | j
    · change a.val = j.val at h
      exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp j.property).1).2 (h ▸ a.property)
    · change a.val = j.val at h
      exact (Finset.mem_sdiff.mp (hTR j.property)).2 (h ▸ a.property)
  have hUcard : U.card = R.card - T.card := Finset.card_sdiff_of_subset hTR
  have hlt : Fintype.card T ≤ Fintype.card U := by
    simp only [Fintype.card_coe]
    rw [hUcard, hTcard]
    omega
  have hRcard : R.card = (setoidPartition s).parts.card - leftBlockCount q := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ L), Finset.card_univ,
      Fintype.card_coe, hLcard]
  have hcapP := (setoid_cap_iff_partition_cap s).mp hcap
  have hqM : q ≤ (setoidPartition s).parts.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hl : (n : ℝ) / (4 * b) - 1 ≤ (Fintype.card T : ℝ) := by
    simp only [Fintype.card_coe]
    rw [hTcard, hRcard]
    exact training_card_real_lower hb hn (partition_card_lower (setoidPartition s) hcapP) hq hqM
  have hbound := fixedSetoidGramEvent_bound_of_split hα hαhalf hb p hp s hcap left right hleft hdisj hlt hl
  simpa only [Fintype.card_coe, hLcard] using hbound

end AdaptiveOrthogonalRigidity
