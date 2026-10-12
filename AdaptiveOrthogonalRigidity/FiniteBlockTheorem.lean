import AdaptiveOrthogonalRigidity.FixedPartitionProbability

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

namespace AdaptiveOrthogonalRigidity

/-- All capped partitions with precisely `q` nontrivial physical classes. -/
def CappedSetoids (n b q : ℕ) := {s : Setoid (Fin n) //
  (∀ i, Nat.card {j : Fin n // s.r i j} ≤ b) ∧
  (nontrivialParts (setoidPartition s)).card = q}

instance (n b q : ℕ) : Fintype (CappedSetoids n b q) := by
  unfold CappedSetoids
  infer_instance

theorem blockEpsilon_nonneg {α : ℝ} (hα : 0 < α) (hαhalf : α ≤ 1 / 2) (n b : ℕ) :
    0 ≤ blockEpsilon α n b := by
  have hg : 0 ≤ gamma α := by unfold gamma; nlinarith
  exact mul_nonneg (by positivity) (Real.rpow_nonneg hg _)

/-- The finite sum in the manuscript, with the original all-real adaptive
witness event and the original heterogeneous independent graph law. -/
theorem finite_block_sum_bound {α : ℝ} {n b : ℕ}
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) (hb : 2 ≤ b) (hn : 2 * b ≤ n)
    (p : EdgeParameters n) (hp : Admissible α p) :
    eventProbability p (blockEvent n b) ≤ finiteBlockSum α n b := by
  let Q := Finset.Icc 1 (n / 2)
  let E (q : Q) : Set (GraphSample n) :=
    ⋃ s : CappedSetoids n b q.val, fixedSetoidGramEvent s.val
  have hsub : blockEvent n b ⊆ ⋃ q : Q, E q := by
    intro ω hω
    obtain ⟨s, hcap, hnon, hnorm⟩ := blockEvent_subset_blockGramEvent n b hω
    let q := (nontrivialParts (setoidPartition s)).card
    have hq : q ∈ Q := Finset.mem_Icc.mpr
      ⟨(setoid_nontrivial_iff s).mp hnon, partition_nontrivial_card_le_half _⟩
    exact Set.mem_iUnion.mpr ⟨⟨q, hq⟩, Set.mem_iUnion.mpr ⟨⟨s, hcap, rfl⟩, hnorm⟩⟩
  have hE (q : Q) : eventProbability p (E q) ≤
      (blockCandidateCount n b) ^ q.val *
        (min 1 (blockEpsilon α n b)) ^ leftBlockCount q.val := by
    let D := (min 1 (blockEpsilon α n b)) ^ leftBlockCount q.val
    have hD : 0 ≤ D := pow_nonneg (le_min (by norm_num) (blockEpsilon_nonneg hα hαhalf n b)) _
    have hfixed (s : CappedSetoids n b q.val) : eventProbability p (fixedSetoidGramEvent s.val) ≤ D := by
      have hq := (Finset.mem_Icc.mp q.property).1
      have hs := fixedSetoidGramEvent_bound hα hαhalf hb hn p hp s.val s.property.1
        (s.property.2.symm ▸ hq)
      simpa only [s.property.2] using hs
    have hcount : (Fintype.card (CappedSetoids n b q.val) : ℝ) ≤ (blockCandidateCount n b) ^ q.val := by
      have hc := capped_setoids_count (q := q.val) (show 1 ≤ n by omega) hb
      have hc' : (Fintype.card (CappedSetoids n b q.val) : ℝ) ≤
          ((((b - 1) * n ^ b) ^ q.val : ℕ) : ℝ) := by exact_mod_cast hc
      simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_sub (show 1 ≤ b by omega),
        Nat.cast_one, blockCandidateCount] using hc'
    calc
      _ ≤ ∑ s : CappedSetoids n b q.val, eventProbability p (fixedSetoidGramEvent s.val) :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _s : CappedSetoids n b q.val, D := Finset.sum_le_sum (fun s _ => hfixed s)
      _ = (Fintype.card (CappedSetoids n b q.val) : ℝ) * D := by simp
      _ ≤ (blockCandidateCount n b) ^ q.val * D := mul_le_mul_of_nonneg_right hcount hD
  calc
    _ ≤ eventProbability p (⋃ q : Q, E q) := measureReal_mono hsub
    _ ≤ ∑ q : Q, eventProbability p (E q) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ q : Q, (blockCandidateCount n b) ^ q.val *
        (min 1 (blockEpsilon α n b)) ^ leftBlockCount q.val :=
      Finset.sum_le_sum (fun q _ => hE q)
    _ = finiteBlockSum α n b := by
      simp only [finiteBlockSum, Q, Finset.univ_eq_attach]
      exact Finset.sum_attach _ (fun q => (blockCandidateCount n b) ^ q *
        (min 1 (blockEpsilon α n b)) ^ leftBlockCount q)

end AdaptiveOrthogonalRigidity
