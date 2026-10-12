import AdaptiveOrthogonalRigidity.GraphTrainingTesting
import Mathlib.Order.Partition.Finpartition

open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

abbrev VertexPartition (n : ℕ) := Finpartition (Finset.univ : Finset (Fin n))

def nontrivialParts {n : ℕ} (P : VertexPartition n) : Finset (Finset (Fin n)) :=
  P.parts.filter (fun I => 2 ≤ I.card)

def candidateBlocks (n b : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun I => 2 ≤ I.card ∧ I.card ≤ b)

theorem partition_nontrivial_card_le_half {n : ℕ} (P : VertexPartition n) :
    (nontrivialParts P).card ≤ n / 2 := by
  have hlow : 2 * (nontrivialParts P).card ≤ ∑ I ∈ nontrivialParts P, I.card := by
    calc
      _ = ∑ _I ∈ nontrivialParts P, 2 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun I hI => (Finset.mem_filter.mp hI).2)
  have hsub : ∑ I ∈ nontrivialParts P, I.card ≤ ∑ I ∈ P.parts, I.card :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have hsum : ∑ I ∈ P.parts, I.card = n := by simpa using P.sum_card_parts
  omega

theorem partition_card_lower {n b : ℕ} (P : VertexPartition n)
    (hcap : ∀ I ∈ P.parts, I.card ≤ b) : n ≤ b * P.parts.card := by
  have hsum : ∑ I ∈ P.parts, I.card = n := by simpa using P.sum_card_parts
  calc
    n = ∑ I ∈ P.parts, I.card := hsum.symm
    _ ≤ ∑ _I ∈ P.parts, b := Finset.sum_le_sum hcap
    _ = _ := by simp [Nat.mul_comm]

/-- Singleton parts are forced by the union of nontrivial parts. Hence no
additional choices or sign patterns enter the physical-partition count. -/
theorem nontrivialParts_injective (n : ℕ) : Function.Injective (nontrivialParts (n := n)) := by
  have hsub (P Q : VertexPartition n) (he : nontrivialParts P = nontrivialParts Q) : P.parts ⊆ Q.parts := by
    intro I hI
    by_cases hsize : 2 ≤ I.card
    · have hmem : I ∈ nontrivialParts P := Finset.mem_filter.mpr ⟨hI, hsize⟩
      rw [he] at hmem
      exact (Finset.mem_filter.mp hmem).1
    · have hpos := Finset.card_pos.mpr (P.nonempty_of_mem_parts hI)
      have hone : I.card = 1 := by omega
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hone
      obtain ⟨J, hJ, hiJ⟩ := Q.exists_mem (Finset.mem_univ i)
      by_cases hJsize : 2 ≤ J.card
      · have hmem : J ∈ nontrivialParts Q := Finset.mem_filter.mpr ⟨hJ, hJsize⟩
        rw [← he] at hmem
        have heq := P.eq_of_mem_parts hI (Finset.mem_filter.mp hmem).1 (Finset.mem_singleton_self i) hiJ
        rwa [← heq] at hJ
      · have hJpos := Finset.card_pos.mpr (Q.nonempty_of_mem_parts hJ)
        have hJone : J.card = 1 := by omega
        obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hJone
        have hij : i = j := Finset.mem_singleton.mp hiJ
        simpa only [hij] using hJ
  intro P Q he
  exact Finpartition.ext (Finset.Subset.antisymm (hsub P Q he) (hsub Q P he.symm))

theorem nontrivialParts_subset_candidates {n b : ℕ} (P : VertexPartition n)
    (hcap : ∀ I ∈ P.parts, I.card ≤ b) : nontrivialParts P ⊆ candidateBlocks n b := by
  intro I hI
  obtain ⟨hmem, hsize⟩ := Finset.mem_filter.mp hI
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsize, hcap I hmem⟩

theorem candidateBlocks_card_le {n b : ℕ} (hn : 1 ≤ n) (hb : 2 ≤ b) :
    (candidateBlocks n b).card ≤ (b - 1) * n ^ b := by
  have hsub : candidateBlocks n b ⊆
      (Finset.Icc 2 b).biUnion (fun s => (Finset.univ : Finset (Fin n)).powersetCard s) := by
    intro I hI
    obtain ⟨_, hlo, hhi⟩ := Finset.mem_filter.mp hI
    apply Finset.mem_biUnion.mpr
    exact ⟨I.card, Finset.mem_Icc.mpr ⟨hlo, hhi⟩,
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩
  calc
    _ ≤ ((Finset.Icc 2 b).biUnion (fun s => (Finset.univ : Finset (Fin n)).powersetCard s)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ s ∈ Finset.Icc 2 b, ((Finset.univ : Finset (Fin n)).powersetCard s).card :=
      Finset.card_biUnion_le
    _ = ∑ s ∈ Finset.Icc 2 b, n.choose s := by simp
    _ ≤ ∑ _s ∈ Finset.Icc 2 b, n ^ b := by
      apply Finset.sum_le_sum
      intro s hs
      exact (Nat.choose_le_pow n s).trans (Nat.pow_le_pow_right hn (Finset.mem_Icc.mp hs).2)
    _ = (b - 1) * n ^ b := by simp

/-- With q nontrivial parts the finite partition count is at most a^q; allowing
all q-subsets of candidates only increases the count. -/
theorem capped_partitions_count {n b q : ℕ} (hn : 1 ≤ n) (hb : 2 ≤ b) :
    Fintype.card {P : VertexPartition n //
      (∀ I ∈ P.parts, I.card ≤ b) ∧ (nontrivialParts P).card = q} ≤
      ((b - 1) * n ^ b) ^ q := by
  let code : {P : VertexPartition n //
      (∀ I ∈ P.parts, I.card ≤ b) ∧ (nontrivialParts P).card = q} →
      {S // S ∈ (candidateBlocks n b).powersetCard q} := fun P =>
    ⟨nontrivialParts P.val,
      Finset.mem_powersetCard.mpr ⟨nontrivialParts_subset_candidates P.val P.property.1, P.property.2⟩⟩
  have hinj : Function.Injective code := by
    intro P Q h
    exact Subtype.ext (nontrivialParts_injective n (congrArg Subtype.val h))
  calc
    _ ≤ Fintype.card {S // S ∈ (candidateBlocks n b).powersetCard q} :=
      Fintype.card_le_of_injective code hinj
    _ = (candidateBlocks n b).card.choose q := by
      rw [Fintype.card_coe, Finset.card_powersetCard]
    _ ≤ (candidateBlocks n b).card ^ q := Nat.choose_le_pow _ _
    _ ≤ ((b - 1) * n ^ b) ^ q := Nat.pow_le_pow_left (candidateBlocks_card_le hn hb) q

end AdaptiveOrthogonalRigidity
