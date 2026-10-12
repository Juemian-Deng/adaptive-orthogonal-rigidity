import AdaptiveOrthogonalRigidity.PartitionCounting

open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

noncomputable def setoidPartition {n : ℕ} (s : Setoid (Fin n)) : VertexPartition n :=
  Finpartition.ofSetoid s

theorem setoidPartition_injective (n : ℕ) : Function.Injective (setoidPartition (n := n)) := by
  intro s t h
  apply Setoid.ext
  intro i j
  rw [← Finpartition.mem_part_ofSetoid_iff_rel, ← Finpartition.mem_part_ofSetoid_iff_rel]
  change j ∈ (setoidPartition s).part i ↔ j ∈ (setoidPartition t).part i
  rw [h]

noncomputable instance finiteSetoidFintype (n : ℕ) : Fintype (Setoid (Fin n)) :=
  Fintype.ofInjective setoidPartition (setoidPartition_injective n)

theorem setoid_part_membership {n : ℕ} (s : Setoid (Fin n)) (i j : Fin n) :
    j ∈ (setoidPartition s).part i ↔ s.r i j :=
  Finpartition.mem_part_ofSetoid_iff_rel

theorem setoid_part_card {n : ℕ} (s : Setoid (Fin n)) (i : Fin n) :
    ((setoidPartition s).part i).card = Nat.card {j : Fin n // s.r i j} := by
  rw [Nat.card_eq_fintype_card]
  let e : ((setoidPartition s).part i) ≃ {j : Fin n // s.r i j} :=
    Equiv.subtypeEquivRight (fun j => setoid_part_membership s i j)
  simpa only [Fintype.card_coe] using Fintype.card_congr e

/-- A deterministic representative of each genuine equivalence class. -/
noncomputable def partitionRepresentative {n : ℕ} (P : VertexPartition n) (I : P.parts) : Fin n :=
  Classical.choose (P.nonempty_of_mem_parts I.property)

theorem partitionRepresentative_mem {n : ℕ} (P : VertexPartition n) (I : P.parts) :
    partitionRepresentative P I ∈ I.val :=
  Classical.choose_spec (P.nonempty_of_mem_parts I.property)

theorem part_representative_eq {n : ℕ} (P : VertexPartition n) (I : P.parts) :
    P.part (partitionRepresentative P I) = I.val :=
  P.part_eq_of_mem I.property (partitionRepresentative_mem P I)

theorem setoid_representative_class {n : ℕ} (s : Setoid (Fin n))
    (I : (setoidPartition s).parts) (j : Fin n) :
    s.r (partitionRepresentative (setoidPartition s) I) j ↔ j ∈ I.val := by
  rw [← setoid_part_membership, part_representative_eq]

theorem setoid_cap_iff_partition_cap {n b : ℕ} (s : Setoid (Fin n)) :
    (∀ i, Nat.card {j : Fin n // s.r i j} ≤ b) ↔
      (∀ I ∈ (setoidPartition s).parts, I.card ≤ b) := by
  constructor
  · intro h I hI
    let J : (setoidPartition s).parts := ⟨I, hI⟩
    have hi := h (partitionRepresentative (setoidPartition s) J)
    rw [← setoid_part_card, part_representative_eq] at hi
    exact hi
  · intro h i
    rw [← setoid_part_card]
    exact h _ ((setoidPartition s).part_mem.mpr (Finset.mem_univ i))

theorem setoid_nontrivial_iff {n : ℕ} (s : Setoid (Fin n)) :
    (∃ i, 2 ≤ Nat.card {j : Fin n // s.r i j}) ↔
      1 ≤ (nontrivialParts (setoidPartition s)).card := by
  change (∃ i, 2 ≤ Nat.card {j : Fin n // s.r i j}) ↔
    0 < (nontrivialParts (setoidPartition s)).card
  rw [Finset.card_pos]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨(setoidPartition s).part i, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact (setoidPartition s).part_mem.mpr (Finset.mem_univ i)
    · rwa [setoid_part_card]
  · rintro ⟨I, hI⟩
    obtain ⟨hmem, hsize⟩ := Finset.mem_filter.mp hI
    let J : (setoidPartition s).parts := ⟨I, hmem⟩
    refine ⟨partitionRepresentative (setoidPartition s) J, ?_⟩
    rw [← setoid_part_card, part_representative_eq]
    exact hsize

theorem capped_setoids_count {n b q : ℕ} (hn : 1 ≤ n) (hb : 2 ≤ b) :
    Fintype.card {s : Setoid (Fin n) //
      (∀ i, Nat.card {j : Fin n // s.r i j} ≤ b) ∧
      (nontrivialParts (setoidPartition s)).card = q} ≤ ((b - 1) * n ^ b) ^ q := by
  let f : {s : Setoid (Fin n) //
      (∀ i, Nat.card {j : Fin n // s.r i j} ≤ b) ∧
      (nontrivialParts (setoidPartition s)).card = q} →
      {P : VertexPartition n // (∀ I ∈ P.parts, I.card ≤ b) ∧ (nontrivialParts P).card = q} :=
    fun s => ⟨setoidPartition s.val, (setoid_cap_iff_partition_cap s.val).mp s.property.1, s.property.2⟩
  have hinj : Function.Injective f := by
    intro s t h
    exact Subtype.ext (setoidPartition_injective n (congrArg Subtype.val h))
  exact (Fintype.card_le_of_injective f hinj).trans (capped_partitions_count hn hb)

end AdaptiveOrthogonalRigidity
