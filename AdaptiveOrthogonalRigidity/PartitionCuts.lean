import AdaptiveOrthogonalRigidity.SetoidPartitions
import AdaptiveOrthogonalRigidity.BlockBoundArithmetic

open scoped BigOperators Classical

noncomputable section

namespace AdaptiveOrthogonalRigidity

abbrev PartIndex {n : ℕ} (s : Setoid (Fin n)) := (setoidPartition s).parts

def classRepresentative {n : ℕ} (s : Setoid (Fin n)) (I : PartIndex s) : Fin n :=
  partitionRepresentative (setoidPartition s) I

abbrev ClassRows {n : ℕ} (s : Setoid (Fin n)) (I : PartIndex s) :=
  {i : Fin n // s.r (classRepresentative s I) i}

instance classRows_nonempty {n : ℕ} (s : Setoid (Fin n)) (I : PartIndex s) : Nonempty (ClassRows s I) :=
  ⟨⟨classRepresentative s I, s.refl _⟩⟩

theorem classRows_mem {n : ℕ} (s : Setoid (Fin n)) (I : PartIndex s) (i : ClassRows s I) :
    i.val ∈ I.val := (setoid_representative_class s I i.val).mp i.property

theorem classRows_card {n : ℕ} (s : Setoid (Fin n)) (I : PartIndex s) :
    Fintype.card (ClassRows s I) = I.val.card := by
  rw [← Nat.card_eq_fintype_card, ← setoid_part_card]
  exact congrArg Finset.card (part_representative_eq (setoidPartition s) I)

/-- Original vertices in distinct physical classes are injectively indexed;
this embedding is the source of all later disjoint-edge independence. -/
noncomputable def classFamilyVertexEmbedding {n : ℕ} {τ : Type*} (s : Setoid (Fin n))
    (blocks : τ ↪ PartIndex s) : (Σ t, ClassRows s (blocks t)) ↪ Fin n where
  toFun q := q.2.val
  inj' := by
    rintro ⟨a, x⟩ ⟨b, y⟩ heq
    change x.val = y.val at heq
    have hpart : blocks a = blocks b := by
      apply Subtype.ext
      exact (setoidPartition s).eq_of_mem_parts (blocks a).property (blocks b).property
        (classRows_mem s (blocks a) x) (heq.symm ▸ classRows_mem s (blocks b) y)
    have hab := blocks.injective hpart
    subst b
    congr 1
    exact Subtype.ext heq

noncomputable def classSplitVertexEmbedding {n : ℕ} {σ τ : Type*} (s : Setoid (Fin n))
    (blocks : (τ ⊕ σ) ↪ PartIndex s) :
    ((Σ t, ClassRows s (blocks (Sum.inl t))) ⊕ (Σ a, ClassRows s (blocks (Sum.inr a)))) ↪ Fin n :=
  (Equiv.sumSigmaDistrib (fun k => ClassRows s (blocks k))).symm.toEmbedding.trans
    (classFamilyVertexEmbedding s blocks)

theorem class_families_disjoint {n : ℕ} {η σ τ : Type*} (s : Setoid (Fin n))
    (left : η ↪ PartIndex s) (right : (τ ⊕ σ) ↪ PartIndex s)
    (hdisj : ∀ i j, left i ≠ right j)
    (a : Σ i, ClassRows s (left i))
    (b : ((Σ t, ClassRows s (right (Sum.inl t))) ⊕ (Σ j, ClassRows s (right (Sum.inr j))))) :
    classFamilyVertexEmbedding s left a ≠ classSplitVertexEmbedding s right b := by
  intro h
  rcases b with ⟨t, y⟩ | ⟨t, y⟩
  all_goals
    change a.2.val = y.val at h
    apply hdisj a.1 _
    apply Subtype.ext
    exact (setoidPartition s).eq_of_mem_parts (left a.1).property (right _).property
      (classRows_mem s (left a.1) a.2) (h.symm ▸ classRows_mem s (right _) y)

noncomputable def classVertexEmbedding {n : ℕ} (s : Setoid (Fin n)) (I : PartIndex s) :
    ClassRows s I ↪ Fin n := ⟨Subtype.val, Subtype.val_injective⟩

theorem class_single_family_disjoint {n : ℕ} {σ τ : Type*} (s : Setoid (Fin n))
    (I : PartIndex s) (right : (τ ⊕ σ) ↪ PartIndex s) (hdisj : ∀ j, I ≠ right j)
    (a : ClassRows s I)
    (b : ((Σ t, ClassRows s (right (Sum.inl t))) ⊕ (Σ j, ClassRows s (right (Sum.inr j))))) :
    classVertexEmbedding s I a ≠ classSplitVertexEmbedding s right b := by
  intro h
  rcases b with ⟨t, y⟩ | ⟨t, y⟩
  all_goals
    change a.val = y.val at h
    apply hdisj _
    apply Subtype.ext
    exact (setoidPartition s).eq_of_mem_parts I.property (right _).property
      (classRows_mem s I a) (h.symm ▸ classRows_mem s (right _) y)

/-- The full necessary event for one fixed physical equivalence relation. -/
def fixedSetoidGramEvent {n : ℕ} (s : Setoid (Fin n)) : Set (GraphSample n) :=
  {ω | ∀ i, 2 ≤ Nat.card {j : Fin n // s.r i j} →
    ∃ u : {k : Fin n // s.r i k} → ℝ,
      (∑ k, u k ^ 2 = 1) ∧ ¬ IsSignedCoordinate u ∧
      ∀ j, ∃ m : ℕ, m ≤ Fintype.card {k : Fin n // s.r j k} ∧
        quadraticValue (blockSubmatrix (adjacency ω) s i j *
          (blockSubmatrix (adjacency ω) s i j).transpose) u = m}

end AdaptiveOrthogonalRigidity
