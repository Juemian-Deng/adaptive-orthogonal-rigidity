import AdaptiveOrthogonalRigidity.FiniteRankPartition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Disjoint linear bases and rank-defect obstructions

The finite row base-packing criterion and its mutually exclusive alternative.
The sufficient direction is derived from the rank-axiom partition theorem in
`FiniteRankPartition`, proved there by tight-set induction.
-/

open scoped BigOperators Classical

noncomputable section

namespace AdaptiveOrthogonalRigidity

theorem row_image_eq_range {ι V : Type*} (u : ι → V) (S : Finset ι) :
    u '' (S : Set ι) = Set.range (fun i : S => u i) := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.property, rfl⟩

section RowRank
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq ι]

/-- The rank of the span of the rows with indices in a finite set. -/
def rowSetRank (u : ι → V) (S : Finset ι) : ℕ :=
  Module.finrank K (Submodule.span K (u '' (S : Set ι)))

/-- Row span dimension satisfies the finite matroid rank axioms over any field. -/
def rowFiniteRank (u : ι → V) : FiniteRank ι where
  rank := rowSetRank (K := K) u
  empty := by simp [rowSetRank]
  mono h := Submodule.finrank_mono (Submodule.span_mono (Set.image_mono h))
  card_le S := by
    have h := finrank_range_le_card (R := K) (fun i : S => u i)
    unfold rowSetRank
    rw [row_image_eq_range]
    simpa only [Set.finrank, Fintype.card_coe] using h
  submod S T := by
    let A := Submodule.span K (u '' (S : Set ι))
    let B := Submodule.span K (u '' (T : Set ι))
    have hU : Submodule.span K (u '' ((S ∪ T : Finset ι) : Set ι)) = A ⊔ B := by
      simp [A, B, Finset.coe_union, Set.image_union, Submodule.span_union]
    have hI : Submodule.span K (u '' ((S ∩ T : Finset ι) : Set ι)) ≤ A ⊓ B := by
      apply le_inf
      · exact Submodule.span_mono (Set.image_mono (by simp))
      · exact Submodule.span_mono (Set.image_mono (by simp))
    have hd := Submodule.finrank_sup_add_finrank_inf_eq A B
    have hle := Submodule.finrank_mono hI
    unfold rowSetRank
    rw [hU]
    exact (Nat.add_le_add_left hle _).trans_eq hd

@[simp] theorem rowFiniteRank_apply (u : ι → V) (S : Finset ι) :
    rowFiniteRank (K := K) u S = rowSetRank (K := K) u S := rfl

omit [FiniteDimensional K V] [DecidableEq ι] in
theorem rowSetRank_eq_card_iff (u : ι → V) (S : Finset ι) :
    rowSetRank (K := K) u S = S.card ↔ LinearIndependent K (fun i : S => u i) := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  simp only [Fintype.card_coe, Set.finrank, rowSetRank]
  rw [row_image_eq_range]
  exact eq_comm

end RowRank

section Packing
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] {k R : ℕ}

/-- The actual-index, pairwise disjoint row bases required in the packing lemma. -/
def DisjointRowBases (u : ι → Fin k → K) (R : ℕ) : Prop :=
  ∃ I : Fin R → Finset ι,
    Pairwise (fun a b => Disjoint (I a) (I b)) ∧
      (∀ a, LinearIndependent K (fun i : I a => u i)) ∧ (∀ a, (I a).card = k)

/-- A row deletion whose rank loss is positive and costs fewer than R rows per lost rank. -/
def RankDefectObstruction (u : ι → Fin k → K) (R : ℕ) : Prop :=
  ∃ T : Finset ι,
    1 ≤ k - rowSetRank (K := K) u (Finset.univ \ T) ∧
      T.card < R * (k - rowSetRank (K := K) u (Finset.univ \ T))

/-- The sufficient direction of the linear row base-packing criterion. -/
theorem disjointRowBases_of_rank_inequalities (u : ι → Fin k → K)
    (hspan : Submodule.span K (Set.range u) = ⊤)
    (h : ∀ T : Finset ι, R * (k - rowSetRank (K := K) u (Finset.univ \ T)) ≤ T.card) :
    DisjointRowBases u R := by
  have hr : rowFiniteRank (K := K) u Finset.univ = k := by
    rw [rowFiniteRank_apply]
    unfold rowSetRank
    rw [Finset.coe_univ, Set.image_univ, hspan, finrank_top, Module.finrank_fin_fun]
  obtain ⟨I, _, hi, hd, hc⟩ := (rowFiniteRank (K := K) u).exists_disjoint_bases
    Finset.univ k R hr (fun T _ => h T)
  refine ⟨I, hd, ?_, hc⟩
  intro a
  exact (rowSetRank_eq_card_iff u (I a)).mp (hi a)

/-- Every row basis uses at least the complementary rank defect inside any deleted set. -/
theorem DisjointRowBases.rank_inequalities {u : ι → Fin k → K}
    (hpack : DisjointRowBases u R) (T : Finset ι) :
    R * (k - rowSetRank (K := K) u (Finset.univ \ T)) ≤ T.card := by
  classical
  obtain ⟨I, hd, hi, hc⟩ := hpack
  let r := rowFiniteRank (K := K) u
  have hpart (a : Fin R) :
      k - r (Finset.univ \ T) ≤ (I a ∩ T).card := by
    have hi' : r (I a) = k :=
      ((rowSetRank_eq_card_iff u (I a)).mpr (hi a)).trans (hc a)
    have hdecomp : (I a \ T) ∪ (I a ∩ T) = I a := by
      ext e
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    have hsplit := r.union_le_add_card (I a \ T) (I a ∩ T)
    rw [hdecomp, hi'] at hsplit
    have hrank := r.mono (show I a \ T ⊆ Finset.univ \ T from by
      intro e he
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, (Finset.mem_sdiff.mp he).2⟩)
    omega
  have hd' : Pairwise (fun a b : Fin R => Disjoint (I a ∩ T) (I b ∩ T)) := by
    intro a b hab
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact Finset.disjoint_left.mp (hd hab) (Finset.mem_inter.mp he).1
      (Finset.mem_inter.mp hf).1
  have hcard : (∑ a : Fin R, (I a ∩ T).card) ≤ T.card := by
    rw [← Finset.card_biUnion (fun a _ b _ hab => hd' hab)]
    apply Finset.card_le_card
    intro e he
    obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_inter.mp ha).2
  calc
    R * (k - rowSetRank (K := K) u (Finset.univ \ T)) =
        ∑ _a : Fin R, (k - r (Finset.univ \ T)) := by simp [r]
    _ ≤ ∑ a : Fin R, (I a ∩ T).card := Finset.sum_le_sum (fun a _ => hpart a)
    _ ≤ T.card := hcard

/-- The exact finite linear base-packing criterion over an arbitrary field. -/
theorem disjointRowBases_iff_rank_inequalities (u : ι → Fin k → K)
    (hspan : Submodule.span K (Set.range u) = ⊤) :
    DisjointRowBases u R ↔
      ∀ T : Finset ι, R * (k - rowSetRank (K := K) u (Finset.univ \ T)) ≤ T.card :=
  ⟨fun h T => h.rank_inequalities T, disjointRowBases_of_rank_inequalities u hspan⟩

/-- The packing alternative from the manuscript, with genuine finite row witnesses. -/
theorem linear_base_packing_alternative (u : ι → Fin k → K)
    (hspan : Submodule.span K (Set.range u) = ⊤) (_hR : 1 ≤ R) :
    DisjointRowBases u R ∨ RankDefectObstruction u R := by
  classical
  by_cases hp : DisjointRowBases u R
  · exact Or.inl hp
  · right
    have hn : ¬ ∀ T : Finset ι,
        R * (k - rowSetRank (K := K) u (Finset.univ \ T)) ≤ T.card := by
      intro hh
      exact hp (disjointRowBases_of_rank_inequalities u hspan hh)
    push Not at hn
    obtain ⟨T, hT⟩ := hn
    refine ⟨T, ?_, hT⟩
    by_contra hj
    have hz : k - rowSetRank (K := K) u (Finset.univ \ T) = 0 := by omega
    simp [hz] at hT

/-- The two alternatives are mutually exclusive. No spanning assumption is needed here. -/
theorem linear_base_packing_exclusive (u : ι → Fin k → K) :
    ¬ (DisjointRowBases u R ∧ RankDefectObstruction u R) := by
  rintro ⟨hp, T, _, hT⟩
  exact (not_lt_of_ge (hp.rank_inequalities T)) hT

/-- A nonpacked spanning row family has a positive rank-defect deletion witness. -/
theorem rankDefectObstruction_of_not_disjointRowBases (u : ι → Fin k → K)
    (hspan : Submodule.span K (Set.range u) = ⊤) (hR : 1 ≤ R)
    (hnot : ¬ DisjointRowBases u R) : RankDefectObstruction u R :=
  (linear_base_packing_alternative u hspan hR).resolve_left hnot

end Packing
end AdaptiveOrthogonalRigidity
