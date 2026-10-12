import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ext
import Lean.Elab.Tactic.Omega

/-!
# Finite rank-function partition

A self-contained finite matroid partition argument from the rank axioms.
The proof uses induction on the ground-set cardinality and tight subsets.
This module does not assume a matroid union or packing theorem.
-/

open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- The finite matroid rank axioms, on an ambient type of elements. -/
structure FiniteRank (ι : Type*) [DecidableEq ι] where
  rank : Finset ι → ℕ
  empty : rank ∅ = 0
  mono : ∀ {S T}, S ⊆ T → rank S ≤ rank T
  card_le : ∀ S, rank S ≤ S.card
  submod : ∀ S T, rank (S ∪ T) + rank (S ∩ T) ≤ rank S + rank T

namespace FiniteRank

variable {ι : Type*} [DecidableEq ι]

instance : CoeFun (FiniteRank ι) (fun _ => Finset ι → ℕ) := ⟨FiniteRank.rank⟩

@[simp] theorem empty_eq (r : FiniteRank ι) : r ∅ = 0 := r.empty

theorem union_le (r : FiniteRank ι) (S T : Finset ι) : r (S ∪ T) ≤ r S + r T := by
  have := r.submod S T
  omega

theorem union_le_add_card (r : FiniteRank ι) (S T : Finset ι) :
    r (S ∪ T) ≤ r S + T.card := (r.union_le S T).trans (Nat.add_le_add_left (r.card_le T) _)

/-- Contract a set. The new rank may be evaluated on arbitrary ambient subsets. -/
def contract (r : FiniteRank ι) (C : Finset ι) : FiniteRank ι where
  rank S := r (S ∪ C) - r C
  empty := by simp
  mono h := Nat.sub_le_sub_right (r.mono (Finset.union_subset_union_left h)) _
  card_le S := by
    have := r.union_le_add_card C S
    rw [Finset.union_comm] at this
    omega
  submod S T := by
    have h := r.submod (S ∪ C) (T ∪ C)
    have h₁ := r.mono (Finset.subset_union_right : C ⊆ S ∪ C)
    have h₂ := r.mono (Finset.subset_union_right : C ⊆ T ∪ C)
    have h₃ := r.mono (Finset.subset_union_right : C ⊆ (S ∩ T) ∪ C)
    have h₄ := r.mono (Finset.subset_union_right : C ⊆ (S ∪ T) ∪ C)
    have hu : (S ∪ C) ∪ (T ∪ C) = (S ∪ T) ∪ C := by ext; simp; tauto
    have hi : (S ∪ C) ∩ (T ∪ C) = (S ∩ T) ∪ C := by ext; simp; tauto
    rw [hu, hi] at h
    omega

@[simp] theorem contract_apply (r : FiniteRank ι) (C S : Finset ι) :
    r.contract C S = r (S ∪ C) - r C := rfl

theorem contract_add (r : FiniteRank ι) (C S : Finset ι) :
    r.contract C S + r C = r (S ∪ C) :=
  Nat.sub_add_cancel (r.mono Finset.subset_union_right)

theorem le_contract_add (r : FiniteRank ι) (C S : Finset ι) :
    r S ≤ r.contract C S + r C := by
  rw [r.contract_add]
  exact r.mono Finset.subset_union_left

/-- Replacing a spanning subset by the set it spans does not change any union rank. -/
theorem union_eq_of_subset_of_rank_eq (r : FiniteRank ι) {I A : Finset ι}
    (hIA : I ⊆ A) (h : r I = r A) (S : Finset ι) : r (I ∪ S) = r (A ∪ S) := by
  apply Nat.le_antisymm (r.mono (Finset.union_subset_union_left hIA))
  have hsub := r.submod A (I ∪ S)
  have hI := r.mono (show I ⊆ A ∩ (I ∪ S) from by
    intro e he; exact Finset.mem_inter.mpr ⟨hIA he, Finset.mem_union_left _ he⟩)
  have hU : A ∪ (I ∪ S) = A ∪ S := by
    ext e; simp only [Finset.mem_union]; constructor
    · rintro (ha | hi | hs)
      · exact Or.inl ha
      · exact Or.inl (hIA hi)
      · exact Or.inr hs
    · tauto
  rw [hU] at hsub
  omega

/-- The uniform finite rank function with a prescribed capacity. -/
def uniform (q : ℕ) : FiniteRank ι where
  rank S := min S.card q
  empty := by simp
  mono h := min_le_min_right _ (Finset.card_le_card h)
  card_le S := Nat.min_le_left _ _
  submod S T := by
    have hc := Finset.card_union_add_card_inter S T
    have h₁ := Finset.card_le_card (Finset.inter_subset_left : S ∩ T ⊆ S)
    have h₂ := Finset.card_le_card (Finset.inter_subset_right : S ∩ T ⊆ T)
    omega

@[simp] theorem uniform_apply (q : ℕ) (S : Finset ι) : uniform q S = min S.card q := rfl

end FiniteRank

/-- A partition of a finite ground set into independent sets for a family of ranks. -/
structure RankPartition {ι α : Type*} [DecidableEq ι] (r : α → FiniteRank ι)
    (E : Finset ι) where
  parts : α → Finset ι
  subset : ∀ a, parts a ⊆ E
  independent : ∀ a, r a (parts a) = (parts a).card
  disjoint : Pairwise (fun a b => Disjoint (parts a) (parts b))
  covers : ∀ e ∈ E, ∃ a, e ∈ parts a

namespace RankPartition

variable {ι α : Type*} [DecidableEq ι] [Fintype α]
variable {r : α → FiniteRank ι} {E : Finset ι}

/-- The cardinality of the ground set is the sum of the part cardinalities. -/
theorem sum_card (P : RankPartition r E) : ∑ a, (P.parts a).card = E.card := by
  classical
  have hU : Finset.univ.biUnion P.parts = E := by
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨fun ⟨a, ha⟩ => P.subset a ha, P.covers e⟩
  calc
    _ = (Finset.univ.biUnion P.parts).card :=
      (Finset.card_biUnion (fun a _ b _ hab => P.disjoint hab)).symm
    _ = E.card := congrArg Finset.card hU

/-- On a tight ground set every part spans its corresponding rank. -/
theorem rank_eq_on_tight (P : RankPartition r E) (hE : E.card = ∑ a, r a E) (a : α) :
    r a (P.parts a) = r a E := by
  have hle (b : α) : (P.parts b).card ≤ r b E := by
    rw [← P.independent]
    exact (r b).mono (P.subset b)
  have hsum : ∑ b, (P.parts b).card = ∑ b, r b E := P.sum_card.trans hE
  rw [P.independent]
  exact (Finset.sum_eq_sum_iff_of_le (fun b _ => hle b)).mp hsum a (Finset.mem_univ a)

/-- Glue a partition of a tight set to a partition in the contracted ranks. -/
def glue {A : Finset ι} (hAE : A ⊆ E) (P : RankPartition r A)
    (hA : A.card = ∑ a, r a A)
    (Q : RankPartition (fun a => (r a).contract A) (E \ A)) : RankPartition r E where
  parts a := P.parts a ∪ Q.parts a
  subset a := Finset.union_subset (fun _ hx => hAE (P.subset a hx))
    (fun _ hx => (Finset.mem_sdiff.mp (Q.subset a hx)).1)
  independent a := by
    have hd : Disjoint (P.parts a) (Q.parts a) := by
      apply Finset.disjoint_left.mpr
      intro e he he'
      exact (Finset.mem_sdiff.mp (Q.subset a he')).2 (P.subset a he)
    rw [(r a).union_eq_of_subset_of_rank_eq (P.subset a) (P.rank_eq_on_tight hA a),
      Finset.union_comm A, ← (r a).contract_add, Q.independent, Finset.card_union_of_disjoint hd]
    have := P.rank_eq_on_tight hA a
    rw [P.independent] at this
    omega
  disjoint := by
    intro a b hab
    apply Finset.disjoint_left.mpr
    intro e he hf
    rcases Finset.mem_union.mp he with he | he <;>
      rcases Finset.mem_union.mp hf with hf | hf
    · exact Finset.disjoint_left.mp (P.disjoint hab) he hf
    · exact (Finset.mem_sdiff.mp (Q.subset b hf)).2 (P.subset a he)
    · exact (Finset.mem_sdiff.mp (Q.subset a he)).2 (P.subset b hf)
    · exact Finset.disjoint_left.mp (Q.disjoint hab) he hf
  covers e he := by
    by_cases h : e ∈ A
    · obtain ⟨a, ha⟩ := P.covers e h
      exact ⟨a, Finset.mem_union_left _ ha⟩
    · obtain ⟨a, ha⟩ := Q.covers e (Finset.mem_sdiff.mpr ⟨he, h⟩)
      exact ⟨a, Finset.mem_union_right _ ha⟩

/-- Contract a single chosen element in a single chosen color. -/
noncomputable def contractOne (r : α → FiniteRank ι) (a₀ : α) (e : ι) : α → FiniteRank ι :=
  fun a => if a = a₀ then (r a).contract {e} else r a

/-- Reinsert an element in its contracted color. -/
noncomputable def addSingleton (e : ι) (he : e ∈ E) (a₀ : α)
    (ha : r a₀ {e} = 1) (Q : RankPartition (contractOne r a₀ e) (E.erase e)) :
    RankPartition r E := by
  classical
  refine {
    parts := fun a => if a = a₀ then insert e (Q.parts a) else Q.parts a
    subset := ?_
    independent := ?_
    disjoint := ?_
    covers := ?_
  }
  · intro a
    split_ifs
    · exact Finset.insert_subset he (fun _ hx => Finset.mem_of_mem_erase (Q.subset a hx))
    · exact fun _ hx => Finset.mem_of_mem_erase (Q.subset a hx)
  · intro a
    have hen : e ∉ Q.parts a := by
      intro hx
      exact (Finset.mem_erase.mp (Q.subset a hx)).1 rfl
    by_cases h : a = a₀
    · subst a
      simp only [ite_true, Finset.card_insert_of_notMem hen]
      have hQ := Q.independent a₀
      simp [contractOne, FiniteRank.contract_apply, ha] at hQ
      have hle : 1 ≤ r a₀ (insert e (Q.parts a₀)) := by
        rw [← ha]
        exact (r a₀).mono (by simp)
      omega
    · simp only [ite_eq_right h]
      simpa only [contractOne, ite_eq_right h] using Q.independent a
  · intro a b hab
    apply Finset.disjoint_left.mpr
    intro x hx hy
    by_cases ha' : a = a₀ <;> by_cases hb' : b = a₀
    · exact hab (ha'.trans hb'.symm)
    · simp only [ite_eq_left ha', ite_eq_right hb', Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · exact (Finset.mem_erase.mp (Q.subset b hy)).1 rfl
      · exact Finset.disjoint_left.mp (Q.disjoint hab) hx hy
    · simp only [ite_eq_right ha', ite_eq_left hb', Finset.mem_insert] at hx hy
      rcases hy with rfl | hy
      · exact (Finset.mem_erase.mp (Q.subset a hx)).1 rfl
      · exact Finset.disjoint_left.mp (Q.disjoint hab) hx hy
    · simp only [ite_eq_right ha', ite_eq_right hb'] at hx hy
      exact Finset.disjoint_left.mp (Q.disjoint hab) hx hy
  · intro x hx
    by_cases hxe : x = e
    · subst x
      exact ⟨a₀, by simp⟩
    · obtain ⟨a, ha'⟩ := Q.covers x (Finset.mem_erase.mpr ⟨hxe, hx⟩)
      refine ⟨a, ?_⟩
      split_ifs
      · exact Finset.mem_insert_of_mem ha'
      · exact ha'

end RankPartition

/-- Finite matroid partition, proved directly from finite rank axioms. -/
theorem exists_rankPartition {ι α : Type*} [DecidableEq ι] [Fintype α]
    (E : Finset ι) (r : α → FiniteRank ι)
    (h : ∀ S ⊆ E, S.card ≤ ∑ a, r a S) : Nonempty (RankPartition r E) := by
  classical
  induction E using Finset.strongInductionOn generalizing r with
  | _ E ih =>
    by_cases hE : E = ∅
    · subst E
      exact ⟨{
        parts := fun _ => ∅
        subset := by simp
        independent := by simp
        disjoint := by simp [Pairwise]
        covers := by simp
      }⟩
    by_cases htight : ∃ A : Finset ι, A.Nonempty ∧ A ⊂ E ∧ A.card = ∑ a, r a A
    · obtain ⟨A, hAn, hAE, hA⟩ := htight
      obtain ⟨P⟩ := ih A hAE r (fun S hS => h S (hS.trans hAE.subset))
      have hEA : (E \ A).card < E.card := by
        have hh := Finset.card_sdiff_add_card_eq_card hAE.subset
        have hp := Finset.card_pos.mpr hAn
        omega
      have hcontract : ∀ S ⊆ E \ A, S.card ≤ ∑ a, (r a).contract A S := by
        intro S hS
        have hd : Disjoint S A := by
          apply Finset.disjoint_left.mpr
          intro e he ha
          exact (Finset.mem_sdiff.mp (hS he)).2 ha
        have hU := h (S ∪ A) (Finset.union_subset
          (fun _ he => (Finset.mem_sdiff.mp (hS he)).1) hAE.subset)
        rw [Finset.card_union_of_disjoint hd] at hU
        have hr : (∑ a, (r a).contract A S) + ∑ a, r a A = ∑ a, r a (S ∪ A) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun a _ => (r a).contract_add A S)
        omega
      obtain ⟨Q⟩ := ih (E \ A) (Finset.sdiff_ssubset hAE.subset hAn) _ hcontract
      exact ⟨P.glue hAE.subset hA Q⟩
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hE
      have hsing := h {e} (Finset.singleton_subset_iff.mpr he)
      have hex : ∃ a, r a {e} = 1 := by
        by_contra hn
        push Not at hn
        have hz (a : α) : r a {e} = 0 := by
          have hh := (r a).card_le {e}
          simp only [Finset.card_singleton] at hh
          have := hn a
          omega
        simp only [hz, Finset.sum_const_zero, Finset.card_singleton] at hsing
        omega
      obtain ⟨a₀, ha₀⟩ := hex
      let r' := RankPartition.contractOne r a₀ e
      have h' : ∀ S ⊆ E.erase e, S.card ≤ ∑ a, r' a S := by
        intro S hS
        by_cases hSe : S = ∅
        · subst S; simp
        have hSE : S ⊂ E := by
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨hS.trans (Finset.erase_subset e E), ?_⟩
          intro heq
          have hh := hS (heq.symm ▸ he)
          exact (Finset.mem_erase.mp hh).1 rfl
        have hlt : S.card < ∑ a, r a S := by
          have hle := h S hSE.subset
          have hn : S.card ≠ ∑ a, r a S := by
            intro hh
            exact htight ⟨S, Finset.nonempty_iff_ne_empty.mpr hSe, hSE, hh⟩
          omega
        have hsum : (∑ a, r a S) ≤ (∑ a, r' a S) + 1 := by
          calc
            _ ≤ ∑ a, (r' a S + if a = a₀ then 1 else 0) := by
              apply Finset.sum_le_sum
              intro a _
              by_cases haa : a = a₀
              · subst a
                simpa [r', RankPartition.contractOne, ha₀] using (r a₀).le_contract_add {e} S
              · simp only [r', RankPartition.contractOne, ite_eq_right haa, add_zero]
                exact le_rfl
            _ = _ := by simp [Finset.sum_add_distrib]
        omega
      obtain ⟨Q⟩ := ih (E.erase e) (Finset.erase_ssubset he) r' h'
      exact ⟨RankPartition.addSingleton e he a₀ ha₀ Q⟩

/-- Packing from the rank-defect inequalities, by one extra uniform-rank color. -/
theorem FiniteRank.exists_disjoint_bases {ι : Type*} [DecidableEq ι]
    (r : FiniteRank ι) (E : Finset ι) (k R : ℕ) (hr : r E = k)
    (h : ∀ T ⊆ E, R * (k - r (E \ T)) ≤ T.card) :
    ∃ I : Fin R → Finset ι, (∀ a, I a ⊆ E) ∧
      (∀ a, r (I a) = (I a).card) ∧
      Pairwise (fun a b => Disjoint (I a) (I b)) ∧ (∀ a, (I a).card = k) := by
  classical
  have hn : R * k ≤ E.card := by simpa using h E (Finset.Subset.refl E)
  let q := E.card - R * k
  let rs : Option (Fin R) → FiniteRank ι := fun a =>
    match a with
    | none => FiniteRank.uniform q
    | some _ => r
  have hh : ∀ S ⊆ E, S.card ≤ ∑ a, rs a S := by
    intro S hS
    have hT := h (E \ S) Finset.sdiff_subset
    have hcomp : E \ (E \ S) = S := by
      ext e
      simp only [Finset.mem_sdiff]
      constructor
      · tauto
      · exact fun he => ⟨hS he, by tauto⟩
    rw [hcomp] at hT
    have hcard := Finset.card_sdiff_add_card_eq_card hS
    have hle : r S ≤ k := hr ▸ r.mono hS
    have hmul : R * (k - r S) + R * r S = R * k := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hle]
    have hbound : S.card ≤ R * r S + q := by
      dsimp [q]
      omega
    simpa [rs, Fintype.sum_option, Finset.sum_const, Nat.mul_comm] using
      (show S.card ≤ min S.card q + R * r S from by omega)
  obtain ⟨P⟩ := exists_rankPartition E rs hh
  let I : Fin R → Finset ι := fun a => P.parts (some a)
  have hle (a : Fin R) : (I a).card ≤ k := by
    have hi := P.independent (some a)
    change r (I a) = (I a).card at hi
    rw [← hi]
    exact hr ▸ r.mono (P.subset (some a))
  have hnone : (P.parts none).card ≤ q := by
    have hi := P.independent none
    change min (P.parts none).card q = (P.parts none).card at hi
    omega
  have hsum : (P.parts none).card + ∑ a, (I a).card = E.card := by
    simpa [Fintype.sum_option, I] using P.sum_card
  have hsle : (∑ a, (I a).card) ≤ R * k := by
    calc
      _ ≤ ∑ _a : Fin R, k := Finset.sum_le_sum (fun a _ => hle a)
      _ = _ := by simp
  have hseq : (∑ a, (I a).card) = ∑ _a : Fin R, k := by
    have hconst : (∑ _a : Fin R, k) = R * k := by simp
    rw [hconst]
    dsimp [q] at hnone
    omega
  refine ⟨I, (fun a => P.subset (some a)), (fun a => P.independent (some a)), ?_, ?_⟩
  · intro a b hab
    exact P.disjoint (by simpa using hab)
  · intro a
    exact (Finset.sum_eq_sum_iff_of_le (fun b _ => hle b)).mp hseq a (Finset.mem_univ a)

end AdaptiveOrthogonalRigidity
