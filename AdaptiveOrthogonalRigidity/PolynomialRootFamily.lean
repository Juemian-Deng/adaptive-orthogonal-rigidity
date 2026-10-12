import AdaptiveOrthogonalRigidity.FiniteBounds
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev MonicF3Degree (a : ℕ) := {p : Polynomial (ZMod 3) // p.Monic ∧ p.natDegree = a}

noncomputable def monicF3Coefficients (a : ℕ) : MonicF3Degree a ≃ (Fin a → ZMod 3) :=
  (Polynomial.monicEquivDegreeLT a).trans (Polynomial.degreeLTEquiv (ZMod 3) a).toEquiv

noncomputable instance monicF3DegreeFintype (a : ℕ) : Fintype (MonicF3Degree a) :=
  Fintype.ofEquiv (Fin a → ZMod 3) (monicF3Coefficients a).symm

theorem monicF3Degree_card (a : ℕ) : Fintype.card (MonicF3Degree a) = 3 ^ a := by
  rw [Fintype.card_congr (monicF3Coefficients a)]
  simp

/-- All roots to be tested are chosen from the coefficient field before any
random matrix is exposed. Repeated roots and overlaps are counted only once. -/
noncomputable def lowDegreeRoots {K : Type*} [Field K] (f : ZMod 3 →+* K) (d : ℕ) : Finset K :=
  (Finset.Icc 1 d).biUnion fun a => Finset.univ.biUnion fun p : MonicF3Degree a =>
    (p.val.map f).roots.toFinset

theorem lowDegreeRoots_card {K : Type*} [Field K] (f : ZMod 3 →+* K) (d : ℕ) :
    (lowDegreeRoots f d).card ≤ rootCount d := by
  unfold lowDegreeRoots rootCount
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun a _ => ?_)
  calc
    _ ≤ ∑ p : MonicF3Degree a, (p.val.map f).roots.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _p : MonicF3Degree a, a := Finset.sum_le_sum (fun p _ =>
      (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans_eq
        ((Polynomial.natDegree_map f).trans p.property.2)))
    _ = a * 3 ^ a := by simp [monicF3Degree_card, Nat.mul_comm]

theorem mem_lowDegreeRoots {K : Type*} [Field K] (f : ZMod 3 →+* K) (d : ℕ)
    (p : Polynomial (ZMod 3)) (hp : p ≠ 0) (hdeg : p.natDegree ≤ d)
    {c : K} (hc : c ∈ (p.map f).roots) : c ∈ lowDegreeRoots f d := by
  have hpos : 0 < p.natDegree := by
    by_contra h
    have hz : p.natDegree = 0 := by omega
    rw [Polynomial.eq_C_of_natDegree_eq_zero hz, Polynomial.map_C, Polynomial.roots_C] at hc
    exact Multiset.notMem_zero c hc
  refine Finset.mem_biUnion.mpr ⟨p.natDegree, Finset.mem_Icc.mpr ⟨hpos, hdeg⟩, ?_⟩
  refine Finset.mem_biUnion.mpr ⟨⟨normalize p, Polynomial.monic_normalize hp,
    Polynomial.natDegree_normalize⟩, Finset.mem_univ _, ?_⟩
  simpa only [Polynomial.map_normalize, Polynomial.roots_normalize, Multiset.mem_toFinset] using hc

end AdaptiveOrthogonalRigidity
