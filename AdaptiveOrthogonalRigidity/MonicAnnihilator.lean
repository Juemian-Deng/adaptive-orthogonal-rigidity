import AdaptiveOrthogonalRigidity.FieldGraphAlgebra
import Mathlib.Algebra.Polynomial.FieldDivision

open Polynomial
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Normalize a nonzero annihilating polynomial without changing its degree.
A nonzero mark rules out the constant case. -/
theorem exists_monic_annihilator {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (v : V) (hv : v ≠ 0) (q : Polynomial K) (hq : q ≠ 0)
    (hzero : (Polynomial.aeval T q) v = 0) :
    ∃ g : Polynomial K, g.Monic ∧ g.natDegree = q.natDegree ∧ 0 < g.natDegree ∧
      (Polynomial.aeval T g) v = 0 := by
  let g := normalize q
  have hg : g.Monic := Polynomial.monic_normalize hq
  have hd : g.natDegree = q.natDegree := Polynomial.natDegree_normalize
  have hz : (Polynomial.aeval T g) v = 0 := by
    dsimp [g]
    rw [normalize_apply, Polynomial.coe_normUnit_of_ne_zero hq, map_mul, Polynomial.aeval_C]
    simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, LinearMap.smul_apply, hzero, smul_zero]
  have hpos : 0 < g.natDegree := by
    by_contra h
    have hdeg : g.natDegree = 0 := by omega
    have he : g = 1 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
      have hc := hg.coeff_natDegree
      rw [hdeg] at hc
      rw [hc, Polynomial.C_1]
    rw [he, map_one, Module.End.one_apply] at hz
    exact hv hz
  exact ⟨g, hg, hd, hpos, hz⟩

end AdaptiveOrthogonalRigidity
