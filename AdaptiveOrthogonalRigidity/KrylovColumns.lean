import AdaptiveOrthogonalRigidity.PolynomialSeedUnion

open Matrix Polynomial
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Actual columns V, MV, ..., M^d V, indexed by power and seed label. -/
def krylovColumns {K ι τ : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d : ℕ) (M : Matrix ι ι K) (V : τ → ι → K) : Fin (d + 1) × τ → ι → K :=
  fun ij => (M ^ ij.1.val).mulVec (V ij.2)

theorem aeval_lowF3Polynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (M : Matrix ι ι (ZMod 3)) (q : LowF3Polynomial d) :
    Polynomial.aeval M q.val = ∑ k : Fin (d + 1), q.val.coeff k.val • M ^ k.val := by
  rw [Polynomial.aeval_eq_sum_range' (n := d + 1) (by have := lowF3Polynomial_degree q; omega)]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

theorem krylov_combination_identity {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ]
    (d : ℕ) (M : Matrix ι ι (ZMod 3)) (V : τ → ι → ZMod 3) (q : τ → LowF3Polynomial d) :
    (∑ ij : Fin (d + 1) × τ, (q ij.2).val.coeff ij.1.val • krylovColumns d M V ij) =
      ∑ j, (Polynomial.aeval M (q j).val).mulVec (V j) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [aeval_lowF3Polynomial]
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, krylovColumns]

/-- Exact deterministic equivalence between actual Krylov column dependence
and a nonzero tuple of bounded-degree polynomials. -/
theorem krylov_dependent_iff_polynomial_relation {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] (d : ℕ) (M : Matrix ι ι (ZMod 3)) (V : τ → ι → ZMod 3) :
    ¬ LinearIndependent (ZMod 3) (krylovColumns d M V) ↔
      ∃ q : τ → LowF3Polynomial d, (∃ j, (q j).val ≠ 0) ∧
        ∑ j, (Polynomial.aeval M (q j).val).mulVec (V j) = 0 := by
  constructor
  · intro h
    obtain ⟨c, hc, ij, hij⟩ := Fintype.not_linearIndependent_iff.mp h
    let q : τ → LowF3Polynomial d := fun j =>
      (Polynomial.degreeLTEquiv (ZMod 3) (d + 1)).symm (fun k => c (k, j))
    have hcoeff (j : τ) (k : Fin (d + 1)) : (q j).val.coeff k.val = c (k, j) :=
      congrFun ((Polynomial.degreeLTEquiv (ZMod 3) (d + 1)).apply_symm_apply (fun k => c (k, j))) k
    refine ⟨q, ⟨ij.2, ?_⟩, ?_⟩
    · intro hz
      have ht := hcoeff ij.2 ij.1
      rw [hz, Polynomial.coeff_zero] at ht
      exact hij ht.symm
    · rw [← krylov_combination_identity d M V q]
      simpa only [hcoeff] using hc
  · rintro ⟨q, ⟨j, hj⟩, hrel⟩
    let c : Fin (d + 1) × τ → ZMod 3 := fun ij => (q ij.2).val.coeff ij.1.val
    have hq : q j ≠ 0 := fun hz => hj (congrArg Subtype.val hz)
    have he : (Polynomial.degreeLTEquiv (ZMod 3) (d + 1)) (q j) ≠ 0 := by
      intro hz
      apply hq
      apply (Polynomial.degreeLTEquiv (ZMod 3) (d + 1)).injective
      simpa only [map_zero] using hz
    obtain ⟨k, hk⟩ := Function.ne_iff.mp he
    apply Fintype.not_linearIndependent_iff.mpr
    refine ⟨c, ?_, ⟨(k, j), hk⟩⟩
    exact (krylov_combination_identity d M V q).trans hrel

/-- Split the exact dependence into a genuinely random-seed relation or an
annihilator of the prescribed mark. -/
theorem marked_krylov_failure_split {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (d : ℕ) (M : Matrix ι ι (ZMod 3)) (v : ι → ZMod 3) (Y : ι × κ → Bool)
    (hdep : ¬ LinearIndependent (ZMod 3) (krylovColumns d M
      (fun j : Option κ => j.elim v (fun k => boolVector (fun i => Y (i, k)))))) :
    Y ∈ seedPolynomialFailure d M v ∨
      ∃ q : Polynomial (ZMod 3), q ≠ 0 ∧ q.natDegree ≤ d ∧ (Polynomial.aeval M q).mulVec v = 0 := by
  obtain ⟨q, hq, hrel⟩ := (krylov_dependent_iff_polynomial_relation d M _).mp hdep
  rw [Fintype.sum_option] at hrel
  simp only [Option.elim_none, Option.elim_some] at hrel
  by_cases hr : ∃ j : κ, (q (some j)).val ≠ 0
  · exact Or.inl ⟨q, hr, hrel⟩
  · have hz (j : κ) : (q (some j)).val = 0 := by by_contra h; exact hr ⟨j, h⟩
    have hn : (q none).val ≠ 0 := by
      obtain ⟨j, hj⟩ := hq
      cases j with
      | none => exact hj
      | some j => exact False.elim (hj (hz j))
    refine Or.inr ⟨(q none).val, hn, lowF3Polynomial_degree _, ?_⟩
    simpa only [hz, map_zero, Matrix.zero_mulVec, Finset.sum_const_zero, add_zero] using hrel

end AdaptiveOrthogonalRigidity
