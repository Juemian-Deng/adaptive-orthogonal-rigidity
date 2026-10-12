import AdaptiveOrthogonalRigidity.FieldGraphAlgebra

open Polynomial
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- The polynomial multiplying the fresh star in the top coordinates of B^k v.
Its coefficients may depend on B; they will be enumerated, never conditioned on. -/
noncomputable def starOrbitPolynomial {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : Module.End K (V × K)) (v : V × K) : ℕ → Polynomial K
  | 0 => 0
  | k + 1 => X * starOrbitPolynomial B v k + C (((B ^ k) v).2)

theorem starOrbitPolynomial_monic {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : Module.End K (V × K)) (v : V × K) (hv : v.2 = 1) (k : ℕ) :
    (starOrbitPolynomial B v (k + 1)).Monic ∧ (starOrbitPolynomial B v (k + 1)).natDegree = k := by
  induction k with
  | zero => simp [starOrbitPolynomial, hv]
  | succ k ih =>
    have hm := Polynomial.monic_X.mul ih.1
    have hd : (X * starOrbitPolynomial B v (k + 1)).natDegree = k + 1 := by
      rw [Polynomial.natDegree_X_mul ih.1.ne_zero, ih.2]
    have hlt : (C (((B ^ (k + 1)) v).2)).degree <
        (X * starOrbitPolynomial B v (k + 1)).degree := by
      rw [Polynomial.degree_eq_natDegree hm.ne_zero, hd]
      exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast Nat.zero_lt_succ k)
    exact ⟨hm.add_of_left hlt, (Polynomial.natDegree_add_eq_left_of_degree_lt hlt).trans hd⟩

theorem starOrbitPolynomial_degree_lt {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : Module.End K (V × K)) (v : V × K) (hv : v.2 = 1) (k : ℕ) :
    (starOrbitPolynomial B v k).degree < (k : WithBot ℕ) := by
  cases k with
  | zero => simp [starOrbitPolynomial]
  | succ k =>
    have h := starOrbitPolynomial_monic B v hv k
    rw [Polynomial.degree_eq_natDegree h.1.ne_zero, h.2]
    exact_mod_cast Nat.lt_succ_self k

/-- Deterministic star recurrence, expressed through a polynomial in the old
principal operator. Only the top-row block identity is used. -/
theorem star_orbit_identity {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A : Module.End K V) (B : Module.End K (V × K)) (x : V)
    (hB : ∀ w, (B w).1 = A w.1 + w.2 • x) (v : V × K) (k : ℕ) :
    ((B ^ k) v).1 = (A ^ k) v.1 + (Polynomial.aeval A (starOrbitPolynomial B v k)) x := by
  induction k with
  | zero => simp [starOrbitPolynomial]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, hB, ih, starOrbitPolynomial]
    simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
      pow_succ', Module.End.mul_apply, LinearMap.add_apply,
      Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    abel

end AdaptiveOrthogonalRigidity
