import AdaptiveOrthogonalRigidity.MarkedStarPolynomials

open Polynomial
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

noncomputable def starRelationPolynomial {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : Module.End K (V × K)) (v : V × K) (g : Polynomial K) : Polynomial K :=
  ∑ k ∈ Finset.range (g.natDegree + 1), g.coeff k • starOrbitPolynomial B v k

theorem star_relation_identity {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A : Module.End K V) (B : Module.End K (V × K)) (x : V)
    (hB : ∀ w, (B w).1 = A w.1 + w.2 • x) (v : V × K) (g : Polynomial K) :
    ((Polynomial.aeval B g) v).1 = (Polynomial.aeval A g) v.1 +
      (Polynomial.aeval A (starRelationPolynomial B v g)) x := by
  conv_lhs => rw [Polynomial.aeval_eq_sum_range]
  conv_rhs => lhs; rw [Polynomial.aeval_eq_sum_range]
  simp only [starRelationPolynomial, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, Prod.fst_sum, Prod.smul_fst]
  simp_rw [star_orbit_identity A B x hB v]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => smul_add _ _ _)

theorem starRelationPolynomial_monic {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : Module.End K (V × K)) (v : V × K) (hv : v.2 = 1)
    (g : Polynomial K) (hg : g.Monic) (hpos : 0 < g.natDegree) :
    (starRelationPolynomial B v g).Monic ∧
      (starRelationPolynomial B v g).natDegree = g.natDegree - 1 := by
  have hk : g.natDegree - 1 + 1 = g.natDegree := by omega
  have hlead := starOrbitPolynomial_monic B v hv (g.natDegree - 1)
  rw [hk] at hlead
  have hlt : (∑ k ∈ Finset.range g.natDegree, g.coeff k • starOrbitPolynomial B v k).degree <
      (starOrbitPolynomial B v g.natDegree).degree := by
    rw [Polynomial.degree_eq_natDegree hlead.1.ne_zero, hlead.2]
    apply (Polynomial.degree_sum_le _ _).trans_lt
    apply (Finset.sup_lt_iff (WithBot.bot_lt_coe (g.natDegree - 1))).mpr
    intro k hk'
    apply (Polynomial.degree_smul_le _ _).trans_lt
    have hkn : k ≤ g.natDegree - 1 := by have := Finset.mem_range.mp hk'; omega
    exact (starOrbitPolynomial_degree_lt B v hv k).trans_le (WithBot.coe_le_coe.mpr hkn)
  unfold starRelationPolynomial
  rw [Finset.sum_range_succ, hg.coeff_natDegree, one_smul]
  exact ⟨hlead.1.add_of_right hlt, (Polynomial.natDegree_add_eq_right_of_degree_lt hlt).trans hlead.2⟩

/-- A monic annihilator of the prescribed mark gives a monic fresh-star equation
of degree one less. Its potentially sample-dependent coefficients remain explicit. -/
theorem marked_star_equation {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A : Module.End K V) (B : Module.End K (V × K)) (x : V)
    (hB : ∀ w, (B w).1 = A w.1 + w.2 • x) (v : V × K) (hv : v.2 = 1)
    (g : Polynomial K) (hg : g.Monic) (hpos : 0 < g.natDegree)
    (hzero : (Polynomial.aeval B g) v = 0) :
    ∃ f : Polynomial K, f.Monic ∧ f.natDegree = g.natDegree - 1 ∧
      (Polynomial.aeval A g) v.1 + (Polynomial.aeval A f) x = 0 := by
  refine ⟨starRelationPolynomial B v g, (starRelationPolynomial_monic B v hv g hg hpos).1,
    (starRelationPolynomial_monic B v hv g hg hpos).2, ?_⟩
  rw [← star_relation_identity A B x hB v g, hzero]
  rfl

end AdaptiveOrthogonalRigidity
