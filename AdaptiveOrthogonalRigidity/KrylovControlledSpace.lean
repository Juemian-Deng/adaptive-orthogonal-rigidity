import AdaptiveOrthogonalRigidity.RationalControlledFilter

open Matrix Polynomial
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

theorem krylov_independent_mono {K ι τ : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {a b : ℕ} (C : Matrix ι ι K) (V : τ → ι → K) (hab : a ≤ b)
    (hI : LinearIndependent K (krylovColumns b C V)) :
    LinearIndependent K (krylovColumns a C V) := by
  let f : Fin (a + 1) × τ → Fin (b + 1) × τ := fun ij =>
    (⟨ij.1.val, lt_of_lt_of_le ij.1.isLt (Nat.add_le_add_right hab 1)⟩, ij.2)
  have hf : Function.Injective f := by
    intro i j hij
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun z : Fin (b + 1) × τ => z.1.val) hij
    · exact congrArg (fun z : Fin (b + 1) × τ => z.2) hij
  exact hI.comp f hf

theorem krylov_span_polynomial_representation {K ι τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype τ] (d : ℕ) (C : Matrix ι ι K)
    (V : τ → ι → K) (x : ι → K)
    (hx : x ∈ Submodule.span K (Set.range (krylovColumns d C V))) :
    ∃ q : τ → Polynomial K, (∀ t, (q t).natDegree ≤ d) ∧
      ∑ t, (Polynomial.aeval C (q t)).mulVec (V t) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
  let q : τ → Polynomial.degreeLT K (d + 1) := fun t =>
    (Polynomial.degreeLTEquiv K (d + 1)).symm (fun j => c (j, t))
  have hcoeff (t : τ) (j : Fin (d + 1)) : (q t).val.coeff j.val = c (j, t) :=
    congrFun ((Polynomial.degreeLTEquiv K (d + 1)).apply_symm_apply (fun j => c (j, t))) j
  have hdeg (t : τ) : (q t).val.natDegree ≤ d := by
    apply Polynomial.natDegree_le_of_degree_le
    apply Polynomial.mem_degreeLE.mp
    have hle : Polynomial.degreeLT K (d + 1) ≤ Polynomial.degreeLE K (d : WithBot ℕ) :=
      le_of_eq (Polynomial.degreeLT_succ_eq_degreeLE)
    exact hle (q t).property
  refine ⟨fun t => (q t).val, hdeg, ?_⟩
  have heval (t : τ) : Polynomial.aeval C (q t).val =
      ∑ j : Fin (d + 1), c (j, t) • C ^ j.val := by
    rw [Polynomial.aeval_eq_sum_range' (n := d + 1) (by have := hdeg t; omega)]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    rw [hcoeff]
  rw [Fintype.sum_prod_type, Finset.sum_comm] at hc
  simpa only [heval, Matrix.sum_mulVec, Matrix.smul_mulVec, krylovColumns] using hc

/-- Multiplication by C cannot retain the highest coefficient inside a
controlled space with a uniform bounded Krylov expansion. -/
theorem controlled_krylov_top_coefficient_zero {K ι τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype τ] (d : ℕ) (C : Matrix ι ι K)
    (V : τ → ι → K) (H : Submodule K (ι → K))
    (hI : LinearIndependent K (krylovColumns (d + 1) C V))
    (hrep : ∀ x ∈ H, ∃ q : τ → Polynomial K, (∀ t, (q t).natDegree ≤ d) ∧
      ∑ t, (Polynomial.aeval C (q t)).mulVec (V t) = x)
    (hcontrol : ∀ x ∈ H, C.mulVec x ∈ H ⊔ Submodule.span K (Set.range V))
    (x : ι → K) (hx : x ∈ H) (q : τ → Polynomial K)
    (hq : ∀ t, (q t).natDegree ≤ d)
    (hqx : ∑ t, (Polynomial.aeval C (q t)).mulVec (V t) = x) :
    ∀ t, (q t).coeff d = 0 := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hcontrol x hx)
  obtain ⟨q', hq', hqy⟩ := hrep y hy
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hz
  let f : τ → Polynomial K := fun t => Polynomial.X * q t - q' t - Polynomial.C (c t)
  have hdegree (t : τ) : (f t).natDegree ≤ d + 1 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · exact Polynomial.natDegree_mul_le.trans (by simp only [Polynomial.natDegree_X]; have := hq t; omega)
      · exact (hq' t).trans (Nat.le_succ d)
    · simp only [Polynomial.natDegree_C]; omega
  have hrelation : ∑ t, (Polynomial.aeval C (f t)).mulVec (V t) = 0 := by
    simp only [f, map_sub, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, ← Matrix.mulVec_mulVec, Finset.sum_sub_distrib, ← Matrix.mulVec_sum]
    rw [hqx, hqy, hc, ← hyz]
    abel
  have hzero := krylov_polynomial_relation_eq_zero (d + 1) C V hI f hdegree hrelation
  intro t
  have hcq := congrArg (fun p : Polynomial K => p.coeff (d + 1)) (hzero t)
  have hq'top : (q' t).coeff (d + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (hq' t) (Nat.lt_succ_self d))
  simpa only [f, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_succ,
    Polynomial.coeff_zero, hq'top, sub_zero] using hcq

/-- No nonzero controlled space can lie in the low-degree part of an
independent Krylov family. This uses through power d+1, not a doubled window. -/
theorem controlled_krylov_space_eq_bot {K ι τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype τ] (d : ℕ) (C : Matrix ι ι K)
    (V : τ → ι → K) (H : Submodule K (ι → K))
    (hI : LinearIndependent K (krylovColumns (d + 1) C V))
    (hrep : ∀ x ∈ H, ∃ q : τ → Polynomial K, (∀ t, (q t).natDegree ≤ d) ∧
      ∑ t, (Polynomial.aeval C (q t)).mulVec (V t) = x)
    (hcontrol : ∀ x ∈ H, C.mulVec x ∈ H ⊔ Submodule.span K (Set.range V)) : H = ⊥ := by
  induction d with
  | zero =>
    apply le_antisymm
    · intro x hx
      obtain ⟨q, hq, hqx⟩ := hrep x hx
      have hcoeff := controlled_krylov_top_coefficient_zero 0 C V H hI hrep hcontrol x hx q hq hqx
      have hzero (t : τ) : q t = 0 := by
        rw [Polynomial.eq_C_of_natDegree_le_zero (hq t), hcoeff t, Polynomial.C_0]
      rw [← hqx]
      simp only [hzero, map_zero, Matrix.zero_mulVec, Finset.sum_const_zero, Submodule.zero_mem]
    · exact bot_le
  | succ d ih =>
    apply ih (krylov_independent_mono C V (Nat.le_succ (d + 1)) hI)
    intro x hx
    obtain ⟨q, hq, hqx⟩ := hrep x hx
    have hcoeff := controlled_krylov_top_coefficient_zero (d + 1) C V H hI hrep hcontrol x hx q hq hqx
    refine ⟨q, ?_, hqx⟩
    intro t
    by_contra hnot
    have heq : (q t).natDegree = d + 1 := by have := hq t; omega
    have hlead : (q t).leadingCoeff = 0 := by
      rw [← Polynomial.coeff_natDegree, heq, hcoeff t]
    have hzero : q t = 0 := Polynomial.leadingCoeff_eq_zero.mp hlead
    simp only [hzero, Polynomial.natDegree_zero] at hnot
    omega

end AdaptiveOrthogonalRigidity
