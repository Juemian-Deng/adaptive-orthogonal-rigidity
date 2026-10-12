import AdaptiveOrthogonalRigidity.RationalControlledDescent
import AdaptiveOrthogonalRigidity.RationalControlledRealization

open Matrix Polynomial
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Translate a bounded polynomial filter to its genuine finite coefficient
system, with every output column present. -/
theorem polynomial_filter_finite_coefficients {K ι τ υ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype τ]
    (k : ℕ) (C : Matrix ι ι K) (V : Matrix ι τ K) (Z : Matrix ι υ K)
    (g : Polynomial K) (P : τ → υ → Polynomial K)
    (hg : g.natDegree ≤ k) (hP : ∀ t j, (P t j).natDegree ≤ k)
    (hf : ∀ j, (Polynomial.aeval C g).mulVec (Z.col j) =
      ∑ t, (Polynomial.aeval C (P t j)).mulVec (V.col t)) :
    ∀ i j, (∑ a : Fin (k + 1), g.coeff a.val * (C ^ a.val * Z) i j) =
      ∑ a : Fin (k + 1), ∑ t, (C ^ a.val * V) i t * (P t j).coeff a.val := by
  have heval (q : Polynomial K) (hq : q.natDegree ≤ k) :
      Polynomial.aeval C q = ∑ a : Fin (k + 1), q.coeff a.val • C ^ a.val := by
    rw [Polynomial.aeval_eq_sum_range' (n := k + 1) (by omega)]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  intro i j
  have hh := congrFun (hf j) i
  simp only [heval g hg, heval _ (hP _ _), Matrix.sum_mulVec, Matrix.smul_mulVec,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hh
  rw [Finset.sum_comm] at hh
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col_apply,
    mul_comm ((P _ _).coeff _)] using hh

/-- Reassemble a bounded coefficient filter as a polynomial filter. -/
theorem polynomial_filter_of_finite_coefficients {K ι τ υ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype τ]
    (k : ℕ) (C : Matrix ι ι K) (V : Matrix ι τ K) (Z : Matrix ι υ K)
    (g : Polynomial K) (P : τ → υ → Polynomial K)
    (hg : g.natDegree ≤ k) (hP : ∀ t j, (P t j).natDegree ≤ k)
    (hf : ∀ i j, (∑ a : Fin (k + 1), g.coeff a.val * (C ^ a.val * Z) i j) =
      ∑ a : Fin (k + 1), ∑ t, (C ^ a.val * V) i t * (P t j).coeff a.val) :
    ∀ j, (Polynomial.aeval C g).mulVec (Z.col j) =
      ∑ t, (Polynomial.aeval C (P t j)).mulVec (V.col t) := by
  have heval (q : Polynomial K) (hq : q.natDegree ≤ k) :
      Polynomial.aeval C q = ∑ a : Fin (k + 1), q.coeff a.val • C ^ a.val := by
    rw [Polynomial.aeval_eq_sum_range' (n := k + 1) (by omega)]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  intro j
  funext i
  simp only [heval g hg, heval _ (hP _ _), Matrix.sum_mulVec, Matrix.smul_mulVec,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col_apply,
    mul_comm ((P _ _).coeff _)] using hf i j

/-- Bounded coefficient arrays give polynomials with exactly those
coefficients and no coefficients beyond the prescribed degree window. -/
theorem exists_polynomial_of_bounded_coefficients {K : Type*} [Field K]
    (k : ℕ) (a : Fin (k + 1) → K) :
    ∃ p : Polynomial K, p.natDegree ≤ k ∧ ∀ i : Fin (k + 1), p.coeff i.val = a i := by
  let p := (Polynomial.degreeLTEquiv K (k + 1)).symm a
  refine ⟨p.val, ?_, ?_⟩
  · apply Polynomial.natDegree_le_of_degree_le
    apply Polynomial.mem_degreeLE.mp
    have hh := p.property
    simpa only [Polynomial.degreeLT_succ_eq_degreeLE] using hh
  · exact fun i => congrFun ((Polynomial.degreeLTEquiv K (k + 1)).apply_symm_apply a) i

/-- Polynomial-filter solvability descends from a field extension while the
monic denominator degree and all output columns are preserved. -/
theorem monic_polynomial_filter_descent {K L ι τ υ : Type*}
    [Field K] [Field L] [Algebra K L]
    [Fintype ι] [DecidableEq ι] [Fintype τ]
    (k : ℕ) (C : Matrix ι ι K) (V : Matrix ι τ K) (Z : Matrix ι υ K)
    (g : Polynomial L) (P : τ → υ → Polynomial L)
    (hg : g.Monic) (hgd : g.natDegree = k)
    (hP : ∀ t j, (P t j).natDegree ≤ k)
    (hf : ∀ j, (Polynomial.aeval (C.map (algebraMap K L)) g).mulVec
      ((Z.map (algebraMap K L)).col j) =
      ∑ t, (Polynomial.aeval (C.map (algebraMap K L)) (P t j)).mulVec
        ((V.map (algebraMap K L)).col t)) :
    ∃ (g' : Polynomial K) (P' : τ → υ → Polynomial K),
      g'.Monic ∧ g'.natDegree = k ∧ (∀ t j, (P' t j).natDegree ≤ k) ∧
      ∀ j, (Polynomial.aeval C g').mulVec (Z.col j) =
        ∑ t, (Polynomial.aeval C (P' t j)).mulVec (V.col t) := by
  have hs := polynomial_filter_finite_coefficients k (C.map (algebraMap K L))
    (V.map (algebraMap K L)) (Z.map (algebraMap K L)) g P hgd.le hP hf
  have hp (a : ℕ) (D : Matrix ι υ K) :
      (C.map (algebraMap K L) ^ a * D.map (algebraMap K L)) =
        (C ^ a * D).map (algebraMap K L) := by
    rw [Matrix.map_mul, Matrix.map_pow]
  have hpV (a : ℕ) :
      (C.map (algebraMap K L) ^ a * V.map (algebraMap K L)) =
        (C ^ a * V).map (algebraMap K L) := by
    rw [Matrix.map_mul, Matrix.map_pow]
  simp only [hp, hpV, Matrix.map_apply] at hs
  obtain ⟨a, b, ha, hab⟩ := monic_filter_coefficients_descent k
    (fun a => C ^ a.val * Z) (fun a => C ^ a.val * V)
    (fun a => g.coeff a.val) (fun a t j => (P t j).coeff a.val)
    (by simpa only [Fin.val_last, ← hgd] using hg.coeff_natDegree) hs
  obtain ⟨g', hdeg, hc⟩ := exists_polynomial_of_bounded_coefficients k a
  choose P' hdegP hcP using fun t j =>
    exists_polynomial_of_bounded_coefficients k (fun a => b a t j)
  have htop : g'.coeff k = 1 := (hc (Fin.last k)).trans ha
  have hg' : g'.Monic := Polynomial.monic_of_natDegree_le_of_coeff_eq_one k hdeg htop
  have hgd' : g'.natDegree = k := le_antisymm hdeg
    (Polynomial.le_natDegree_of_ne_zero (by rw [htop]; exact one_ne_zero))
  refine ⟨g', P', hg', hgd', hdegP, ?_⟩
  apply polynomial_filter_of_finite_coefficients k C V Z g' P' hdeg hdegP
  simpa only [hc, hcP] using hab

end AdaptiveOrthogonalRigidity
