import AdaptiveOrthogonalRigidity.RegularDescriptor
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Matrix Polynomial
open scoped BigOperators Classical

noncomputable section
namespace AdaptiveOrthogonalRigidity

/-- Swapping the two polynomial variables interchanges their coefficients. -/
theorem pencil_swap_coeff_coeff {K : Type*} [CommRing K]
    (p : Polynomial (Polynomial K)) (a b : ℕ) :
    ((Polynomial.Bivariate.swap p).coeff a).coeff b = (p.coeff b).coeff a := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq]
  | monomial n p =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, coeff_add, hp, hq]
    | monomial m x =>
      rw [Polynomial.Bivariate.swap_monomial_monomial]
      by_cases hna : n = b <;> by_cases hma : m = a <;> simp [coeff_monomial, hna, hma]

/-- Every coefficient's inner degree is bounded by the swapped outer degree. -/
theorem pencil_coeff_natDegree_le_swap {K : Type*} [CommRing K]
    (p : Polynomial (Polynomial K)) (m : ℕ) :
    (p.coeff m).natDegree ≤ (Polynomial.Bivariate.swap p).natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [← pencil_swap_coeff_coeff]
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj, Polynomial.coeff_zero]

/-- Cofactors of an affine pencil have degree at most one less than its size. -/
theorem pencil_adjugate_natDegree_le {K : Type*} [CommRing K] (h : ℕ)
    (E M : Matrix (Fin (h+1)) (Fin (h+1)) K) (i j : Fin (h+1)) :
    (((Polynomial.X : Polynomial K) • E.map Polynomial.C + M.map Polynomial.C).adjugate i j).natDegree ≤ h := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  apply (Polynomial.natDegree_mul_le).trans
  have hd : (((Polynomial.X : Polynomial K) • E.map Polynomial.C + M.map Polynomial.C).submatrix
      j.succAbove i.succAbove).det.natDegree ≤ h := by
    have heq : ((Polynomial.X : Polynomial K) • E.map Polynomial.C + M.map Polynomial.C).submatrix
        j.succAbove i.succAbove =
        (Polynomial.X : Polynomial K) • (E.submatrix j.succAbove i.succAbove).map Polynomial.C +
          (M.submatrix j.succAbove i.succAbove).map Polynomial.C := by funext a b; rfl
    rw [heq]
    simpa using Polynomial.natDegree_det_X_add_C_le (E.submatrix j.succAbove i.succAbove)
      (M.submatrix j.succAbove i.succAbove)
  have hz : (((-1 : Polynomial K) ^ (j + i : ℕ))).natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa using (Polynomial.natDegree_pow_le (p := (-1 : Polynomial K)) (n := (j + i : ℕ)))
  simpa only [hz, zero_add] using hd

/-- An independent formal variable regularizes every square polynomial matrix. -/
def pencilShift {K : Type*} [CommRing K] {k : ℕ}
    (E M : Matrix (Fin k) (Fin k) K) : Matrix (Fin k) (Fin k) (Polynomial (Polynomial K)) :=
  (Polynomial.X : Polynomial (Polynomial K)) • 1 + (descriptorPencil E M).map Polynomial.C

theorem pencilShift_swap {K : Type*} [CommRing K] {k : ℕ}
    (E M : Matrix (Fin k) (Fin k) K) :
    (pencilShift E M).map Polynomial.Bivariate.swap =
      (Polynomial.X : Polynomial (Polynomial K)) • (E.map Polynomial.C).map Polynomial.C +
        ((Polynomial.X : Polynomial K) • (1 : Matrix (Fin k) (Fin k) (Polynomial K)) -
          M.map Polynomial.C).map Polynomial.C := by
  funext i j
  by_cases hij : i = j
  · subst j
    simp [pencilShift, descriptorPencil, Matrix.smul_apply, Matrix.map_apply, Matrix.add_apply,
      Matrix.sub_apply, Polynomial.Bivariate.swap_Y, Polynomial.Bivariate.swap_C,
      smul_eq_mul]
    ring
  · simp [pencilShift, descriptorPencil, Matrix.smul_apply, Matrix.map_apply, Matrix.add_apply,
      Matrix.sub_apply, hij, Polynomial.Bivariate.swap_C,
      smul_eq_mul]
    ring

theorem pencilShift_adjugate_coeff_degree {K : Type*} [CommRing K] (h : ℕ)
    (E M : Matrix (Fin (h+1)) (Fin (h+1)) K) (m : ℕ) (i j : Fin (h+1)) :
    (((pencilShift E M).adjugate i j).coeff m).natDegree ≤ h := by
  apply (pencil_coeff_natDegree_le_swap _ _).trans
  have hmap : Polynomial.Bivariate.swap ((pencilShift E M).adjugate i j) =
      ((pencilShift E M).map Polynomial.Bivariate.swap).adjugate i j := by
    exact congrFun (congrFun (Polynomial.Bivariate.swap.toRingHom.map_adjugate (pencilShift E M)) i) j
  rw [hmap, pencilShift_swap]
  exact pencil_adjugate_natDegree_le h (E.map Polynomial.C)
    ((Polynomial.X : Polynomial K) • 1 - M.map Polynomial.C) i j


/-- A singular affine square pencil has a nonzero polynomial right kernel of
coordinate degree strictly below its order. No invertibility of E is used. -/
theorem singular_pencil_short_kernel {K : Type*} [Field K] (k : ℕ)
    (E M : Matrix (Fin k) (Fin k) K) (hsing : (descriptorPencil E M).det = 0) :
    ∃ v : Fin k → Polynomial K, v ≠ 0 ∧ (∀ i, (v i).natDegree < k) ∧
      (descriptorPencil E M).mulVec v = 0 := by
  cases k with
  | zero => simp at hsing
  | succ h =>
    let A := descriptorPencil E M
    let P := pencilShift E M
    let Q := P.adjugate
    have hA : A.det = 0 := hsing
    have hP : P.det ≠ 0 := by
      intro hz
      have hh := Polynomial.leadingCoeff_det_X_one_add_C A
      change P.det.leadingCoeff = 1 at hh
      rw [hz, Polynomial.leadingCoeff_zero] at hh
      exact zero_ne_one hh
    have hQ : Q ≠ 0 := by
      intro hz
      have hh := Matrix.mul_adjugate P
      change P * Q = P.det • (1 : Matrix (Fin (h+1)) (Fin (h+1)) _) at hh
      rw [hz, Matrix.mul_zero] at hh
      have hd := congrFun (congrFun hh (0 : Fin (h+1))) (0 : Fin (h+1))
      have hdz : P.det = 0 := by simpa using hd.symm
      exact hP hdz
    have hex : ∃ m : ℕ, Q.map (fun p => p.coeff m) ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hQ
      funext i j
      apply Polynomial.ext
      intro m
      have hh := congrFun (congrFun (hn m) i) j
      simpa using hh
    let m := Nat.find hex
    let B := Q.map (fun p => p.coeff m)
    have hB : B ≠ 0 := Nat.find_spec hex
    have hprev : ∀ d < m, Q.map (fun p => p.coeff d) = 0 := by
      intro d hd
      exact not_not.mp (Nat.find_min hex hd)
    have hX : ∀ i j, ((Polynomial.X : Polynomial (Polynomial K)) * Q i j).coeff m = 0 := by
      intro i j
      cases hm : m with
      | zero => simp
      | succ d =>
        rw [Polynomial.coeff_X_mul]
        have hh := congrFun (congrFun (hprev d (by omega)) i) j
        simpa using hh
    have hcoef : ∀ i j, (A * B) i j = ((P * Q) i j).coeff m := by
      intro i j
      rw [Matrix.mul_apply, Matrix.mul_apply, Polynomial.finsetSum_coeff]
      apply Finset.sum_congr rfl
      intro l _
      change A i l * (Q l j).coeff m = ((pencilShift E M i l) * Q l j).coeff m
      by_cases hil : i = l
      · simp only [pencilShift, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
          Matrix.one_apply, hil, ite_true, smul_eq_mul, mul_one, add_mul,
          Polynomial.coeff_add, Polynomial.coeff_C_mul, hX, zero_add]
        rfl
      · simp only [pencilShift, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
          Matrix.one_apply, hil, ite_false, smul_eq_mul, mul_zero, zero_add, Polynomial.coeff_C_mul]
        rfl
    have hAB : A * B = P.det.coeff m • (1 : Matrix (Fin (h+1)) (Fin (h+1)) (Polynomial K)) := by
      funext i j
      rw [hcoef, Matrix.mul_adjugate]
      by_cases hij : i = j <;> simp [Matrix.smul_apply, hij, smul_eq_mul]
    have hd : P.det.coeff m = 0 := by
      have hh := congrArg Matrix.det hAB
      rw [Matrix.det_mul, hA, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hh
      exact (pow_eq_zero_iff (by omega : h+1 ≠ 0)).mp hh.symm
    have hAB0 : A * B = 0 := by simpa only [hd, zero_smul] using hAB
    obtain ⟨i, j, hij⟩ : ∃ i j, B i j ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hB (funext fun i => funext fun j => hn i j)
    refine ⟨fun i => B i j, ?_, ?_, ?_⟩
    · intro hv
      exact hij (congrFun hv i)
    · intro l
      exact Nat.lt_succ_of_le (pencilShift_adjugate_coeff_degree h E M m l j)
    · funext l
      exact congrFun (congrFun hAB0 l) j

end AdaptiveOrthogonalRigidity
