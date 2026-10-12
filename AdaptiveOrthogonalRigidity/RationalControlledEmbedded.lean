import AdaptiveOrthogonalRigidity.RationalControlledTrajectory
import AdaptiveOrthogonalRigidity.RationalControlledFilterDescent
import AdaptiveOrthogonalRigidity.RationalControlledDisjoint

open Matrix Polynomial
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- An annihilated embedded trajectory descends through its rational scalar
recurrence without taking any external-transfer quotient. -/
theorem annihilated_embedded_trajectory_descends {K L ι σ τ : Type*}
    [Field K] [Field L] [Algebra K L]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ]
    (d : ℕ) (C : Matrix ι ι K) (V : Matrix ι τ K)
    (X : Matrix ι σ L) (M : Matrix σ σ L) (F : Matrix τ σ L)
    (hX : C.map (algebraMap K L) * X = X * M + V.map (algebraMap K L) * F)
    (g : Polynomial K) (hg : g.Monic) (hgd : g.natDegree = d + 1)
    (l : σ → L) (u : τ → L) (z : ι → K)
    (hz : X.mulVec ((Polynomial.aeval M (g.map (algebraMap K L))).mulVec l) = 0)
    (hI : LinearIndependent L (krylovColumns (d + 1)
      (C.map (algebraMap K L)) (V.map (algebraMap K L)).col))
    (hZ : X.mulVec l + (V.map (algebraMap K L)).mulVec u = fun i => algebraMap K L (z i)) :
    ∀ j : Fin (d + 1), ∃ w : ι → K,
      (fun i => algebraMap K L (w i)) = X.mulVec ((M ^ j.val).mulVec l) := by
  let W := fun n : ℕ => X.mulVec ((M ^ n).mulVec l)
  let Q := fun n : ℕ => F.mulVec ((M ^ n).mulVec l)
  have hstep (j : ℕ) (_ : j ≤ d) :
      (C.map (algebraMap K L)).mulVec (W j) =
        W (j + 1) + (V.map (algebraMap K L)).mulVec (Q j) := by
    have hh := congrArg (fun A => A.mulVec ((M ^ j).mulVec l)) hX
    simpa only [W, Q, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, pow_succ'] using hh
  have hlast : W (d + 1) = -∑ j : Fin (d + 1),
      algebraMap K L (g.coeff j.val) • W j.val := by
    have he := hz
    rw [Polynomial.aeval_eq_sum_range' (n := d + 2)
      (by have := Polynomial.natDegree_map_le (p := g) (f := algebraMap K L); omega)] at he
    simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.mulVec_sum,
      Matrix.mulVec_smul, Polynomial.coeff_map] at he
    rw [Finset.sum_range_succ] at he
    have ht : g.coeff (d + 1) = 1 := by rw [← hgd]; exact hg.coeff_natDegree
    rw [ht, map_one, one_smul] at he
    rw [Fin.sum_univ_eq_sum_range (fun n => algebraMap K L (g.coeff n) • W n)]
    exact eq_neg_of_add_eq_zero_right he
  apply finite_embedded_trajectory_descends d C V (fun j => g.coeff j.val) W Q hstep hlast hI u z
  simpa only [W, pow_zero, Matrix.one_mulVec] using hZ

/-- Matrix polynomial evaluation commutes with the genuine scalar extension. -/
theorem controlled_aeval_matrix_map {K L ι : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι K) (p : Polynomial K) :
    (Polynomial.aeval C p).map (algebraMap K L) =
      Polynomial.aeval (C.map (algebraMap K L)) (p.map (algebraMap K L)) := by
  exact Polynomial.map_aeval_eq_aeval_map (φ := algebraMap K L)
    (ψ := (algebraMap K L).mapMatrix) (by
      ext a i j
      simp only [RingHom.comp_apply, Matrix.algebraMap_matrix_apply,
        RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.algebraMap_self]
      split_ifs <;> simp) p C

/-- Extending an existing filter uses only the field inclusion. -/
theorem controlled_polynomial_filter_map {K L ι τ υ : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype ι] [DecidableEq ι] [Fintype τ]
    (C : Matrix ι ι K) (V : Matrix ι τ K) (Z : Matrix ι υ K)
    (g : Polynomial K) (P : τ → υ → Polynomial K)
    (hf : ∀ j, (Polynomial.aeval C g).mulVec (Z.col j) =
      ∑ t, (Polynomial.aeval C (P t j)).mulVec (V.col t)) :
    ∀ j, (Polynomial.aeval (C.map (algebraMap K L)) (g.map (algebraMap K L))).mulVec
      ((Z.map (algebraMap K L)).col j) =
      ∑ t, (Polynomial.aeval (C.map (algebraMap K L)) ((P t j).map (algebraMap K L))).mulVec
        ((V.map (algebraMap K L)).col t) := by
  intro j
  funext i
  have hh := congrArg (algebraMap K L) (congrFun (hf j) i)
  simp only [Finset.sum_apply, map_sum, RingHom.map_mulVec, controlled_aeval_matrix_map] at hh
  have hzj : (Z.map (algebraMap K L)).col j = (algebraMap K L) ∘ Z.col j := by
    funext i
    rfl
  have hvt (t : τ) : (V.map (algebraMap K L)).col t = (algebraMap K L) ∘ V.col t := by
    funext i
    rfl
  simpa only [hzj, hvt, Finset.sum_apply] using hh

/-- Any actual bounded-degree polynomial input combination belongs to the
corresponding finite Krylov span. -/
theorem polynomial_input_combination_mem_krylov {K ι τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype τ]
    (k : ℕ) (C : Matrix ι ι K) (V : Matrix ι τ K)
    (P : τ → Polynomial K) (hP : ∀ t, (P t).natDegree ≤ k) :
    (∑ t, (Polynomial.aeval C (P t)).mulVec (V.col t)) ∈ controlledKrylovSpan k C V := by
  apply Submodule.sum_mem
  intro t _
  rw [Polynomial.aeval_eq_sum_range' (n := k + 1) (by have := hP t; omega), Matrix.sum_mulVec]
  apply Submodule.sum_mem
  intro a ha
  rw [Matrix.smul_mulVec]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(⟨a, Finset.mem_range.mp ha⟩, t), rfl⟩

/-- Restrict a genuine input-Krylov independence window to a shorter one. -/
theorem rational_krylov_independent_mono {K ι τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (C : Matrix ι ι K) (V : τ → ι → K)
    {a b : ℕ} (hab : a ≤ b) (hI : LinearIndependent K (krylovColumns b C V)) :
    LinearIndependent K (krylovColumns a C V) := by
  let f : Fin (a + 1) × τ → Fin (b + 1) × τ :=
    fun ij => (⟨ij.1.val, by have := ij.1.isLt; omega⟩, ij.2)
  have hf : Function.Injective f := by
    intro x y h
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun z => z.1.val) h
    · exact congrArg (fun z : Fin (b + 1) × τ => z.2) h
  exact hI.comp f hf

/-- Full embedded output columns in the original extension-field controlled
space descend to the base field. The state operator M is completely arbitrary
over the extension field, and no output columns are discarded. -/
theorem controlled_realization_embedded_columns_descend {K L ι σ τ υ : Type*}
    [Field K] [Field L] [Algebra K L]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ]
    (C : Matrix ι ι K) (V : Matrix ι τ K) (Z : Matrix ι υ K)
    (X : Matrix ι σ L) (M : Matrix σ σ L) (F : Matrix τ σ L)
    (L₀ : Matrix σ υ L) (G : Matrix τ υ L)
    (hX : C.map (algebraMap K L) * X = X * M + V.map (algebraMap K L) * F)
    (hZ : Z.map (algebraMap K L) = X * L₀ + V.map (algebraMap K L) * G)
    (hI : LinearIndependent L (krylovColumns (2 * Fintype.card σ)
      (C.map (algebraMap K L)) (V.map (algebraMap K L)).col)) :
    ∀ (a : Fin (Fintype.card σ)) (j : υ), ∃ w : ι → K,
      (fun i => algebraMap K L (w i)) = X.mulVec ((M ^ a.val).mulVec (L₀.col j)) := by
  obtain ⟨g₁, P₁, hg₁, hgd₁, hP₁, hf₁⟩ :=
    controlled_realization_monic_filter (C.map (algebraMap K L)) X M
      (V.map (algebraMap K L)) F L₀ G hX
  have hf₁' : ∀ j, (Polynomial.aeval (C.map (algebraMap K L)) g₁).mulVec
      ((Z.map (algebraMap K L)).col j) =
      ∑ t, (Polynomial.aeval (C.map (algebraMap K L)) (P₁ t j)).mulVec
        ((V.map (algebraMap K L)).col t) := by
    intro j
    rw [hZ]
    exact hf₁ j
  obtain ⟨g, P, hg, hgd, hP, hf⟩ :=
    monic_polynomial_filter_descent (Fintype.card σ) C V Z g₁ P₁ hg₁ hgd₁ hP₁ hf₁'
  have hmap := controlled_polynomial_filter_map (L := L) C V Z g P hf
  have hgdmap : (g.map (algebraMap K L)).natDegree ≤ Fintype.card σ :=
    Polynomial.natDegree_map_le.trans hgd.le
  have hann (j : υ) : X.mulVec
      ((Polynomial.aeval M (g.map (algebraMap K L))).mulVec (L₀.col j)) = 0 := by
    apply controlled_filter_annihilates_embedded_state (C.map (algebraMap K L)) X M
      (V.map (algebraMap K L)) F hX hI (g.map (algebraMap K L)) hgdmap (L₀.col j) (G.col j)
    have hj := hmap j
    rw [hZ] at hj
    rw [show X.mulVec (L₀.col j) + (V.map (algebraMap K L)).mulVec (G.col j) =
      (X * L₀ + V.map (algebraMap K L) * G).col j from rfl, hj]
    exact polynomial_input_combination_mem_krylov (Fintype.card σ)
      (C.map (algebraMap K L)) (V.map (algebraMap K L))
      (fun t => (P t j).map (algebraMap K L))
      (fun t => Polynomial.natDegree_map_le.trans (hP t j))
  have hinit (j : υ) : X.mulVec (L₀.col j) +
      (V.map (algebraMap K L)).mulVec (G.col j) = fun i => algebraMap K L (Z i j) := by
    funext i
    exact (congrFun (congrFun hZ i) j).symm
  intro a j
  have hkpos : 0 < Fintype.card σ := Nat.zero_lt_of_lt a.isLt
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
  have hi : LinearIndependent L (krylovColumns (d + 1)
      (C.map (algebraMap K L)) (V.map (algebraMap K L)).col) :=
    rational_krylov_independent_mono _ _ (by omega) hI
  have hh := annihilated_embedded_trajectory_descends d C V X M F hX g hg
    (hgd.trans hd) (L₀.col j) (G.col j) (Z.col j) (hann j) hi (hinit j)
  exact hh ⟨a.val, by have := a.isLt; omega⟩

end AdaptiveOrthogonalRigidity
