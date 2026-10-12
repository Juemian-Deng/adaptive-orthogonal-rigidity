import AdaptiveOrthogonalRigidity.RationalControlledFilter
import AdaptiveOrthogonalRigidity.RationalControlledRealization

open Matrix Polynomial
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- A controlled realization with k state coordinates cannot meet the degree-k
input-Krylov span when the actual input columns are independent through 2k.
No independence or rationality of the state matrix X is assumed. -/
theorem controlled_realization_disjoint_krylov {K ι σ τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ]
    (C : Matrix ι ι K) (X : Matrix ι σ K) (M : Matrix σ σ K)
    (V : Matrix ι τ K) (F : Matrix τ σ K)
    (h : C * X = X * M + V * F)
    (hI : LinearIndependent K (krylovColumns (2 * Fintype.card σ) C V.col)) :
    Disjoint X.mulVecLin.range (controlledKrylovSpan (Fintype.card σ) C V) := by
  rw [Submodule.disjoint_def]
  intro w hw hK
  obtain ⟨v, rfl⟩ := hw
  let k := Fintype.card σ
  by_cases hk : k = 0
  · have : IsEmpty σ := Fintype.card_eq_zero_iff.mp hk
    change X.mulVec v = 0
    funext i
    simp [Matrix.mulVec, dotProduct]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  obtain ⟨q, hq, hrep⟩ := controlledKrylovSpan_polynomial_representation k C V _ hK
  have hm : (Polynomial.aeval C M.charpoly).mulVec (X.mulVec v) ∈
      controlledKrylovSpan (k - 1) C V := by
    have hh := controlled_polynomial_defect_mem_krylov (k - 1) C X M V F h
      M.charpoly (by rw [Matrix.charpoly_natDegree_eq_dim]; dsimp [k] at *; omega) v
    simpa only [M.aeval_self_charpoly, Matrix.mul_zero, sub_zero,
      Matrix.mulVec_mulVec] using hh
  obtain ⟨R, hR, hRrep⟩ := controlledKrylovSpan_polynomial_representation (k - 1) C V _ hm
  have hrel : ∑ t, (Polynomial.aeval C (M.charpoly * q t - R t)).mulVec (V.col t) = 0 := by
    simp only [map_sub, map_mul, Matrix.sub_mulVec, Finset.sum_sub_distrib,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sum, ← hrep, ← hRrep]
    exact sub_self _
  have hdeg (t : τ) : (M.charpoly * q t - R t).natDegree ≤ 2 * k := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply Polynomial.natDegree_mul_le.trans
      rw [Matrix.charpoly_natDegree_eq_dim]
      have := hq t
      dsimp [k] at *
      omega
    · have := hR t
      omega
  have heq := krylov_polynomial_relation_eq_zero (2 * k) C V.col hI _ hdeg hrel
  have hq0 (t : τ) : q t = 0 := by
    by_contra hqt
    have hp : M.charpoly * q t = R t := sub_eq_zero.mp (heq t)
    have hd := congrArg Polynomial.natDegree hp
    rw [Polynomial.natDegree_mul M.charpoly_monic.ne_zero hqt,
      Matrix.charpoly_natDegree_eq_dim] at hd
    have := hR t
    dsimp [k] at *
    omega
  rw [hrep]
  simp only [hq0, map_zero, Matrix.zero_mulVec, Finset.sum_const_zero]

/-- Any bounded-degree filter annihilates the embedded output state. The
intersection argument keeps state modes even if the external transfer cannot
observe them. -/
theorem controlled_filter_annihilates_embedded_state {K ι σ τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ]
    (C : Matrix ι ι K) (X : Matrix ι σ K) (M : Matrix σ σ K)
    (V : Matrix ι τ K) (F : Matrix τ σ K)
    (h : C * X = X * M + V * F)
    (hI : LinearIndependent K (krylovColumns (2 * Fintype.card σ) C V.col))
    (g : Polynomial K) (hg : g.natDegree ≤ Fintype.card σ)
    (l : σ → K) (u : τ → K)
    (hf : (Polynomial.aeval C g).mulVec (X.mulVec l + V.mulVec u) ∈
      controlledKrylovSpan (Fintype.card σ) C V) :
    X.mulVec ((Polynomial.aeval M g).mulVec l) = 0 := by
  let S := controlledKrylovSpan (Fintype.card σ) C V
  have hu : (Polynomial.aeval C g).mulVec (V.mulVec u) ∈ S := by
    rw [Polynomial.aeval_eq_sum_range' (n := Fintype.card σ + 1) (by omega),
      Matrix.sum_mulVec]
    apply Submodule.sum_mem
    intro a ha
    rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec]
    exact Submodule.smul_mem _ _
      (controlledKrylovSpan_pow_input_mem _ C V a (by have := Finset.mem_range.mp ha; omega) u)
  have hx : (Polynomial.aeval C g).mulVec (X.mulVec l) ∈ S := by
    rw [Matrix.mulVec_add] at hf
    exact (Submodule.add_mem_iff_left _ hu).mp hf
  have hd := controlled_polynomial_defect_mem_krylov (Fintype.card σ) C X M V F h g
    (by omega) l
  have he : X.mulVec ((Polynomial.aeval M g).mulVec l) ∈ S := by
    have := S.sub_mem hx hd
    simpa only [Matrix.sub_mulVec, Matrix.mulVec_mulVec, sub_sub_cancel] using this
  exact (Submodule.disjoint_def.mp (controlled_realization_disjoint_krylov C X M V F h hI))
    _ ⟨_, rfl⟩ he

end AdaptiveOrthogonalRigidity
