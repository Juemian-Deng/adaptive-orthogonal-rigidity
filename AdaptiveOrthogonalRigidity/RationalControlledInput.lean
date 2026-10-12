import AdaptiveOrthogonalRigidity.RationalControlledDisjoint

open Matrix Polynomial
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- A k-coordinate controlled state is disjoint from degree-d input Krylov
columns under actual independence through k+d. -/
theorem controlled_realization_disjoint_krylov_of_bounds {K ι σ τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ]
    (d : ℕ) (C : Matrix ι ι K) (X : Matrix ι σ K) (M : Matrix σ σ K)
    (V : Matrix ι τ K) (F : Matrix τ σ K)
    (h : C * X = X * M + V * F)
    (hI : LinearIndependent K (krylovColumns (Fintype.card σ + d) C V.col)) :
    Disjoint X.mulVecLin.range (controlledKrylovSpan d C V) := by
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
  obtain ⟨q, hq, hrep⟩ := controlledKrylovSpan_polynomial_representation d C V _ hK
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
  have hdeg (t : τ) : (M.charpoly * q t - R t).natDegree ≤ k + d := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply Polynomial.natDegree_mul_le.trans
      rw [Matrix.charpoly_natDegree_eq_dim]
      have := hq t
      dsimp [k] at *
      omega
    · have := hR t
      omega
  have heq := krylov_polynomial_relation_eq_zero (k + d) C V.col hI _ hdeg hrel
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


/-- A k-coordinate controlled state has zero intersection with the original
input span under independence of the first k+1 input blocks. -/
theorem controlled_state_eq_zero_of_eq_input {K ι σ τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ]
    (C : Matrix ι ι K) (X : Matrix ι σ K) (M : Matrix σ σ K)
    (V : Matrix ι τ K) (F : Matrix τ σ K)
    (h : C * X = X * M + V * F)
    (hI : LinearIndependent K (krylovColumns (Fintype.card σ) C V.col))
    (v : σ → K) (u : τ → K) (he : X.mulVec v = V.mulVec u) :
    X.mulVec v = 0 := by
  have hi : LinearIndependent K (krylovColumns (Fintype.card σ + 0) C V.col) := by
    simpa only [Nat.add_zero] using hI
  have hd := controlled_realization_disjoint_krylov_of_bounds 0 C X M V F h hi
  apply (Submodule.disjoint_def.mp hd) _ ⟨v, rfl⟩
  change X.mulVec v ∈ controlledKrylovSpan 0 C V
  rw [he]
  simpa only [pow_zero, Matrix.one_mul] using
    controlledKrylovSpan_pow_input_mem 0 C V 0 le_rfl u

end AdaptiveOrthogonalRigidity
