import AdaptiveOrthogonalRigidity.IntegralDescriptorBridge
import AdaptiveOrthogonalRigidity.PolynomialPencilKernel

open Matrix Polynomial
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Coefficient equations of the actual affine pencil, without any hypothesis
that its leading matrix is invertible. -/
theorem descriptor_pencil_kernel_coefficients {K σ : Type*} [Field K] [Fintype σ]
    (E M : Matrix σ σ K) (v : σ → Polynomial K)
    (hv : (descriptorPencil E M).mulVec v = 0) :
    M.mulVec (fun i => (v i).coeff 0) = 0 ∧
      ∀ n, E.mulVec (fun i => (v i).coeff n) =
        M.mulVec (fun i => (v i).coeff (n + 1)) := by
  constructor
  · funext i
    have hh := congrArg (fun p : Polynomial K => p.coeff 0) (congrFun hv i)
    simpa [descriptorPencil, Matrix.mulVec, dotProduct, sub_mul, mul_assoc,
      Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul] using hh
  · intro n
    funext i
    have hh := congrArg (fun p : Polynomial K => p.coeff (n + 1)) (congrFun hv i)
    simpa [descriptorPencil, Matrix.mulVec, dotProduct, sub_mul, mul_assoc,
      Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul,
      Finset.sum_sub_distrib, sub_eq_zero] using hh

/-- Columnwise control implies control of the actual matrix range. -/
theorem descriptor_range_controlled_of_columns {K ι σ τ : Type*} [Field K]
    [Fintype ι] [Fintype σ] [Fintype τ]
    (C : Matrix ι ι K) (W : Matrix ι σ K) (V : Matrix ι τ K)
    (h : ∀ j, C.mulVec (W.col j) ∈ W.mulVecLin.range ⊔ V.mulVecLin.range) :
    ∀ w ∈ W.mulVecLin.range,
      C.mulVec w ∈ W.mulVecLin.range ⊔ V.mulVecLin.range := by
  rintro w ⟨a, rfl⟩
  change C.mulVec (W.mulVec a) ∈ _
  rw [Matrix.mulVec_eq_sum a W, Matrix.mulVec_sum]
  apply Submodule.sum_mem
  intro j _
  simpa only [op_smul_eq_smul, Matrix.mulVec_smul, Matrix.col_def, Matrix.transpose_apply] using
    (W.mulVecLin.range ⊔ V.mulVecLin.range).smul_mem (a j) (h j)

/-- A short polynomial pencil kernel is impossible under genuine input-Krylov
independence and independence of the actual dynamic columns. The proof uses
the controlled span of its coefficient vectors, retaining singular E. -/
theorem descriptor_short_kernel_eq_zero {K ι τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype τ]
    (k : ℕ) (C : Matrix ι ι K) (X : Matrix ι (Fin k) K) (V : Matrix ι τ K)
    (E M : Matrix (Fin k) (Fin k) K) (F B : Matrix τ (Fin k) K)
    (hact : C * (X * E + V * F) = X * M + V * B)
    (hdyn : LinearIndependent K (X * E + V * F).col)
    (hI : LinearIndependent K (krylovColumns k C V.col))
    (v : Fin k → Polynomial K) (hdeg : ∀ i, (v i).natDegree < k)
    (hv : (descriptorPencil E M).mulVec v = 0) : v = 0 := by
  let U := X * E + V * F
  let c : ℕ → Fin k → K := fun n i => (v i).coeff n
  let W : Matrix ι (Fin k) K := fun i j => U.mulVec (c j.val) i
  obtain ⟨hzero, hsucc⟩ := descriptor_pencil_kernel_coefficients E M v hv
  have hstep (n : ℕ) : C.mulVec (U.mulVec (c n)) =
      X.mulVec (M.mulVec (c n)) + V.mulVec (B.mulVec (c n)) := by
    rw [Matrix.mulVec_mulVec, hact, Matrix.add_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hWmem (n : ℕ) (hn : n < k) : U.mulVec (c n) ∈ W.mulVecLin.range := by
    refine ⟨Pi.single (⟨n, hn⟩ : Fin k) 1, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
    rfl
  have hcontrol : ∀ w ∈ W.mulVecLin.range,
      C.mulVec w ∈ W.mulVecLin.range ⊔ V.mulVecLin.range := by
    apply descriptor_range_controlled_of_columns
    intro j
    change C.mulVec (U.mulVec (c j.val)) ∈ _
    rw [hstep]
    cases hn : j.val with
    | zero =>
      have hz : M.mulVec (c 0) = 0 := hzero
      rw [hz, Matrix.mulVec_zero, zero_add]
      exact Submodule.mem_sup_right ⟨_, rfl⟩
    | succ n =>
      have he : X.mulVec (M.mulVec (c (n + 1))) + V.mulVec (B.mulVec (c (n + 1))) =
          U.mulVec (c n) + V.mulVec (B.mulVec (c (n + 1)) - F.mulVec (c n)) := by
        rw [← hsucc]
        dsimp [U]
        rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          Matrix.mulVec_sub]
        abel
      rw [he]
      exact Submodule.add_mem_sup (hWmem n (by omega)) ⟨_, rfl⟩
  have hdim : Module.finrank K W.mulVecLin.range ≤ k := by
    simpa using W.mulVecLin.finrank_range_le
  have hdisj : Disjoint W.mulVecLin.range V.mulVecLin.range := by
    apply descriptor_controlled_space_disjoint_input C V (0 : Matrix ι (Fin 0) K)
      W.mulVecLin.range hcontrol
    · simp only [Matrix.mulVecLin_zero, LinearMap.range_zero]
      exact bot_le
    · exact rational_krylov_independent_mono _ _ hdim hI
  have hdown (n : ℕ) (hn : n < k) (hc : c (n + 1) = 0) : c n = 0 := by
    have hE : E.mulVec (c n) = 0 := by
      change E.mulVec (fun i => (v i).coeff n) = 0
      rw [hsucc]
      change M.mulVec (c (n + 1)) = 0
      rw [hc, Matrix.mulVec_zero]
    have hu : U.mulVec (c n) = V.mulVec (F.mulVec (c n)) := by
      dsimp [U]
      rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hE, Matrix.mulVec_zero, zero_add]
    have hz : U.mulVec (c n) = 0 :=
      Submodule.disjoint_def.mp hdisj _ (hWmem n hn) (hu ▸ ⟨_, rfl⟩)
    exact Matrix.mulVec_injective_iff.mpr hdyn (hz.trans (Matrix.mulVec_zero U).symm)
  have htop : c k = 0 := by
    funext i
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg i)
  have hall (n : ℕ) (hn : n ≤ k) : c n = 0 := by
    induction hn using Nat.decreasingInduction with
    | self => exact htop
    | of_succ n hn ih => exact hdown n hn ih
  funext i
  apply Polynomial.ext
  intro n
  by_cases hn : n ≤ k
  · exact congrFun (hall n hn) i
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hdeg i; omega)

/-- Genuine finite Krylov independence forces regularity of the descriptor
pencil; E is allowed to be singular. -/
theorem descriptor_regular_of_krylov {K ι τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype τ]
    (k : ℕ) (C : Matrix ι ι K) (X : Matrix ι (Fin k) K) (V : Matrix ι τ K)
    (E M : Matrix (Fin k) (Fin k) K) (F B : Matrix τ (Fin k) K)
    (hact : C * (X * E + V * F) = X * M + V * B)
    (hdyn : LinearIndependent K (X * E + V * F).col)
    (hI : LinearIndependent K (krylovColumns k C V.col)) : regularPencil E M := by
  intro hs
  obtain ⟨v, hv, hdeg, hker⟩ := singular_pencil_short_kernel k E M hs
  exact hv (descriptor_short_kernel_eq_zero k C X V E M F B hact hdyn hI v hdeg hker)

/-- Complete original-data real-to-F3 rational descent and regular modified
descriptor bridge. All output columns are retained and E may be singular. -/
theorem integer_real_regular_descriptor {ι τ υ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ] [Fintype υ]
    (C : Matrix ι ι ℤ) (V : Matrix ι τ ℤ) (Z : Matrix ι υ ℤ)
    (r : ℕ) (H : Submodule ℝ (ι → ℝ)) (hdim : Module.finrank ℝ H ≤ r)
    (hI : LinearIndependent (ZMod 3) (krylovColumns (2 * r)
      (C.map (Int.castRingHom (ZMod 3))) (V.map (Int.castRingHom (ZMod 3))).col))
    (hC : ∀ w ∈ H, (C.map (Int.castRingHom ℝ)).mulVec w ∈
      H ⊔ (V.map (Int.castRingHom ℝ)).mulVecLin.range)
    (hZ : (Z.map (Int.castRingHom ℝ)).mulVecLin.range ≤
      H ⊔ (V.map (Int.castRingHom ℝ)).mulVecLin.range) :
    ∃ (k : ℕ) (X : Matrix ι (Fin k) (ZMod 3))
      (E M : Matrix (Fin k) (Fin k) (ZMod 3)) (F B : Matrix τ (Fin k) (ZMod 3))
      (L₀ : Matrix (Fin k) υ (ZMod 3)) (G : Matrix τ υ (ZMod 3)),
      k ≤ r ∧
      C.map (Int.castRingHom (ZMod 3)) * (X * E + V.map (Int.castRingHom (ZMod 3)) * F) =
        X * M + V.map (Int.castRingHom (ZMod 3)) * B ∧
      Z.map (Int.castRingHom (ZMod 3)) = X * L₀ + V.map (Int.castRingHom (ZMod 3)) * G ∧
      LinearIndependent (ZMod 3) (Matrix.fromCols X (V.map (Int.castRingHom (ZMod 3)))).col ∧
      LinearIndependent (ZMod 3) (X * E + V.map (Int.castRingHom (ZMod 3)) * F).col ∧
      regularPencil E M := by
  obtain ⟨k, X, E, M, F, B, L₀, G, hk, hact, hout, hjoint, hdyn⟩ :=
    integer_real_controlled_descriptor_data C V Z r H hdim hI hC hZ
  refine ⟨k, X, E, M, F, B, L₀, G, hk, hact, hout, hjoint, hdyn, ?_⟩
  apply descriptor_regular_of_krylov k _ X _ E M F B hact hdyn
  exact rational_krylov_independent_mono _ _ (by omega) hI

end AdaptiveOrthogonalRigidity
