import AdaptiveOrthogonalRigidity.IntegralDescriptorConstruction
import AdaptiveOrthogonalRigidity.IntegerColumnLift

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The initial input block is included in every genuine Krylov window. -/
theorem descriptor_krylov_input_independent {K ι τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (d : ℕ) (C : Matrix ι ι K) (V : Matrix ι τ K)
    (hI : LinearIndependent K (krylovColumns d C V.col)) : LinearIndependent K V.col := by
  have hh := hI.comp (fun j : τ => ((0 : Fin (d + 1)), j)) (by
    intro i j h
    exact congrArg Prod.snd h)
  simpa only [Function.comp_def, krylovColumns, Fin.val_zero, pow_zero, Matrix.one_mulVec] using hh

/-- Genuine scalar extension of the actual power columns. -/
theorem descriptor_krylov_map {K L ι τ : Type*} [Field K] [Field L]
    [Fintype ι] [DecidableEq ι] (f : K →+* L)
    (d : ℕ) (C : Matrix ι ι K) (V : Matrix ι τ K) :
    krylovColumns d (C.map f) (V.map f).col =
      fun j => f ∘ krylovColumns d C V.col j := by
  funext j i
  dsimp [krylovColumns]
  rw [← Matrix.map_pow]
  exact (RingHom.map_mulVec f (C ^ j.1.val) (V.col j.2) i).symm

/-- A controlled space is disjoint from the actual input space once the
Krylov window reaches its dimension. -/
theorem descriptor_controlled_space_disjoint_input {K ι τ υ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype τ] [Fintype υ]
    (C : Matrix ι ι K) (V : Matrix ι τ K) (Z : Matrix ι υ K)
    (H : Submodule K (ι → K))
    (hC : ∀ w ∈ H, C.mulVec w ∈ H ⊔ V.mulVecLin.range)
    (hZ : Z.mulVecLin.range ≤ H ⊔ V.mulVecLin.range)
    (hI : LinearIndependent K (krylovColumns (Module.finrank K H) C V.col)) :
    Disjoint H V.mulVecLin.range := by
  obtain ⟨X, M, F, L₀, G, hX, hc, hz⟩ := controlled_subspace_realization C V Z H hC hZ
  have hi : LinearIndependent K (krylovColumns (Fintype.card (Fin (Module.finrank K H))) C V.col) := by
    rw [Fintype.card_fin]
    exact hI
  apply Submodule.disjoint_def.mpr
  intro w hw hv
  have hwX : w ∈ X.mulVecLin.range := hX.ge hw
  obtain ⟨v, rfl⟩ := hwX
  obtain ⟨u, hu⟩ := hv
  exact controlled_state_eq_zero_of_eq_input C X M V F hc hi v u hu.symm

/-- Rationalizing integer data and then including it into R gives exactly
its original real cast. -/
theorem descriptor_integer_rat_real {ι τ : Type*} (A : Matrix ι τ ℤ) :
    (A.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ) = A.map (Int.castRingHom ℝ) := by
  ext i j
  simp only [Matrix.map_apply, Int.coe_castRingHom]
  norm_cast

/-- The complete real-to-finite modified-descriptor construction apart from
pencil regularity, which is proved separately by the short polynomial-kernel
argument. No rational-space or reduction-rank assumption is added. -/
theorem integer_real_controlled_descriptor_data {ι τ υ : Type*}
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
      LinearIndependent (ZMod 3) (X * E + V.map (Int.castRingHom (ZMod 3)) * F).col := by
  have hIR : LinearIndependent ℝ (krylovColumns (2 * r)
      (C.map (Int.castRingHom ℝ)) (V.map (Int.castRingHom ℝ)).col) :=
    integer_krylov_real_independent (2 * r) C V.col hI
  have hIQ : LinearIndependent ℚ (krylovColumns (2 * r)
      (C.map (Int.castRingHom ℚ)) (V.map (Int.castRingHom ℚ)).col) := by
    apply (linearIndependent_algebraMap_comp_iff (S := ℝ)).mp
    rw [← descriptor_krylov_map, descriptor_integer_rat_real, descriptor_integer_rat_real]
    exact hIR
  have hIRC : LinearIndependent ℝ (krylovColumns (2 * r)
      ((C.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ))
      ((V.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ)).col) := by
    rw [descriptor_integer_rat_real, descriptor_integer_rat_real]
    exact hIR
  obtain ⟨S, hdimS, hSH, hSC, hSZ⟩ := rational_controlled_subspace_descent
    (C.map (Int.castRingHom ℚ)) (V.map (Int.castRingHom ℚ)) (Z.map (Int.castRingHom ℚ)) r H
    hdim hIRC (by simpa only [descriptor_integer_rat_real] using hC)
    (by simpa only [descriptor_integer_rat_real] using hZ)
  have hSdim : Module.finrank ℚ S ≤ r := hdimS.trans hdim
  have hIS : LinearIndependent ℚ (krylovColumns (Module.finrank ℚ S)
      (C.map (Int.castRingHom ℚ)) (V.map (Int.castRingHom ℚ)).col) :=
    rational_krylov_independent_mono _ _ (by omega) hIQ
  have hd := descriptor_controlled_space_disjoint_input
    (C.map (Int.castRingHom ℚ)) (V.map (Int.castRingHom ℚ)) (Z.map (Int.castRingHom ℚ)) S hSC hSZ hIS
  obtain ⟨k, X, E, M, F, B, L₀, G, hk, hact, hout, hjoint, hdyn⟩ :=
    integral_controlled_descriptor_data (K := ZMod 3) C V Z S hSC hSZ hd
      (descriptor_krylov_input_independent _ _ _ hIQ) (descriptor_krylov_input_independent _ _ _ hI)
  exact ⟨k, X, E, M, F, B, L₀, G, hk.trans_le hSdim, hact, hout, hjoint, hdyn⟩

end AdaptiveOrthogonalRigidity
