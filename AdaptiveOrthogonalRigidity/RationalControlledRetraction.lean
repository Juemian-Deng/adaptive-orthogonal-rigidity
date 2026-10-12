import AdaptiveOrthogonalRigidity.RationalControlledDescent
import AdaptiveOrthogonalRigidity.RationalControlledInput

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Applying a scalar linear map to the entries commutes with multiplication
by a matrix over its base field. -/
theorem scalar_retraction_matrix_mul_left {K L ι τ υ : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype τ] (ρ : L →ₗ[K] K) (A : Matrix ι τ K) (B : Matrix τ υ L) :
    (A.map (algebraMap K L) * B).map ρ = A * B.map ρ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, ← Algebra.smul_def,
    map_smul, smul_eq_mul]

theorem scalar_retraction_matrix_mul_right {K L ι τ υ : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype τ] (ρ : L →ₗ[K] K) (A : Matrix ι τ L) (B : Matrix τ υ K) :
    (A * B.map (algebraMap K L)).map ρ = A.map ρ * B := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, mul_comm (A _ _),
    ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm (B _ _)]

theorem scalar_retraction_mulVec_left {K L ι τ : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype τ] (ρ : L →ₗ[K] K) (A : Matrix ι τ K) (v : τ → L) :
    (fun i => ρ ((A.map (algebraMap K L)).mulVec v i)) = A.mulVec (fun j => ρ (v j)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, ← Algebra.smul_def,
    map_smul, smul_eq_mul]

theorem scalar_retraction_mulVec_right {K L ι τ : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype τ] (ρ : L →ₗ[K] K) (A : Matrix ι τ L) (v : τ → K) :
    (fun i => ρ (A.mulVec (fun j => algebraMap K L (v j)) i)) = (A.map ρ).mulVec v := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, mul_comm (A _ _),
    ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm (v _)]

/-- A base-field state operator forces the full embedded reachable sequence to
be defined over the base field once its output is, under the genuine input
Krylov independence hypothesis. This retains unobservable state modes. -/
theorem controlled_embedded_sequence_descends {K L ι σ τ : Type*}
    [Field K] [Field L] [Algebra K L]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ]
    (C : Matrix ι ι K) (V : Matrix ι τ K) (M : Matrix σ σ K)
    (X : Matrix ι σ L) (F : Matrix τ σ L)
    (hX : C.map (algebraMap K L) * X = X * M.map (algebraMap K L) +
      V.map (algebraMap K L) * F)
    (hI : LinearIndependent L (krylovColumns (Fintype.card σ)
      (C.map (algebraMap K L)) (V.map (algebraMap K L)).col))
    (l : σ → K) (u : τ → L) (z : ι → K)
    (hZ : X.mulVec (fun j => algebraMap K L (l j)) +
      (V.map (algebraMap K L)).mulVec u = fun i => algebraMap K L (z i)) :
    ∀ n : ℕ, ∃ w : ι → K,
      (fun i => algebraMap K L (w i)) =
        X.mulVec ((M.map (algebraMap K L) ^ n).mulVec (fun j => algebraMap K L (l j))) := by
  obtain ⟨ρ, hρ⟩ := exists_scalar_retraction K L
  let X₀ := X.map ρ
  let F₀ := F.map ρ
  let u₀ := fun j => ρ (u j)
  have hproj : C * X₀ = X₀ * M + V * F₀ := by
    have hh := congrArg (fun A => A.map ρ) hX
    rw [Matrix.map_add _ (map_add ρ)] at hh
    simpa only [scalar_retraction_matrix_mul_left,
      scalar_retraction_matrix_mul_right] using hh
  have hprojZ : X₀.mulVec l + V.mulVec u₀ = z := by
    funext i
    have hh := congrArg ρ (congrFun hZ i)
    have hl := congrFun (scalar_retraction_mulVec_left ρ V u) i
    have hr := congrFun (scalar_retraction_mulVec_right ρ X l) i
    simpa only [Pi.add_apply, map_add, hl, hr, hρ] using hh
  let D := X - X₀.map (algebraMap K L)
  let B := F - F₀.map (algebraMap K L)
  have hD : C.map (algebraMap K L) * D = D * M.map (algebraMap K L) +
      V.map (algebraMap K L) * B := by
    have hh := congrArg (fun A => A.map (algebraMap K L)) hproj
    rw [Matrix.map_add _ (map_add (algebraMap K L))] at hh
    simp only [Matrix.map_mul] at hh
    dsimp [D, B]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub, hX, hh]
    abel
  have hm (A : Matrix ι σ K) (v : σ → K) :
      (A.map (algebraMap K L)).mulVec (fun j => algebraMap K L (v j)) =
        fun i => algebraMap K L (A.mulVec v i) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  have hmV (A : Matrix ι τ K) (v : τ → K) :
      (A.map (algebraMap K L)).mulVec (fun j => algebraMap K L (v j)) =
        fun i => algebraMap K L (A.mulVec v i) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  have hinit : D.mulVec (fun j => algebraMap K L (l j)) =
      (V.map (algebraMap K L)).mulVec ((fun j => algebraMap K L (u₀ j)) - u) := by
    have hh : (X₀.map (algebraMap K L)).mulVec (fun j => algebraMap K L (l j)) +
        (V.map (algebraMap K L)).mulVec (fun j => algebraMap K L (u₀ j)) =
          fun i => algebraMap K L (z i) := by
      rw [hm, hmV]
      funext i
      simpa only [Pi.add_apply, map_add] using congrArg (algebraMap K L) (congrFun hprojZ i)
    dsimp [D]
    rw [Matrix.sub_mulVec, Matrix.mulVec_sub]
    have hh' := hZ.trans hh.symm
    exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using hh')
  have hzero : ∀ n : ℕ, D.mulVec
      ((M.map (algebraMap K L) ^ n).mulVec (fun j => algebraMap K L (l j))) = 0 := by
    intro n
    induction n with
    | zero =>
      simpa only [pow_zero, Matrix.one_mulVec] using
        controlled_state_eq_zero_of_eq_input _ D _ _ B hD hI _ _ hinit
    | succ n ih =>
      let v := (M.map (algebraMap K L) ^ n).mulVec (fun j => algebraMap K L (l j))
      have he : D.mulVec ((M.map (algebraMap K L)).mulVec v) =
          (V.map (algebraMap K L)).mulVec (-(B.mulVec v)) := by
        have hv : D.mulVec v = 0 := ih
        have hh := congrArg (fun A => A.mulVec v) hD
        simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero] at hh
        rw [Matrix.mulVec_neg]
        exact eq_neg_of_add_eq_zero_left hh.symm
      have hz := controlled_state_eq_zero_of_eq_input _ D _ _ B hD hI _ _ he
      simpa only [pow_succ', ← Matrix.mulVec_mulVec] using hz
  intro n
  refine ⟨X₀.mulVec ((M ^ n).mulVec l), ?_⟩
  have hp : (M.map (algebraMap K L) ^ n).mulVec (fun j => algebraMap K L (l j)) =
      fun j => algebraMap K L ((M ^ n).mulVec l j) := by
    rw [← Matrix.map_pow]
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  have hz := hzero n
  rw [hp] at hz ⊢
  dsimp [D] at hz
  rw [Matrix.sub_mulVec, hm] at hz
  exact (sub_eq_zero.mp hz).symm

end AdaptiveOrthogonalRigidity
