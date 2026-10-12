import AdaptiveOrthogonalRigidity.RationalControlledCompanion

open Matrix Polynomial
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

def controlledTrajectoryMatrix {K ι : Type*} (d : ℕ) (W : ℕ → ι → K) :
    Matrix ι (Fin (d + 1)) K := fun i j => W j.val i

/-- A finite embedded trajectory with a scalar recurrence is an actual
companion realization. Every trajectory vector stays in its original ambient
coordinate space. -/
theorem finite_trajectory_companion_realization {K ι τ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype τ]
    (d : ℕ) (C : Matrix ι ι K) (V : Matrix ι τ K)
    (a : Fin (d + 1) → K) (W : ℕ → ι → K) (Q : ℕ → τ → K)
    (hstep : ∀ j ≤ d, C.mulVec (W j) = W (j + 1) + V.mulVec (Q j))
    (hlast : W (d + 1) = -∑ j : Fin (d + 1), a j • W j.val) :
    C * (controlledTrajectoryMatrix d W) =
      (controlledTrajectoryMatrix d W) * controlledCompanion d a +
        V * (controlledTrajectoryMatrix d Q) := by
  let WM : Matrix ι (Fin (d + 1)) K := fun i j => W j.val i
  have hc (j : Fin (d + 1)) : (C * WM).col j = C.mulVec (W j.val) := by
    funext i
    rfl
  have hq (j : Fin (d + 1)) : (V * (controlledTrajectoryMatrix d Q)).col j =
      V.mulVec (Q j.val) := by
    funext i
    rfl
  have ha (A B : Matrix ι (Fin (d + 1)) K) (j : Fin (d + 1)) :
      (A + B).col j = A.col j + B.col j := rfl
  have hcol : ∀ j : Fin (d + 1), (C * WM).col j =
      (WM * controlledCompanion d a + V * (controlledTrajectoryMatrix d Q)).col j := by
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [ha, hc, hq, mul_controlledCompanion_last]
      change C.mulVec (W d) = (-∑ j : Fin (d + 1), a j • W j.val) + V.mulVec (Q d)
      exact (hstep d le_rfl).trans (congrArg (fun w => w + V.mulVec (Q d)) hlast)
    · rw [ha, hc, hq, mul_controlledCompanion_castSucc]
      exact hstep j.val (by omega)
  ext i j
  exact congrFun (hcol j) i

/-- The embedded vectors of a finite trajectory are all rational/base-field
vectors when its scalar recurrence and output data are over that field. -/
theorem finite_embedded_trajectory_descends {K L ι τ : Type*}
    [Field K] [Field L] [Algebra K L]
    [Fintype ι] [DecidableEq ι] [Fintype τ]
    (d : ℕ) (C : Matrix ι ι K) (V : Matrix ι τ K)
    (a : Fin (d + 1) → K) (W : ℕ → ι → L) (Q : ℕ → τ → L)
    (hstep : ∀ j ≤ d, (C.map (algebraMap K L)).mulVec (W j) =
      W (j + 1) + (V.map (algebraMap K L)).mulVec (Q j))
    (hlast : W (d + 1) = -∑ j : Fin (d + 1), algebraMap K L (a j) • W j.val)
    (hI : LinearIndependent L (krylovColumns (d + 1)
      (C.map (algebraMap K L)) (V.map (algebraMap K L)).col))
    (u : τ → L) (z : ι → K)
    (hZ : W 0 + (V.map (algebraMap K L)).mulVec u = fun i => algebraMap K L (z i)) :
    ∀ j : Fin (d + 1), ∃ w : ι → K, (fun i => algebraMap K L (w i)) = W j.val := by
  let WM : Matrix ι (Fin (d + 1)) L := fun i j => W j.val i
  let QM : Matrix τ (Fin (d + 1)) L := fun t j => Q j.val t
  have hr : C.map (algebraMap K L) * WM = WM *
      (controlledCompanion d a).map (algebraMap K L) + V.map (algebraMap K L) * QM := by
    rw [controlledCompanion_map]
    exact finite_trajectory_companion_realization d _ _ _ W Q hstep hlast
  have hinit : WM.mulVec (fun j => algebraMap K L ((Pi.single (0 : Fin (d + 1)) (1 : K) : Fin (d + 1) → K) j)) +
      (V.map (algebraMap K L)).mulVec u = fun i => algebraMap K L (z i) := by
    have hs : (fun j => algebraMap K L ((Pi.single (0 : Fin (d + 1)) (1 : K) : Fin (d + 1) → K) j)) =
        Pi.single 0 1 := by
      funext j
      simp only [Pi.single_apply]
      split_ifs <;> simp
    rw [hs, Matrix.mulVec_single_one]
    exact hZ
  have hi : LinearIndependent L (krylovColumns (Fintype.card (Fin (d + 1)))
      (C.map (algebraMap K L)) (V.map (algebraMap K L)).col) := by
    rw [Fintype.card_fin]
    exact hI
  intro j
  obtain ⟨w, hw⟩ := controlled_embedded_sequence_descends C V (controlledCompanion d a)
    WM QM hr hi (Pi.single 0 1) u z hinit j.val
  refine ⟨w, ?_⟩
  have hs : (fun j => algebraMap K L ((Pi.single (0 : Fin (d + 1)) (1 : K) : Fin (d + 1) → K) j)) =
      Pi.single 0 1 := by
    funext j
    simp only [Pi.single_apply]
    split_ifs <;> simp
  rw [controlledCompanion_map, hs, controlledCompanion_pow_initial,
    Matrix.mulVec_single_one] at hw
  exact hw

end AdaptiveOrthogonalRigidity
