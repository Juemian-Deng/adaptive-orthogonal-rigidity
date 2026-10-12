import AdaptiveOrthogonalRigidity.RationalControlledRetraction

open Matrix Polynomial
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Companion matrix with shift columns followed by the negative recurrence
coefficients. The state dimension is `d+1`, so the initial state is available. -/
def controlledCompanion {K : Type*} [Ring K] (d : ℕ) (a : Fin (d + 1) → K) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) K :=
  fun i j => if h : j.val < d then
    if i = (⟨j.val, h⟩ : Fin d).succ then 1 else 0 else -a i

@[simp] theorem controlledCompanion_castSucc {K : Type*} [Ring K]
    (d : ℕ) (a : Fin (d + 1) → K) (i : Fin (d + 1)) (j : Fin d) :
    controlledCompanion d a i j.castSucc = if i = j.succ then 1 else 0 := by
  simp [controlledCompanion, j.isLt]

@[simp] theorem controlledCompanion_last {K : Type*} [Ring K]
    (d : ℕ) (a : Fin (d + 1) → K) (i : Fin (d + 1)) :
    controlledCompanion d a i (Fin.last d) = -a i := by
  simp [controlledCompanion]

@[simp] theorem controlledCompanion_map {K L : Type*} [Ring K] [Ring L]
    (f : K →+* L) (d : ℕ) (a : Fin (d + 1) → K) :
    (controlledCompanion d a).map f = controlledCompanion d (fun i => f (a i)) := by
  ext i j
  simp only [Matrix.map_apply, controlledCompanion]
  split_ifs <;> simp

@[simp] theorem controlledCompanion_mulVec_single {K : Type*} [Field K]
    (d : ℕ) (a : Fin (d + 1) → K) (j : Fin d) :
    (controlledCompanion d a).mulVec (Pi.single j.castSucc 1) = Pi.single j.succ 1 := by
  rw [Matrix.mulVec_single_one]
  funext i
  simp only [Pi.single_apply]
  split_ifs <;> simp_all

/-- The first d+1 iterates of the first coordinate are precisely the original
state coordinates; no unobservable-mode quotient is taken. -/
theorem controlledCompanion_pow_initial {K : Type*} [Field K]
    (d : ℕ) (a : Fin (d + 1) → K) (j : Fin (d + 1)) :
    (controlledCompanion d a ^ j.val).mulVec (Pi.single 0 1) = Pi.single j 1 := by
  have hn : ∀ n (hn : n < d + 1), (controlledCompanion d a ^ n).mulVec (Pi.single 0 1) =
      Pi.single (⟨n, hn⟩ : Fin (d + 1)) 1 := by
    intro n
    induction n with
    | zero => intro hn; simp only [pow_zero, Matrix.one_mulVec]; rfl
    | succ n ih =>
      intro hn
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih (by omega)]
      exact controlledCompanion_mulVec_single d a ⟨n, by omega⟩
  exact hn j.val j.isLt

/-- Multiplying an embedded state matrix by a companion shift advances an
original coordinate column. -/
theorem mul_controlledCompanion_castSucc {K ι : Type*} [Field K]
    (d : ℕ) (a : Fin (d + 1) → K) (W : Matrix ι (Fin (d + 1)) K) (j : Fin d) :
    (W * controlledCompanion d a).col j.castSucc = W.col j.succ := by
  funext i
  simp [Matrix.mul_apply, Matrix.col_apply, controlledCompanion_castSucc]

theorem mul_controlledCompanion_last {K ι : Type*} [Field K]
    (d : ℕ) (a : Fin (d + 1) → K) (W : Matrix ι (Fin (d + 1)) K) :
    (W * controlledCompanion d a).col (Fin.last d) =
      -∑ j, a j • W.col j := by
  funext i
  simp only [Matrix.col_apply, Matrix.mul_apply, controlledCompanion_last,
    neg_mul, Finset.sum_neg_distrib, Pi.neg_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, mul_comm (W _ _)]

end AdaptiveOrthogonalRigidity
