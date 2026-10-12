import AdaptiveOrthogonalRigidity.BoundaryKrylov

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

noncomputable def boundaryKrylovBudget (α : ℝ) (n b d t : ℕ) : ℝ :=
  ((3 : ℝ) ^ ((d + 1) * (b + 1)) + markPairCount d) *
    (beta α) ^ ((n : ℝ) - b - 1 - d * t) +
  2 * rootCount d * (2 : ℝ) ^ n * (beta α) ^ (((t : ℝ) ^ 2 - 1) / 4)

theorem fixed_boundary_krylov_le_budget {n b : ℕ} (hb : b < n)
    (S : Finset (Fin n)) (hS : S.card ≤ b) (d t : ℕ)
    {α : ℝ} (hα : 0 ≤ α) (hαhalf : α ≤ 1 / 2)
    (p : EdgeParameters n) (hp : Admissible α p) :
    eventProbability p (fixedBoundaryKrylovFailure S d) ≤ boundaryKrylovBudget α n b d t := by
  have hβ : 0 < beta α := by dsimp [beta]; linarith
  have hβ1 : beta α ≤ 1 := by dsimp [beta]; linarith
  have hSn : S.card ≤ n := hS.trans hb.le
  have hSr : (S.card : ℝ) ≤ b := by exact_mod_cast hS
  have hpow : (beta α) ^ (((n - S.card : ℕ) : ℝ) - 1 - d * t) ≤
      (beta α) ^ ((n : ℝ) - b - 1 - d * t) := by
    apply Real.rpow_le_rpow_of_exponent_ge hβ hβ1
    rw [Nat.cast_sub hSn]
    linarith
  have hcoeff : (3 : ℝ) ^ ((d + 1) * (S.card + 1)) + markPairCount d ≤
      (3 : ℝ) ^ ((d + 1) * (b + 1)) + markPairCount d := by
    exact add_le_add (pow_le_pow_right₀ (by norm_num)
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right hS 1))) (le_refl _)
  have hsize : (2 : ℝ) ^ (n - S.card) ≤ (2 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  apply (fixed_boundary_krylov_bound S (hS.trans_lt hb) d t hα hαhalf p hp).trans
  exact add_le_add
    (mul_le_mul hcoeff hpow (Real.rpow_nonneg hβ.le _) (by positivity))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsize (by positivity))
      (Real.rpow_nonneg hβ.le _))

/-- Simultaneous control of every original boundary up to b; no chosen boundary
or deletion path is conditioned on to assert an independent law. -/
theorem uniform_krylov_bound {n b : ℕ} (hb : b < n) (d t : ℕ)
    {α : ℝ} (hα : 0 ≤ α) (hαhalf : α ≤ 1 / 2)
    (p : EdgeParameters n) (hp : Admissible α p) :
    eventProbability p (boundaryKrylovFailure n b d) ≤
      (boundaryCount n b : ℝ) * boundaryKrylovBudget α n b d t := by
  let Q := Finset.range (b + 1)
  let E (q : Q) : Set (GraphSample n) :=
    ⋃ S : (Finset.univ : Finset (Fin n)).powersetCard q.val, fixedBoundaryKrylovFailure S.val d
  let C := boundaryKrylovBudget α n b d t
  have hsub : boundaryKrylovFailure n b d ⊆ ⋃ q : Q, E q := by
    rintro ω ⟨S, hS, hω⟩
    refine Set.mem_iUnion.mpr ⟨⟨S.card, Finset.mem_range.mpr (by omega)⟩, ?_⟩
    exact Set.mem_iUnion.mpr ⟨⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩, hω⟩
  have hE (q : Q) : eventProbability p (E q) ≤ (n.choose q.val : ℝ) * C := by
    have hq : q.val ≤ b := by have := Finset.mem_range.mp q.property; omega
    have hS (S : (Finset.univ : Finset (Fin n)).powersetCard q.val) :
        eventProbability p (fixedBoundaryKrylovFailure S.val d) ≤ C :=
      fixed_boundary_krylov_le_budget hb S.val ((Finset.mem_powersetCard.mp S.property).2.trans_le hq)
        d t hα hαhalf p hp
    calc
      _ ≤ ∑ S : (Finset.univ : Finset (Fin n)).powersetCard q.val,
        eventProbability p (fixedBoundaryKrylovFailure S.val d) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _S : (Finset.univ : Finset (Fin n)).powersetCard q.val, C :=
        Finset.sum_le_sum (fun S _ => hS S)
      _ = _ := by simp [Finset.card_powersetCard]
  calc
    _ ≤ eventProbability p (⋃ q : Q, E q) := measureReal_mono hsub
    _ ≤ ∑ q : Q, eventProbability p (E q) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ q : Q, (n.choose q.val : ℝ) * C := Finset.sum_le_sum (fun q _ => hE q)
    _ = (boundaryCount n b : ℝ) * C := by
      rw [← Finset.sum_mul]
      congr 1
      simp only [boundaryCount, Nat.cast_sum, Q, Finset.univ_eq_attach]
      exact Finset.sum_attach _ (fun q => (n.choose q : ℝ))

/-- The exact K_n term in the finite movement theorem. -/
theorem uniform_movement_krylov_bound {n b : ℕ} (hb : b < n) (r t : ℕ)
    {α : ℝ} (hα : 0 ≤ α) (hαhalf : α ≤ 1 / 2)
    (p : EdgeParameters n) (hp : Admissible α p) :
    eventProbability p (boundaryKrylovFailure n b (2 * r)) ≤ krylovBound α n r t b := by
  simpa only [boundaryKrylovBudget, krylovBound, Nat.cast_mul, Nat.cast_ofNat] using
    uniform_krylov_bound hb (2 * r) t hα hαhalf p hp

end AdaptiveOrthogonalRigidity
