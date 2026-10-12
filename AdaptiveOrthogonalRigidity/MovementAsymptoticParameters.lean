import AdaptiveOrthogonalRigidity.BoundArithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Asymptotics
namespace AdaptiveOrthogonalRigidity

noncomputable def movementLambda (α : ℝ) (n r : ℕ) : ℝ :=
  max (max 1 (2 * coverEntropy n / coverRate α)) (Real.sqrt (n * Real.log n) / r)
noncomputable def movementRounds (α : ℝ) (n : ℕ) : ℕ :=
  ⌈3 * Real.log n / Real.log (1 / kappa α)⌉₊
/-- Algebraically the manuscript's `ceil(n^(3/4)/sqrt(r))`. -/
noncomputable def movementCutoff (n r : ℕ) : ℕ :=
  ⌈Real.sqrt ((n : ℝ) * Real.sqrt n / r)⌉₊
noncomputable def movementBoundary (α : ℝ) (n r : ℕ) : ℕ :=
  totalBoundary (movementLambda α n r) r (movementRounds α n)

theorem movement_coverRate_pos {α : ℝ} (hα : 0 < α) (ha : α ≤ 1 / 2) :
    0 < coverRate α := by
  apply Real.log_pos
  exact (one_lt_div (beta_pos hα ha)).2 (beta_lt_one hα)

theorem movement_kappa_pos_lt_one {α : ℝ} (hα : 0 < α) (ha : α ≤ 1 / 2) :
    0 < kappa α ∧ kappa α < 1 := by
  have hn : 0 < 1 - 3 * α * (1 - α) := by nlinarith [sq_nonneg (α - 1 / 2)]
  constructor
  · exact Real.sqrt_pos.2 hn
  · rw [kappa, Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    nlinarith

theorem movement_roundRate_pos {α : ℝ} (hα : 0 < α) (ha : α ≤ 1 / 2) :
    0 < Real.log (1 / kappa α) := by
  exact Real.log_pos ((one_lt_div (movement_kappa_pos_lt_one hα ha).1).2
    (movement_kappa_pos_lt_one hα ha).2)

theorem movement_log_limits (m : ℕ) :
    Tendsto (fun n : ℕ => (Real.log n) ^ m / n) atTop (nhds 0) :=
  (Real.isLittleO_pow_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop).tendsto_div_nhds_zero

theorem movement_sqrt_log_limits :
    Tendsto (fun n : ℕ => Real.sqrt (n * Real.log n) / n) atTop (nhds 0) ∧
    Tendsto (fun n : ℕ => Real.sqrt (n * Real.log n) * Real.log n / n) atTop (nhds 0) := by
  have he : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) ∧ 0 ≤ Real.log n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact ⟨by exact_mod_cast (show 0 < n by omega), Real.log_nonneg (by exact_mod_cast hn)⟩
  constructor
  · have h := (movement_log_limits 1).sqrt
    simp only [pow_one, Real.sqrt_zero] at h
    apply h.congr'
    filter_upwards [he] with n hn
    rw [Real.sqrt_div hn.2, Real.sqrt_mul hn.1.le]
    have hs := Real.sq_sqrt hn.1.le
    have hs0 := Real.sqrt_pos.2 hn.1
    have hnz := ne_of_gt hn.1
    field_simp
    rw [hs]
  · have h := (movement_log_limits 3).sqrt
    simp only [Real.sqrt_zero] at h
    apply h.congr'
    filter_upwards [he] with n hn
    have hleft : 0 ≤ Real.sqrt ((Real.log n) ^ 3 / n) := Real.sqrt_nonneg _
    have hright : 0 ≤ Real.sqrt (n * Real.log n) * Real.log n / n := by positivity
    apply (sq_eq_sq₀ hleft hright).mp
    rw [Real.sq_sqrt (by positivity), div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp

theorem movement_ratio_limits (r : ℕ → ℕ)
    (hs : IsLittleO atTop (fun n => (r n : ℝ))
      (fun n => Real.sqrt ((n : ℝ) / Real.log n))) :
    Tendsto (fun n => (r n : ℝ) * Real.sqrt (n * Real.log n) / n) atTop (nhds 0) ∧
    Tendsto (fun n => (r n : ℝ) ^ 2 * Real.log n / n) atTop (nhds 0) ∧
    Tendsto (fun n => (r n : ℝ) / Real.sqrt n) atTop (nhds 0) ∧
    Tendsto (fun n => (r n : ℝ) / n) atTop (nhds 0) := by
  have he : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) ∧ 1 ≤ Real.log n := by
    filter_upwards [eventually_ge_atTop 1,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1] with n hn hl
    exact ⟨by exact_mod_cast (show 0 < n by omega), hl⟩
  have hq := hs.tendsto_div_nhds_zero
  have hid : ∀ᶠ n : ℕ in atTop,
      (r n : ℝ) / Real.sqrt ((n : ℝ) / Real.log n) =
        (r n : ℝ) * Real.sqrt (n * Real.log n) / n := by
    filter_upwards [he] with n hn
    have hl : 0 < Real.log (n : ℝ) := by linarith [hn.2]
    rw [Real.sqrt_div hn.1.le, Real.sqrt_mul hn.1.le]
    have hs := Real.sq_sqrt hn.1.le
    have hnz := ne_of_gt hn.1
    have hsz := ne_of_gt (Real.sqrt_pos.2 hn.1)
    have hlz := ne_of_gt (Real.sqrt_pos.2 hl)
    field_simp
    nlinarith
  have h1 := hq.congr' hid
  have h2 : Tendsto (fun n => (r n : ℝ) ^ 2 * Real.log n / n) atTop (nhds 0) := by
    have h := h1.pow 2
    simp only [zero_pow (by decide : 2 ≠ 0)] at h
    apply h.congr'
    filter_upwards [he] with n hn
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have h3 : Tendsto (fun n => (r n : ℝ) / Real.sqrt n) atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) ?_ hq
    filter_upwards [he] with n hn
    apply div_le_div_of_nonneg_left (by positivity)
      (Real.sqrt_pos.2 (div_pos hn.1 (by linarith [hn.2])))
    apply Real.sqrt_le_sqrt
    exact (div_le_self hn.1.le hn.2)
  have h4 : Tendsto (fun n => (r n : ℝ) / n) atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) ?_ h3
    filter_upwards [he, eventually_ge_atTop 1] with n hn hn1
    apply div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 hn.1)
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      nlinarith
  exact ⟨h1, h2, h3, h4⟩


theorem movement_coverEntropy_le {n : ℕ} (hn : 1 ≤ n) (hl : 1 ≤ Real.log (n : ℝ)) :
    coverEntropy n ≤ 16 * Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : Real.log 5 ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
    norm_num at h ⊢
    exact h
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < 1 + 4 * (n : ℝ)^2)
    (show 1 + 4 * (n : ℝ)^2 ≤ 5 * (n : ℝ)^2 by nlinarith)
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hh
  norm_num at hh
  unfold coverEntropy
  linarith

noncomputable def movementBudgetConstant (α : ℝ) : ℝ :=
  4 * max 1 (32 / coverRate α) + 3 / Real.log (1 / kappa α) + 2

theorem movement_boundary_le {α : ℝ} (hα : 0 < α) (ha : α ≤ 1 / 2)
    {n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r) (hl : 1 ≤ Real.log (n : ℝ))
    (hrl : (r : ℝ) * Real.log n ≤ Real.sqrt (n * Real.log n)) :
    (movementBoundary α n r : ℝ) ≤ movementBudgetConstant α * Real.sqrt (n * Real.log n) := by
  let z := Real.sqrt (n * Real.log n)
  let C := max 1 (32 / coverRate α)
  let A := 3 / Real.log (1 / kappa α)
  have hc := movement_coverRate_pos hα ha
  have hd := movement_roundRate_pos hα ha
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hz : 1 ≤ z := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hrz : (r : ℝ) ≤ z := by nlinarith
  have hC : 1 ≤ C := le_max_left _ _
  have hCA : 32 / coverRate α ≤ C := le_max_right _ _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hLam : movementLambda α n r * r ≤ C * z := by
    unfold movementLambda
    rw [max_mul_of_nonneg _ _ hr0.le, max_mul_of_nonneg _ _ hr0.le,
      div_mul_cancel₀ _ hr0.ne']
    apply max_le
    · apply max_le
      · simpa using hrz.trans (by nlinarith : z ≤ C * z)
      · have hh := movement_coverEntropy_le hn hl
        have hh' : 2 * coverEntropy n / coverRate α ≤ 32 / coverRate α * Real.log n := by
          apply (div_le_iff₀ hc).2
          have hcz := hc.ne'
          field_simp
          linarith
        calc
          _ ≤ (32 / coverRate α * Real.log n) * r := mul_le_mul_of_nonneg_right hh' hr0.le
          _ = (32 / coverRate α) * ((r : ℝ) * Real.log n) := by ring
          _ ≤ (32 / coverRate α) * z := mul_le_mul_of_nonneg_left hrl (by positivity)
          _ ≤ C * z := mul_le_mul_of_nonneg_right hCA (by linarith)
    · nlinarith
  have hLampos : 0 ≤ movementLambda α n r := (by norm_num : (0 : ℝ) ≤ 1).trans
    ((le_max_left _ _).trans (le_max_left _ _))
  have hR : (movementRounds α n : ℝ) ≤ A * Real.log n + 1 := by
    unfold movementRounds
    convert (Nat.ceil_lt_add_one (show 0 ≤ 3 * Real.log (n : ℝ) / Real.log (1 / kappa α) by positivity)).le using 1
    dsimp [A]
    ring
  have hRr : (movementRounds α n : ℝ) * r ≤ (A + 1) * z := by
    have hh := mul_le_mul_of_nonneg_right hR hr0.le
    have hh' := mul_le_mul_of_nonneg_left hrl hA
    nlinarith
  have hb : (initialBoundary (movementLambda α n r) r : ℝ) ≤ 4 * movementLambda α n r * r + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  unfold movementBoundary totalBoundary
  push_cast
  change _ ≤ (4 * C + A + 2) * z
  nlinarith

theorem movement_boundary_limits {α : ℝ} (hα : 0 < α) (ha : α ≤ 1 / 2)
    (r : ℕ → ℕ) (hr : ∀ n, 1 ≤ r n)
    (hs : IsLittleO atTop (fun n => (r n : ℝ))
      (fun n => Real.sqrt ((n : ℝ) / Real.log n))) :
    Tendsto (fun n => (movementBoundary α n (r n) : ℝ) / n) atTop (nhds 0) ∧
    Tendsto (fun n => (movementBoundary α n (r n) : ℝ) * Real.log n / n) atTop (nhds 0) ∧
    Tendsto (fun n => (r n : ℝ) * movementBoundary α n (r n) / n) atTop (nhds 0) := by
  have hrat := (movement_ratio_limits r hs).1
  have hb : ∀ᶠ n : ℕ in atTop,
      (movementBoundary α n (r n) : ℝ) ≤ movementBudgetConstant α * Real.sqrt (n * Real.log n) := by
    filter_upwards [eventually_ge_atTop 1,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
      hrat.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with n hn hl hq
    change 1 ≤ Real.log (n : ℝ) at hl
    apply movement_boundary_le hα ha hn (hr n) hl
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hz0 : 0 < Real.sqrt ((n : ℝ) * Real.log n) := Real.sqrt_pos.2 (by positivity)
    have hzsq := Real.sq_sqrt (show 0 ≤ (n : ℝ) * Real.log n by positivity)
    have hh := (div_le_iff₀ hn0).mp hq
    have hm := mul_le_mul_of_nonneg_right hh (show 0 ≤ Real.log (n : ℝ) by linarith)
    apply le_of_mul_le_mul_left (a := Real.sqrt ((n : ℝ) * Real.log n)) _ hz0
    nlinarith only [hm, hzsq]
  have h1 : Tendsto (fun n => (movementBoundary α n (r n) : ℝ) / n) atTop (nhds 0) := by
    have hh := movement_sqrt_log_limits.1.const_mul (movementBudgetConstant α)
    simp only [mul_zero] at hh
    apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) ?_ hh
    filter_upwards [hb] with n hn
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hn (Nat.cast_nonneg n)
  have h2 : Tendsto (fun n => (movementBoundary α n (r n) : ℝ) * Real.log n / n) atTop (nhds 0) := by
    have hh := movement_sqrt_log_limits.2.const_mul (movementBudgetConstant α)
    simp only [mul_zero] at hh
    apply squeeze_zero' ?_ ?_ hh
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hn))) (by positivity)
    · filter_upwards [hb, eventually_ge_atTop 1] with n hn hn1
      have h := mul_le_mul_of_nonneg_right hn (Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hn1))
      simpa only [mul_div_assoc, mul_assoc] using div_le_div_of_nonneg_right h (Nat.cast_nonneg n)
  have h3 : Tendsto (fun n => (r n : ℝ) * movementBoundary α n (r n) / n) atTop (nhds 0) := by
    have hh := hrat.const_mul (movementBudgetConstant α)
    simp only [mul_zero] at hh
    apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) ?_ hh
    filter_upwards [hb] with n hn
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (r n))) (Nat.cast_nonneg n)
    convert h using 1
    ring
  exact ⟨h1, h2, h3⟩


theorem movement_rounds_limits {α : ℝ} (hα : 0 < α) (ha : α ≤ 1 / 2)
    (r : ℕ → ℕ)
    (hs : IsLittleO atTop (fun n => (r n : ℝ))
      (fun n => Real.sqrt ((n : ℝ) / Real.log n))) :
    Tendsto (fun n => (r n : ℝ)^2 * movementRounds α n / n) atTop (nhds 0) := by
  let A := 3 / Real.log (1 / kappa α)
  have hd := movement_roundRate_pos hα ha
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hh := (movement_ratio_limits r hs).2.1.const_mul (A + 1)
  simp only [mul_zero] at hh
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) ?_ hh
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1] with n hl
  change 1 ≤ Real.log (n : ℝ) at hl
  have hR : (movementRounds α n : ℝ) ≤ (A + 1) * Real.log n := by
    have h := (Nat.ceil_lt_add_one (show 0 ≤ 3 * Real.log (n : ℝ) / Real.log (1 / kappa α) by positivity)).le
    change (movementRounds α n : ℝ) ≤ _ at h
    have heq : 3 * Real.log (n : ℝ) / Real.log (1 / kappa α) = A * Real.log n := by dsimp [A]; ring
    rw [heq] at h
    linarith
  have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hR (sq_nonneg (r n : ℝ))) (Nat.cast_nonneg n)
  convert h using 1
  ring

theorem movement_cutoff_limits (r : ℕ → ℕ) (hr : ∀ n, 1 ≤ r n)
    (hs : IsLittleO atTop (fun n => (r n : ℝ))
      (fun n => Real.sqrt ((n : ℝ) / Real.log n))) :
    Tendsto (fun n => (r n : ℝ) * movementCutoff n (r n) / n) atTop (nhds 0) ∧
    Tendsto (fun n => (movementCutoff n (r n) : ℝ)^2 / n) atTop atTop := by
  have hrat := (movement_ratio_limits r hs).2.2.1
  have hrn := (movement_ratio_limits r hs).2.2.2
  have he : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) ∧ 0 < (r n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact ⟨by exact_mod_cast (show 0 < n by omega), by exact_mod_cast (show 0 < r n by have := hr n; omega)⟩
  have hceil : ∀ n, (movementCutoff n (r n) : ℝ) ≤
      Real.sqrt ((n : ℝ) * Real.sqrt n / r n) + 1 :=
    fun n => (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le
  have hid : ∀ᶠ n : ℕ in atTop,
      (r n : ℝ) * Real.sqrt ((n : ℝ) * Real.sqrt n / r n) / n =
        Real.sqrt ((r n : ℝ) / Real.sqrt n) := by
    filter_upwards [he] with n hn
    have hs0 := Real.sqrt_pos.2 hn.1
    have hsq := Real.sq_sqrt hn.1.le
    have hnz := hn.1.ne'
    have hrz := hn.2.ne'
    have hsz := hs0.ne'
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    field_simp
    nlinarith [congrArg (fun x : ℝ => (r n : ℝ) * n * x) hsq]
  constructor
  · have hh := hrat.sqrt.add hrn
    simp only [Real.sqrt_zero, zero_add] at hh
    apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) ?_ hh
    filter_upwards [hid] with n hn
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hceil n) (Nat.cast_nonneg (r n))) (Nat.cast_nonneg n)
    calc
      _ ≤ (r n : ℝ) * (Real.sqrt ((n : ℝ) * Real.sqrt n / r n) + 1) / n := h
      _ = Real.sqrt ((r n : ℝ) / Real.sqrt n) + (r n : ℝ) / n := by rw [mul_add, add_div, hn, mul_one]
  · have ht : Tendsto (fun n => ((r n : ℝ) / Real.sqrt n)⁻¹) atTop atTop := by
      apply Filter.Tendsto.inv_tendsto_nhdsGT_zero
      exact tendsto_nhdsWithin_iff.mpr ⟨hrat, he.mono (fun n hn => div_pos hn.2 (Real.sqrt_pos.2 hn.1))⟩
    apply tendsto_atTop_mono' _ ?_ ht
    filter_upwards [he] with n hn
    have hsq := Real.sq_sqrt (show 0 ≤ (n : ℝ) * Real.sqrt n / r n by positivity)
    have hc := Nat.le_ceil (Real.sqrt ((n : ℝ) * Real.sqrt n / r n))
    have hc2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hc 2
    change _ ≤ (movementCutoff n (r n) : ℝ)^2 at hc2
    rw [hsq] at hc2
    have h := div_le_div_of_nonneg_right hc2 hn.1.le
    have hnz := hn.1.ne'
    have hrz := hn.2.ne'
    convert h using 1
    field_simp


theorem movement_rounds_fourier {α : ℝ} (hα : 0 < α) (ha : α ≤ 1 / 2)
    {n : ℕ} (hn : 1 ≤ n) : (kappa α)^(movementRounds α n) ≤ ((n : ℝ)^3)⁻¹ := by
  have hk := movement_kappa_pos_lt_one hα ha
  have hd := movement_roundRate_pos hα ha
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl : Real.log (kappa α) < 0 := Real.log_neg hk.1 hk.2
  have hlog : Real.log (1 / kappa α) = -Real.log (kappa α) := by rw [one_div, Real.log_inv]
  have hc := Nat.le_ceil (3 * Real.log (n : ℝ) / Real.log (1 / kappa α))
  change _ ≤ (movementRounds α n : ℝ) at hc
  have hh := (div_le_iff₀ hd).mp hc
  rw [hlog] at hh
  calc
    _ = Real.exp ((movementRounds α n : ℝ) * Real.log (kappa α)) := by rw [Real.exp_nat_mul, Real.exp_log hk.1]
    _ ≤ Real.exp (-(3 * Real.log (n : ℝ))) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by
      rw [Real.exp_neg]
      congr 1
      simpa using Real.exp_nat_mul (Real.log (n : ℝ)) 3 |>.trans (by rw [Real.exp_log hn0])

theorem movement_fourier_limit {α : ℝ} (hα : 0 < α) (ha : α ≤ 1 / 2)
    (r : ℕ → ℕ)
    (hs : IsLittleO atTop (fun n => (r n : ℝ))
      (fun n => Real.sqrt ((n : ℝ) / Real.log n))) :
    Tendsto (fun n => (r n : ℝ) * (kappa α)^(movementRounds α n)) atTop (nhds 0) := by
  have hk := (movement_kappa_pos_lt_one hα ha).1
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) ?_ (movement_ratio_limits r hs).2.2.2
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hh := movement_rounds_fourier hα ha hn
  have hpow : (n : ℝ) ≤ (n : ℝ)^3 := by
    simpa using pow_le_pow_right₀ hn1 (by decide : 1 ≤ 3)
  have hi : ((n : ℝ)^3)⁻¹ ≤ (n : ℝ)⁻¹ := inv_anti₀ hn0 hpow
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left (hh.trans hi) (Nat.cast_nonneg (r n))

theorem movement_parameters_eventually {α : ℝ} (hα : 0 < α) (ha : α ≤ 1 / 2)
    (r : ℕ → ℕ) (hr : ∀ n, 1 ≤ r n)
    (hs : IsLittleO atTop (fun n => (r n : ℝ))
      (fun n => Real.sqrt ((n : ℝ) / Real.log n))) :
    ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ 1 ≤ movementRounds α n ∧ 2 ≤ movementCutoff n (r n) ∧
      max 1 (2 * coverEntropy n / coverRate α) ≤ movementLambda α n (r n) ∧
      movementBoundary α n (r n) ≤ n - 2 ∧
      movementRounds α n * r n ≤ n - movementBoundary α n (r n) := by
  have hb := (movement_boundary_limits hα ha r hr hs).1
  have ht := (movement_cutoff_limits r hr hs).2
  have hd := movement_roundRate_pos hα ha
  filter_upwards [eventually_ge_atTop 4, hb.eventually_le_const (by norm_num : (0 : ℝ) < 1/4),
    ht.eventually_ge_atTop 1] with n hn hb ht
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hb4 : (4 : ℝ) * movementBoundary α n (r n) ≤ n := by
    have hh := (div_le_iff₀ hn0).mp hb
    linarith
  have hb4n : 4 * movementBoundary α n (r n) ≤ n := by exact_mod_cast hb4
  have hR : 1 ≤ movementRounds α n := by
    apply Nat.one_le_ceil_iff.2
    exact div_pos (mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))) hd
  have ht2 : 2 ≤ movementCutoff n (r n) := by
    have hh := (le_div_iff₀ hn0).mp ht
    by_contra h
    have hle : (movementCutoff n (r n) : ℝ) ≤ 1 := by exact_mod_cast (show movementCutoff n (r n) ≤ 1 by omega)
    have ht0 : (0 : ℝ) ≤ movementCutoff n (r n) := by positivity
    nlinarith
  have hRb : movementRounds α n * r n ≤ movementBoundary α n (r n) := by
    unfold movementBoundary totalBoundary
    omega
  exact ⟨by omega, hR, ht2, le_max_left _ _, by omega, by omega⟩


/-- The cutoff uses exactly the paper's real exponent and natural ceiling. -/
theorem movement_cutoff_eq_paper {n r : ℕ} (hn : 1 ≤ n) :
    movementCutoff n r = ⌈(n:ℝ)^(3/4:ℝ) / Real.sqrt r⌉₊ := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold movementCutoff
  congr 1
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
  simp only [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul (Nat.cast_nonneg n), ← Real.rpow_add hn0]
  norm_num

end AdaptiveOrthogonalRigidity
