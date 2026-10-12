import AdaptiveOrthogonalRigidity.MovementFiniteNumerics

open Filter Asymptotics
namespace AdaptiveOrthogonalRigidity

noncomputable def movementErrorSequence (α : ℝ) (r : ℕ → ℕ) (n : ℕ) : ℝ :=
  movementNumericalError α n (r n) (movementRounds α n) (movementCutoff n (r n))
    (movementBoundary α n (r n))

theorem movement_error_isLittleO {α : ℝ} (hα : 0 < α) (ha : α ≤ 1 / 2)
    (r : ℕ → ℕ) (hr : ∀ n, 1 ≤ r n)
    (hs : IsLittleO atTop (fun n => (r n : ℝ))
      (fun n => Real.sqrt ((n : ℝ) / Real.log n))) :
    IsLittleO atTop (movementErrorSequence α r) (fun n => (n : ℝ)) := by
  let b := fun n => movementBoundary α n (r n)
  let R := movementRounds α
  let t := fun n => movementCutoff n (r n)
  have hbs := movement_boundary_limits hα ha r hr hs
  have hbn : Tendsto (fun n => (b n : ℝ) / n) atTop (nhds 0) := hbs.1
  have hbl : Tendsto (fun n => (b n : ℝ) * Real.log n / n) atTop (nhds 0) := hbs.2.1
  have hrb : Tendsto (fun n => (r n : ℝ) * b n / n) atTop (nhds 0) := hbs.2.2
  have hrn := (movement_ratio_limits r hs).2.2.2
  have hr2R : Tendsto (fun n => (r n : ℝ)^2 * R n / n) atTop (nhds 0) := movement_rounds_limits hα ha r hs
  have hrt : Tendsto (fun n => (r n : ℝ) * t n / n) atTop (nhds 0) := (movement_cutoff_limits r hr hs).1
  have hfour : Tendsto (fun n => (r n : ℝ) * (kappa α)^(R n)) atTop (nhds 0) := movement_fourier_limit hα ha r hs
  have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (nhds 0) := tendsto_natCast_atTop_atTop.const_div_atTop 1
  have hl : Tendsto (fun n : ℕ => Real.log n / n) atTop (nhds 0) := by simpa using movement_log_limits 1
  have hr2 : Tendsto (fun n => (r n : ℝ)^2 / n) atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) ?_ (movement_ratio_limits r hs).2.1
    filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1] with n hn
    change 1 ≤ Real.log (n : ℝ) at hn
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [sq_nonneg (r n : ℝ)]
  have hB : Tendsto (fun n => movementBoundaryEntropy n (b n) / n) atTop (nhds 0) := by
    have hmajor := (hbl.add hl).add ((hbn.add h1).mul_const (Real.log 2))
    simp only [zero_add, zero_mul] at hmajor
    apply squeeze_zero' ?_ ?_ hmajor
    · exact Eventually.of_forall (fun n => div_nonneg
        (mul_nonneg (by positivity) (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]))) (by positivity))
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
      have hn0 : (0:ℝ) < n := by linarith
      have hh := Real.log_le_log (by positivity : (0:ℝ) < (n:ℝ)+1)
        (show (n:ℝ)+1 ≤ 2*n by linarith)
      rw [Real.log_mul (by norm_num) hn0.ne'] at hh
      have hh' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh
        (show 0 ≤ (b n : ℝ)+1 by positivity)) hn0.le
      change ((b n : ℝ)+1)*Real.log ((n:ℝ)+1)/n ≤ _
      convert hh' using 1
      ring_nf
  have hP : Tendsto (fun n => movementKrylovEntropy (r n) (b n) / n) atTop (nhds 0) := by
    have h := (((hrb.const_mul 2).add (hrn.const_mul 2)).add hbn |>.add h1).mul_const (Real.log 3)
    convert h using 1 <;> (try funext n) <;> (try simp only [movementKrylovEntropy]) <;> ring_nf
  have hH : Tendsto (fun n => movementRootEntropy (r n) / n) atTop (nhds 0) := by
    have h := hrn.const_mul (4*(1+Real.log 3))
    convert h using 1 <;> (try funext n) <;> (try simp only [movementRootEntropy]) <;> ring_nf
  have hD : Tendsto (fun n => movementDescriptorEntropy (r n) (R n) (b n) / n) atTop (nhds 0) := by
    have h := (((((hr2.const_mul 2).add (hrb.const_mul 2)).add (hrn.const_mul 3)).add hbn).add h1 |>.add hr2R).mul_const (Real.log 3)
    convert h using 1 <;> (try funext n) <;> (try simp only [movementDescriptorEntropy]) <;> ring_nf
  have hC : Tendsto (fun n => coverRate α * ((b n : ℝ)+1+2*(r n:ℝ)*t n) / n) atTop (nhds 0) := by
    have h := ((hbn.add h1).add (hrt.const_mul 2)).const_mul (coverRate α)
    convert h using 1 <;> (try funext n) <;> ring_nf
  have hF : Tendsto (fun n => 2*(r n:ℝ)*n*(kappa α)^(R n)/n) atTop (nhds 0) := by
    have h := hfour.const_mul 2
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnz : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  have hsum := ((((((((((hB.add hP).add hH).add (h1.const_mul (Real.log 2))).add hC).add
    (h1.const_mul (coverRate α / 4))).add hD).sub (hbn.mul_const (Real.log (2/3:ℝ)))).add hrn).add hF).add
    ((hbn.add h1).mul_const (Real.log 3))).sub (hbn.mul_const (Real.log (gamma α))) |>.add (h1.const_mul (Real.log 4))
  have hlim : Tendsto (fun n => movementErrorSequence α r n / n) atTop (nhds 0) := by
    convert hsum using 1 <;> (try funext n) <;> (try simp only [movementErrorSequence, movementNumericalError, movementOverhead, b, R, t]) <;> ring_nf
  apply (isLittleO_iff_tendsto' ?_).mpr hlim
  filter_upwards [eventually_ge_atTop 1] with n hn hz
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact False.elim (hn0.ne' hz)


theorem movement_cover_term_le {α : ℝ} (hα : 0 < α) (ha : α ≤ 1 / 2)
    {n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r) :
    (n:ℝ)^4 * Real.exp (-coverRate α * (movementLambda α n r)^2 / 2) ≤
      (n:ℝ)^4 * Real.exp (-coverRate α * n * Real.log n / (2*(r:ℝ)^2)) := by
  have hc := movement_coverRate_pos hα ha
  have hl : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hr0 : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hLam : Real.sqrt (n * Real.log n) / r ≤ movementLambda α n r := le_max_right _ _
  have hs := pow_le_pow_left₀ (show 0 ≤ Real.sqrt (n * Real.log n) / r by positivity) hLam 2
  rw [div_pow, Real.sq_sqrt (by positivity)] at hs
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonpos_left hs (show -coverRate α / 2 ≤ 0 by linarith)
  convert hh using 1 <;> ring

/-- The finite numerical definition has the first A1 bound. This theorem contains
no assertion about graph events; it supplies the numerical bridge for F1. -/
theorem movement_numerical_first_bound {α : ℝ} (hα : 0 < α) (ha : α ≤ 1 / 2)
    (r : ℕ → ℕ) (hr : ∀ n, 1 ≤ r n)
    (hs : IsLittleO atTop (fun n => (r n : ℝ))
      (fun n => Real.sqrt ((n : ℝ) / Real.log n))) :
    IsLittleO atTop (movementErrorSequence α r) (fun n => (n:ℝ)) ∧
    ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ 1 ≤ movementRounds α n ∧ 2 ≤ movementCutoff n (r n) ∧
      max 1 (2 * coverEntropy n / coverRate α) ≤ movementLambda α n (r n) ∧
      movementBoundary α n (r n) ≤ n - 2 ∧
      movementRounds α n * r n ≤ n - movementBoundary α n (r n) ∧
      finiteMovementBound α (movementLambda α n (r n)) n (r n) (movementRounds α n) (movementCutoff n (r n)) ≤
        (n:ℝ)^4 * Real.exp (-coverRate α * n * Real.log n / (2*(r n:ℝ)^2)) +
          (gamma α)^n * Real.exp (movementErrorSequence α r n) := by
  refine ⟨movement_error_isLittleO hα ha r hr hs, ?_⟩
  have hc := movement_coverRate_pos hα ha
  have ht := (movement_cutoff_limits r hr hs).2
  filter_upwards [movement_parameters_eventually hα ha r hr hs,
    ht.eventually_ge_atTop (4 * (Real.log 2 - Real.log (gamma α)) / coverRate α)] with n hn ht
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcut : (Real.log 2 - Real.log (gamma α)) * n ≤
      coverRate α * (movementCutoff n (r n):ℝ)^2 / 4 := by
    have hh := (le_div_iff₀ hn0).mp ht
    have hm := mul_le_mul_of_nonneg_left hh hc.le
    have hid : coverRate α * (4 * (Real.log 2 - Real.log (gamma α)) / coverRate α * n) =
        4 * (Real.log 2 - Real.log (gamma α)) * n := by field_simp
    rw [hid] at hm
    linarith
  refine ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2, ?_⟩
  have hb : movementBoundary α n (r n) ≤ n := (hn.2.2.2.2.1).trans (Nat.sub_le _ _)
  have hrem := movement_remainder_le (r := r n) (R := movementRounds α n) hα ha hb hcut
  have hcover := movement_cover_term_le hα ha (show 1 ≤ n by omega) (hr n)
  change _ ≤ _ + _
  unfold finiteMovementBound
  dsimp [movementErrorSequence, movementBoundary] at hrem ⊢
  linarith

noncomputable def movementRateSequence (α : ℝ) (r : ℕ → ℕ) (n : ℕ) : ℝ :=
  min ((coverRate α / 8) * n / ((r n:ℝ)^2 * Real.log n))
    (((-Real.log (gamma α)) / 4) * n / (Real.log n)^2)

theorem movement_rate_tendsto {α : ℝ} (hα : 0 < α) (ha : α ≤ 1 / 2)
    (r : ℕ → ℕ) (hr : ∀ n, 1 ≤ r n)
    (hs : IsLittleO atTop (fun n => (r n : ℝ))
      (fun n => Real.sqrt ((n : ℝ) / Real.log n))) :
    Tendsto (movementRateSequence α r) atTop atTop := by
  have hc := movement_coverRate_pos hα ha
  have hd : 0 < -Real.log (gamma α) := neg_pos.mpr (Real.log_neg (gamma_pos hα ha) (gamma_lt_one hα))
  have he : ∀ᶠ n : ℕ in atTop, 0 < (n:ℝ) ∧ 0 < (r n:ℝ) ∧ 0 < Real.log (n:ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact ⟨by exact_mod_cast (show 0 < n by omega),
      by exact_mod_cast (show 0 < r n by have := hr n; omega),
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))⟩
  have hA : Tendsto (fun n => (coverRate α / 8) * n / ((r n:ℝ)^2 * Real.log n)) atTop atTop := by
    have hratio : Tendsto (fun n => (r n:ℝ)^2 * Real.log n / n) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
      tendsto_nhdsWithin_iff.mpr ⟨(movement_ratio_limits r hs).2.1,
        he.mono (fun n hn => div_pos (mul_pos (sq_pos_of_pos hn.2.1) hn.2.2) hn.1)⟩
    have h := hratio.inv_tendsto_nhdsGT_zero.const_mul_atTop (show 0 < coverRate α / 8 by positivity)
    convert h using 1
    funext n
    dsimp
    field_simp
  have hB : Tendsto (fun n : ℕ => ((-Real.log (gamma α))/4) * n / (Real.log n)^2) atTop atTop := by
    have hratio : Tendsto (fun n : ℕ => (Real.log n)^2 / n) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
      tendsto_nhdsWithin_iff.mpr ⟨movement_log_limits 2,
        he.mono (fun n hn => div_pos (sq_pos_of_pos hn.2.2) hn.1)⟩
    have h := hratio.inv_tendsto_nhdsGT_zero.const_mul_atTop (show 0 < -Real.log (gamma α) / 4 by positivity)
    convert h using 1
    funext n
    dsimp
    field_simp
  apply tendsto_atTop.mpr
  intro a
  filter_upwards [hA.eventually_ge_atTop a, hB.eventually_ge_atTop a] with n hn hm
  exact le_min hn hm


theorem movement_two_term_le {α : ℝ} (hα : 0 < α) (ha : α ≤ 1 / 2)
    (r : ℕ → ℕ) {n : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r n)
    (hl : 1 ≤ Real.log (n:ℝ)) {e : ℝ}
    (he : e ≤ (-Real.log (gamma α)) * n / 2)
    (hw : 4 ≤ movementRateSequence α r n) :
    (n:ℝ)^4 * Real.exp (-coverRate α*n*Real.log n/(2*(r n:ℝ)^2)) +
      (gamma α)^n * Real.exp e ≤ Real.exp (-movementRateSequence α r n * (Real.log n)^2) := by
  let A := (coverRate α / 8) * n / ((r n:ℝ)^2 * Real.log n)
  let B := ((-Real.log (gamma α)) / 4) * n / (Real.log n)^2
  let w := movementRateSequence α r n
  have hwA : w ≤ A := min_le_left _ _
  have hwB : w ≤ B := min_le_right _ _
  have hA4 : 4 ≤ A := hw.trans hwA
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr0 : (0:ℝ) < r n := by exact_mod_cast (show 0 < r n by omega)
  have hl0 : 0 < Real.log (n:ℝ) := by linarith
  have hAeq : 4*A*(Real.log n)^2 = coverRate α*n*Real.log n/(2*(r n:ℝ)^2) := by
    dsimp [A]
    field_simp
    ring
  have hBeq : 4*B*(Real.log n)^2 = (-Real.log (gamma α))*n := by
    dsimp [B]
    field_simp
  have hsq : Real.log (n:ℝ) ≤ (Real.log n)^2 := by nlinarith
  have hA4' := mul_le_mul_of_nonneg_right hA4 (sq_nonneg (Real.log (n:ℝ)))
  have hAw := mul_le_mul_of_nonneg_right hwA (sq_nonneg (Real.log (n:ℝ)))
  have hBw := mul_le_mul_of_nonneg_right hwB (sq_nonneg (Real.log (n:ℝ)))
  have hcover : (n:ℝ)^4 * Real.exp (-coverRate α*n*Real.log n/(2*(r n:ℝ)^2)) ≤
      Real.exp (-2*w*(Real.log n)^2) := by
    rw [movement_pow_exp hn0 4, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    norm_num
    rw [neg_div, ← hAeq]
    nlinarith only [hsq, hA4', hAw]
  have hcube : (gamma α)^n * Real.exp e ≤ Real.exp (-2*w*(Real.log n)^2) := by
    rw [movement_pow_exp (gamma_pos hα ha) n, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [he, hBeq, hBw]
  have hlog2 : Real.log (2:ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at h
    exact h
  have hX : Real.log (2:ℝ) ≤ w*(Real.log n)^2 := by
    have hh := mul_le_mul_of_nonneg_right hw (sq_nonneg (Real.log (n:ℝ)))
    change 4*(Real.log n)^2 ≤ w*(Real.log n)^2 at hh
    nlinarith
  calc
    _ ≤ 2 * Real.exp (-2*w*(Real.log n)^2) := by linarith
    _ = Real.exp (Real.log 2 + (-2*w*(Real.log n)^2)) := by rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [w] at *; linarith)

/-- Explicit sequences and one common threshold for all finite numerical
hypotheses and both A1 estimates. No graph-event estimate is assumed here. -/
theorem movement_asymptotic_parameters_and_bounds {α : ℝ} (hα : 0 < α) (ha : α ≤ 1 / 2)
    (r : ℕ → ℕ) (hr : ∀ n, 1 ≤ r n)
    (hs : IsLittleO atTop (fun n => (r n : ℝ))
      (fun n => Real.sqrt ((n : ℝ) / Real.log n))) :
    ∃ (lam : ℕ → ℝ) (R t : ℕ → ℕ) (e w : ℕ → ℝ) (N : ℕ),
      IsLittleO atTop e (fun n => (n:ℝ)) ∧ Tendsto w atTop atTop ∧
      ∀ n, N ≤ n →
        2 ≤ n ∧ 1 ≤ R n ∧ 2 ≤ t n ∧
        max 1 (2 * coverEntropy n / coverRate α) ≤ lam n ∧
        totalBoundary (lam n) (r n) (R n) ≤ n - 2 ∧
        R n * r n ≤ n - totalBoundary (lam n) (r n) (R n) ∧
        finiteMovementBound α (lam n) n (r n) (R n) (t n) ≤
          (n:ℝ)^4 * Real.exp (-coverRate α*n*Real.log n/(2*(r n:ℝ)^2)) +
            (gamma α)^n * Real.exp (e n) ∧
        finiteMovementBound α (lam n) n (r n) (R n) (t n) ≤
          Real.exp (-w n * (Real.log n)^2) := by
  have hfirst := movement_numerical_first_bound hα ha r hr hs
  have hw := movement_rate_tendsto hα ha r hr hs
  have hd : 0 < -Real.log (gamma α) := neg_pos.mpr (Real.log_neg (gamma_pos hα ha) (gamma_lt_one hα))
  have he := hfirst.1.tendsto_div_nhds_zero
  have hall : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ 1 ≤ movementRounds α n ∧ 2 ≤ movementCutoff n (r n) ∧
      max 1 (2 * coverEntropy n / coverRate α) ≤ movementLambda α n (r n) ∧
      movementBoundary α n (r n) ≤ n - 2 ∧
      movementRounds α n * r n ≤ n - movementBoundary α n (r n) ∧
      finiteMovementBound α (movementLambda α n (r n)) n (r n) (movementRounds α n) (movementCutoff n (r n)) ≤
        (n:ℝ)^4 * Real.exp (-coverRate α*n*Real.log n/(2*(r n:ℝ)^2)) +
          (gamma α)^n * Real.exp (movementErrorSequence α r n) ∧
      finiteMovementBound α (movementLambda α n (r n)) n (r n) (movementRounds α n) (movementCutoff n (r n)) ≤
        Real.exp (-movementRateSequence α r n * (Real.log n)^2) := by
    filter_upwards [hfirst.2, hw.eventually_ge_atTop 4,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
      he.eventually_le_const (show 0 < -Real.log (gamma α)/2 by positivity)] with n hn hw hl he
    have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have he' : movementErrorSequence α r n ≤ (-Real.log (gamma α))*n/2 := by
      have hh := (div_le_iff₀ hn0).mp he
      linarith
    exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2.1,
      hn.2.2.2.2.2.2, hn.2.2.2.2.2.2.trans (movement_two_term_le hα ha r hn.1 (hr n) hl he' hw)⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hall
  exact ⟨fun n => movementLambda α n (r n), movementRounds α,
    fun n => movementCutoff n (r n), movementErrorSequence α r, movementRateSequence α r,
    N, hfirst.1, hw, hN⟩

end AdaptiveOrthogonalRigidity
