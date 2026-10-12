import AdaptiveOrthogonalRigidity.MovementAsymptoticParameters
import Mathlib.Data.Nat.Choose.Bounds

open scoped BigOperators
namespace AdaptiveOrthogonalRigidity

noncomputable def movementBoundaryEntropy (n b : ℕ) : ℝ := (b + 1) * Real.log ((n : ℝ) + 1)
noncomputable def movementRootEntropy (r : ℕ) : ℝ := 4 * r * (1 + Real.log 3)
noncomputable def movementKrylovEntropy (r b : ℕ) : ℝ := (2 * r + 1) * (b + 1) * Real.log 3
noncomputable def movementDescriptorEntropy (r R b : ℕ) : ℝ :=
  (2 * (r : ℝ)^2 + 2 * (b + 1) * r + r + (b + 1) + (r : ℝ)^2 * R) * Real.log 3

theorem movement_pow_exp {x : ℝ} (hx : 0 < x) (m : ℕ) :
    x^m = Real.exp ((m : ℝ) * Real.log x) := by
  rw [Real.exp_nat_mul, Real.exp_log hx]

theorem movement_beta_log {α : ℝ} : Real.log (beta α) = -coverRate α := by
  rw [coverRate, one_div, Real.log_inv, neg_neg]

theorem movement_boundaryCount_le {n b : ℕ} (hb : b ≤ n) :
    (boundaryCount n b : ℝ) ≤ Real.exp (movementBoundaryEntropy n b) := by
  have h : boundaryCount n b ≤ (n + 1)^(b + 1) := by
    unfold boundaryCount
    calc
      _ ≤ ∑ _s ∈ Finset.range (b + 1), (n + 1)^b := by
        apply Finset.sum_le_sum
        intro s hs
        have hsb : s ≤ b := by simpa using (show s < b + 1 from Finset.mem_range.mp hs)
        exact (Nat.choose_le_pow n s).trans ((Nat.pow_le_pow_left (by omega) s).trans
          (Nat.pow_le_pow_right (by omega) hsb))
      _ = (b + 1) * (n + 1)^b := by simp
      _ ≤ (n + 1) * (n + 1)^b := Nat.mul_le_mul_right _ (by omega)
      _ = (n + 1)^(b + 1) := by rw [pow_succ, mul_comm]
  have hh : (boundaryCount n b : ℝ) ≤ ((n : ℝ) + 1)^(b + 1) := by exact_mod_cast h
  calc
    _ ≤ _ := hh
    _ = _ := by rw [movement_pow_exp (by positivity)]; simp [movementBoundaryEntropy]

theorem movement_root_counts_le (d : ℕ) :
    rootCount d ≤ (d + 1)^2 * 3^(2*d) ∧ markPairCount d ≤ (d + 1)^2 * 3^(2*d) := by
  have hc : (Finset.Icc 1 d).card ≤ d + 1 := by simp
  constructor
  · unfold rootCount
    calc
      _ ≤ ∑ _a ∈ Finset.Icc 1 d, (d + 1) * 3^(2*d) := by
        apply Finset.sum_le_sum
        intro a ha
        have had := (Finset.mem_Icc.mp ha).2
        exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
      _ = (Finset.Icc 1 d).card * ((d + 1) * 3^(2*d)) := by simp
      _ ≤ (d + 1) * ((d + 1) * 3^(2*d)) := Nat.mul_le_mul_right _ hc
      _ = _ := by ring
  · unfold markPairCount
    calc
      _ ≤ ∑ _a ∈ Finset.Icc 1 d, (d + 1) * 3^(2*d) := by
        apply Finset.sum_le_sum
        intro a ha
        have had := (Finset.mem_Icc.mp ha).2
        exact (Nat.pow_le_pow_right (by omega : 0 < 3) (show 2*a-1 ≤ 2*d by omega)).trans
          (by nlinarith [Nat.one_le_pow (2*d) 3 (by omega)])
      _ = (Finset.Icc 1 d).card * ((d + 1) * 3^(2*d)) := by simp
      _ ≤ (d + 1) * ((d + 1) * 3^(2*d)) := Nat.mul_le_mul_right _ hc
      _ = _ := by ring

theorem movement_root_counts_exp (r : ℕ) :
    (rootCount (2*r) : ℝ) ≤ Real.exp (movementRootEntropy r) ∧
    (markPairCount (2*r) : ℝ) ≤ Real.exp (movementRootEntropy r) := by
  have h := movement_root_counts_le (2*r)
  have hmajor : (((2*r + 1)^2 * 3^(2*(2*r)) : ℕ) : ℝ) ≤ Real.exp (movementRootEntropy r) := by
    push_cast
    have he : 2 * (r : ℝ) + 1 ≤ Real.exp (2 * r) := Real.add_one_le_exp _
    calc
      _ ≤ (Real.exp (2 * r))^2 * (3 : ℝ)^(2*(2*r)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) he 2) (by positivity)
      _ = _ := by
        rw [movement_pow_exp (by norm_num : (0 : ℝ) < 3), ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        unfold movementRootEntropy
        ring
  exact ⟨(show (rootCount (2*r) : ℝ) ≤ _ by exact_mod_cast h.1).trans hmajor,
    (show (markPairCount (2*r) : ℝ) ≤ _ by exact_mod_cast h.2).trans hmajor⟩

theorem movement_krylov_le {α : ℝ} (hα : 0 < α) (ha : α ≤ 1 / 2)
    {n r t b : ℕ} (hb : b ≤ n) :
    krylovBound α n r t b ≤
      Real.exp ((n : ℝ) * Real.log (beta α) + movementBoundaryEntropy n b +
        movementKrylovEntropy r b + movementRootEntropy r + Real.log 2 +
        coverRate α * (b + 1 + 2 * (r : ℝ) * t)) +
      Real.exp ((n : ℝ) * Real.log 2 - coverRate α * (t : ℝ)^2 / 4 +
        movementBoundaryEntropy n b + movementRootEntropy r + Real.log 2 + coverRate α / 4) := by
  have hβ := beta_pos hα ha
  have hB := movement_boundaryCount_le hb
  have hroot := movement_root_counts_exp r
  have hP : 0 ≤ movementKrylovEntropy r b := by unfold movementKrylovEntropy; positivity
  have hH : 0 ≤ movementRootEntropy r := by unfold movementRootEntropy; positivity
  have hcoeff : (3 : ℝ)^((2*r+1)*(b+1)) + markPairCount (2*r) ≤
      Real.exp (movementKrylovEntropy r b + movementRootEntropy r + Real.log 2) := by
    have hpow : (3 : ℝ)^((2*r+1)*(b+1)) = Real.exp (movementKrylovEntropy r b) := by
      rw [movement_pow_exp (by norm_num)]; simp [movementKrylovEntropy]
    rw [hpow]
    have hp := Real.exp_le_exp.mpr (show movementKrylovEntropy r b ≤ movementKrylovEntropy r b + movementRootEntropy r by linarith)
    have hh := Real.exp_le_exp.mpr (show movementRootEntropy r ≤ movementKrylovEntropy r b + movementRootEntropy r by linarith)
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    linarith
  unfold krylovBound
  rw [mul_add]
  apply add_le_add
  · calc
      _ ≤ Real.exp (movementBoundaryEntropy n b) *
          (Real.exp (movementKrylovEntropy r b + movementRootEntropy r + Real.log 2) *
            (beta α)^((n : ℝ)-b-1-2*r*t)) :=
        mul_le_mul hB (mul_le_mul_of_nonneg_right hcoeff (by positivity)) (by positivity) (by positivity)
      _ = _ := by
        rw [Real.rpow_def_of_pos hβ, ← Real.exp_add, ← Real.exp_add, movement_beta_log]
        congr 1
        ring
  · calc
      _ ≤ Real.exp (movementBoundaryEntropy n b) *
          (2 * Real.exp (movementRootEntropy r) * (2 : ℝ)^n *
            (beta α)^(((t : ℝ)^2-1)/4)) := by
        apply mul_le_mul hB _ (by positivity) (by positivity)
        gcongr
        exact hroot.1
      _ = _ := by
        rw [Real.rpow_def_of_pos hβ, movement_pow_exp (by norm_num : (0 : ℝ) < 2),
          show (2 : ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]]
        simp only [← Real.exp_add]
        rw [movement_beta_log]
        simp only [Real.log_exp]
        congr 1
        ring


theorem movement_fourier_power_le {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    (1 + x)^m ≤ Real.exp ((m : ℝ) * x) := by
  rw [Real.exp_nat_mul]
  apply pow_le_pow_left₀ (by positivity)
  simpa [add_comm] using Real.add_one_le_exp x

theorem movement_descriptor_le {α : ℝ} (hα : 0 < α) (ha : α ≤ 1 / 2)
    {n r R b : ℕ} (hb : b ≤ n) :
    descriptorBound α n r R b ≤
      Real.exp ((n : ℝ) * Real.log (2/3:ℝ) + movementBoundaryEntropy n b + r +
        movementDescriptorEntropy r R b - b * Real.log (2/3:ℝ) +
        2 * (r : ℝ) * n * (kappa α)^R) := by
  have hk := (movement_kappa_pos_lt_one hα ha).1
  let F := Real.exp ((n : ℝ) * Real.log (2/3:ℝ) +
    movementDescriptorEntropy r R b - b * Real.log (2/3:ℝ) + 2 * (r : ℝ) * n * (kappa α)^R)
  have hterm : ∀ s ∈ Finset.range (b+1), ∀ k ∈ Finset.Icc 1 r,
      (2/3:ℝ)^(n-s) * (3:ℝ)^(2*k^2+2*(s+1)*k+k+(s+1)+k^2*R) *
        (1+2*(kappa α)^R)^(k*(n-s-k*R)) ≤ F := by
    intro s hs k hk'
    have hsb : s ≤ b := by simpa using Finset.mem_range.mp hs
    have hsn : s ≤ n := hsb.trans hb
    have hkr : k ≤ r := (Finset.mem_Icc.mp hk').2
    have hfirst : (2/3:ℝ)^(n-s) ≤ Real.exp ((n : ℝ)*Real.log (2/3:ℝ)-b*Real.log (2/3:ℝ)) := by
      rw [movement_pow_exp (by norm_num), Nat.cast_sub hsn]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonpos_right (show (s : ℝ) ≤ b by exact_mod_cast hsb)
        (Real.log_nonpos (by norm_num : (0 : ℝ) ≤ 2/3) (by norm_num : (2/3:ℝ) ≤ 1))
      nlinarith
    have hsecond : (3:ℝ)^(2*k^2+2*(s+1)*k+k+(s+1)+k^2*R) ≤ Real.exp (movementDescriptorEntropy r R b) := by
      rw [movement_pow_exp (by norm_num)]
      apply Real.exp_le_exp.mpr
      unfold movementDescriptorEntropy
      push_cast
      gcongr
    have hthird : (1+2*(kappa α)^R)^(k*(n-s-k*R)) ≤ Real.exp (2*(r:ℝ)*n*(kappa α)^R) := by
      apply (movement_fourier_power_le (by positivity) _).trans
      apply Real.exp_le_exp.mpr
      have he : k*(n-s-k*R) ≤ r*n := Nat.mul_le_mul hkr (by omega)
      have hh := mul_le_mul_of_nonneg_right (show (k*(n-s-k*R):ℕ) ≤ (r*n:ℝ) by exact_mod_cast he)
        (show 0 ≤ 2*(kappa α)^R by positivity)
      push_cast at hh
      push_cast
      nlinarith only [hh]
    calc
      _ ≤ Real.exp ((n : ℝ)*Real.log (2/3:ℝ)-b*Real.log (2/3:ℝ)) *
          Real.exp (movementDescriptorEntropy r R b) * Real.exp (2*(r:ℝ)*n*(kappa α)^R) :=
        mul_le_mul (mul_le_mul hfirst hsecond (by positivity) (by positivity)) hthird (by positivity) (by positivity)
      _ = F := by dsimp [F]; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hsum : descriptorBound α n r R b ≤ (boundaryCount n b : ℝ) * ((r : ℝ) * F) := by
    unfold descriptorBound boundaryCount
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro s hs
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 r, F := Finset.sum_le_sum (hterm s hs)
      _ = _ := by simp
  have hrExp : (r : ℝ) ≤ Real.exp r := by linarith [Real.add_one_le_exp (r : ℝ)]
  calc
    _ ≤ (boundaryCount n b : ℝ) * ((r : ℝ) * F) := hsum
    _ ≤ Real.exp (movementBoundaryEntropy n b) * (Real.exp r * F) :=
      mul_le_mul (movement_boundaryCount_le hb) (mul_le_mul_of_nonneg_right hrExp (by dsimp [F]; positivity)) (by dsimp [F]; positivity) (by positivity)
    _ = _ := by dsimp [F]; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem movement_cube_le {α : ℝ} (hα : 0 < α) (ha : α ≤ 1 / 2)
    {n b : ℕ} (hb : b ≤ n) :
    cubeBound α n b ≤ Real.exp ((n : ℝ)*Real.log (gamma α) +
      movementBoundaryEntropy n b + (b+1)*Real.log 3 - b*Real.log (gamma α)) := by
  have hg := gamma_pos hα ha
  have hl := (Real.log_neg hg (gamma_lt_one hα)).le
  let F := (3:ℝ)^(b+1) * (gamma α)^(n-b)
  have hs : cubeBound α n b ≤ (boundaryCount n b : ℝ) * F := by
    unfold cubeBound boundaryCount
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro s hs
    have hsb : s ≤ b := by simpa using Finset.mem_range.mp hs
    calc
      _ = (n.choose s : ℝ) * ((3:ℝ)^(s+1) * (gamma α)^(n-s)) := by ring
      _ ≤ (n.choose s : ℝ) * F := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) (by omega)) _ (by positivity) (by positivity)
        exact pow_le_pow_of_le_one hg.le (gamma_lt_one hα).le (by omega)
  calc
    _ ≤ (boundaryCount n b : ℝ) * F := hs
    _ ≤ Real.exp (movementBoundaryEntropy n b) * F := mul_le_mul_of_nonneg_right (movement_boundaryCount_le hb) (by dsimp [F]; positivity)
    _ = _ := by
      dsimp [F]
      rw [movement_pow_exp (by norm_num : (0:ℝ) < 3), movement_pow_exp hg, ← Real.exp_add, ← Real.exp_add, Nat.cast_sub hb]
      push_cast
      congr 1
      ring


noncomputable def movementOverhead (α : ℝ) (n r R t b : ℕ) : ℝ :=
  movementBoundaryEntropy n b + movementKrylovEntropy r b + movementRootEntropy r +
  Real.log 2 + coverRate α * (b + 1 + 2 * (r : ℝ) * t) + coverRate α / 4 +
  movementDescriptorEntropy r R b - b * Real.log (2/3:ℝ) + r +
  2 * (r : ℝ) * n * (kappa α)^R + (b+1)*Real.log 3 - b*Real.log (gamma α)

noncomputable def movementNumericalError (α : ℝ) (n r R t b : ℕ) : ℝ :=
  movementOverhead α n r R t b + Real.log 4

theorem movement_remainder_le {α : ℝ} (hα : 0 < α) (ha : α ≤ 1 / 2)
    {n r R t b : ℕ} (hb : b ≤ n)
    (ht : (Real.log 2 - Real.log (gamma α)) * n ≤ coverRate α * (t : ℝ)^2 / 4) :
    krylovBound α n r t b + descriptorBound α n r R b + cubeBound α n b ≤
      (gamma α)^n * Real.exp (movementNumericalError α n r R t b) := by
  let E := movementOverhead α n r R t b
  have hc := (movement_coverRate_pos hα ha).le
  have hg := gamma_pos hα ha
  have hβ := beta_pos hα ha
  have hk := (movement_kappa_pos_lt_one hα ha).1
  have hbg : Real.log (beta α) ≤ Real.log (gamma α) := Real.log_le_log hβ (beta_lt_gamma hα ha).le
  have hug : Real.log (2/3:ℝ) ≤ Real.log (gamma α) := Real.log_le_log (by norm_num) (two_thirds_lt_gamma hα ha).le
  have hu0 : Real.log (2/3:ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  have hg0 : Real.log (gamma α) ≤ 0 := (Real.log_neg hg (gamma_lt_one hα)).le
  have hB0 : 0 ≤ movementBoundaryEntropy n b := by
    unfold movementBoundaryEntropy
    exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]))
  have hP0 : 0 ≤ movementKrylovEntropy r b := by unfold movementKrylovEntropy; positivity
  have hH0 : 0 ≤ movementRootEntropy r := by unfold movementRootEntropy; positivity
  have hD0 : 0 ≤ movementDescriptorEntropy r R b := by unfold movementDescriptorEntropy; positivity
  have hL0 : 0 ≤ Real.log (2:ℝ) := by positivity
  have hC0 : 0 ≤ coverRate α * (b + 1 + 2 * (r:ℝ)*t) := by positivity
  have hC4 : 0 ≤ coverRate α / 4 := by positivity
  have hu : 0 ≤ -(b:ℝ)*Real.log (2/3:ℝ) := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg b)) hu0
  have hγ : 0 ≤ -(b:ℝ)*Real.log (gamma α) := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg b)) hg0
  have hF0 : 0 ≤ 2*(r:ℝ)*n*(kappa α)^R := by positivity
  have h3 : 0 ≤ (b+1:ℝ)*Real.log 3 := by positivity
  have hr0 : (0:ℝ) ≤ r := by positivity
  have hE1 : movementBoundaryEntropy n b + movementKrylovEntropy r b + movementRootEntropy r + Real.log 2 +
      coverRate α * (b+1+2*(r:ℝ)*t) ≤ E := by dsimp [E, movementOverhead]; linarith
  have hE2 : movementBoundaryEntropy n b + movementRootEntropy r + Real.log 2 + coverRate α / 4 ≤ E := by
    dsimp [E, movementOverhead]; linarith
  have hED : movementBoundaryEntropy n b + r + movementDescriptorEntropy r R b - b*Real.log (2/3:ℝ) +
      2*(r:ℝ)*n*(kappa α)^R ≤ E := by dsimp [E, movementOverhead]; linarith
  have hEC : movementBoundaryEntropy n b + (b+1)*Real.log 3 - b*Real.log (gamma α) ≤ E := by
    dsimp [E, movementOverhead]; linarith
  let Z := Real.exp ((n:ℝ)*Real.log (gamma α) + E)
  have hK : krylovBound α n r t b ≤ Z + Z := by
    apply (movement_krylov_le hα ha hb).trans
    apply add_le_add <;> apply Real.exp_le_exp.mpr
    · have h := mul_le_mul_of_nonneg_left hbg (Nat.cast_nonneg n)
      linarith
    · linarith
  have hD : descriptorBound α n r R b ≤ Z := by
    apply (movement_descriptor_le hα ha hb).trans
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hug (Nat.cast_nonneg n)
    linarith
  have hC : cubeBound α n b ≤ Z := by
    apply (movement_cube_le hα ha hb).trans
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ 4 * Z := by linarith
    _ = _ := by
      dsimp [Z, movementNumericalError, E]
      rw [movement_pow_exp hg, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 4)]
      ring

end AdaptiveOrthogonalRigidity
