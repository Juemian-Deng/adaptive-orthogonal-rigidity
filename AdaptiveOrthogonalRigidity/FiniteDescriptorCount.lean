import AdaptiveOrthogonalRigidity.PackedActionProbability
import Mathlib.Tactic.LinearCombination

open MeasureTheory Matrix
open scoped BigOperators Classical
noncomputable section
namespace AdaptiveOrthogonalRigidity

/-- A nonzero output coefficient determines one actual coordinate in every row. -/
theorem matrix_eq_of_mulVec_and_other_columns {K : Type*} [Field K] {N k : ℕ}
    (X Y : Matrix (Fin N) (Fin k) K) (a : Fin k → K) (j : Fin k) (hj : a j ≠ 0)
    (hXa : X.mulVec a = Y.mulVec a)
    (hother : ∀ i l, l ≠ j → X i l = Y i l) : X = Y := by
  ext i l
  by_cases hl : l = j
  · subst l
    have hrow := congrFun hXa i
    change (∑ l, X i l * a l) = ∑ l, Y i l * a l at hrow
    have hs : (∑ l ∈ Finset.univ.erase j, X i l * a l) =
        ∑ l ∈ Finset.univ.erase j, Y i l * a l := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [hother i l (Finset.mem_erase.mp hl).1]
    rw [← Finset.sum_erase_add Finset.univ (fun l => X i l * a l) (Finset.mem_univ j),
      ← Finset.sum_erase_add Finset.univ (fun l => Y i l * a l) (Finset.mem_univ j), hs] at hrow
    exact mul_right_cancel₀ hj (add_left_cancel hrow)
  · exact hother i l hl

/-- Candidate matrices and all binary output vectors, with the nonzero coefficient retained. -/
abbrev BinaryOutputCandidate {N k : ℕ} (a : Fin k → ZMod 3) (b : Fin N → ZMod 3) :=
  {t : Matrix (Fin N) (Fin k) (ZMod 3) × (Fin N → Bool) //
    a ≠ 0 ∧ boolVector t.2 = t.1.mulVec a + b}

/-- Exactly one coordinate per row is determined. The binary vector is counted here,
not again in the later union bound. -/
theorem binary_output_candidate_card {N k : ℕ} (a : Fin k → ZMod 3) (b : Fin N → ZMod 3) :
    Fintype.card (BinaryOutputCandidate a b) ≤ 2 ^ N * 3 ^ ((k - 1) * N) := by
  by_cases ha : a = 0
  · let : IsEmpty (BinaryOutputCandidate a b) := ⟨fun x => x.property.1 ha⟩
    simp
  · have hex : ∃ j, a j ≠ 0 := by
      by_contra hn
      push Not at hn
      exact ha (funext hn)
    obtain ⟨j, hj⟩ := hex
    let code : BinaryOutputCandidate a b →
        (Fin N → Bool) × ((Fin N × RemainingCoordinates j) → ZMod 3) :=
      fun x => (x.val.2, fun q => x.val.1 q.1 q.2.val)
    have hinj : Function.Injective code := by
      intro x y he
      have hz : x.val.2 = y.val.2 := congrArg Prod.fst he
      have hother : ∀ i l, l ≠ j → x.val.1 i l = y.val.1 i l := by
        intro i l hl
        exact congrFun (congrArg Prod.snd he) (i, ⟨l, hl⟩)
      have hXa : x.val.1.mulVec a = y.val.1.mulVec a := by
        apply add_right_cancel (b := b)
        rw [← x.property.2, ← y.property.2, hz]
      exact Subtype.ext (Prod.ext (matrix_eq_of_mulVec_and_other_columns _ _ a j hj hXa hother) hz)
    have hrem : Fintype.card (RemainingCoordinates j) = k - 1 := by
      have hc := Fintype.card_congr (singleIndexEquiv j)
      simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin] at hc
      omega
    have hc := Fintype.card_le_of_injective code hinj
    simpa [Fintype.card_prod, Fintype.card_fun, hrem, Nat.mul_comm] using hc

/-- All descriptor coefficients, including the nonzero output direction before filtering. -/
abbrev DescriptorCoefficients (k d : ℕ) :=
  (Matrix (Fin k) (Fin k) (ZMod 3) × Matrix (Fin k) (Fin k) (ZMod 3)) ×
  (Matrix (Fin d) (Fin k) (ZMod 3) × Matrix (Fin d) (Fin k) (ZMod 3)) ×
  ((Fin k → ZMod 3) × (Fin d → ZMod 3))

theorem f3_matrix_card (m n : ℕ) :
    Fintype.card (Matrix (Fin m) (Fin n) (ZMod 3)) = 3 ^ (m * n) := by
  let e : Matrix (Fin m) (Fin n) (ZMod 3) ≃ ((Fin m × Fin n) → ZMod 3) := {
    toFun := fun M q => M q.1 q.2
    invFun := fun v i j => v (i, j)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }
  rw [Fintype.card_congr e]
  simp

theorem descriptor_coefficients_card (k d : ℕ) :
    Fintype.card (DescriptorCoefficients k d) = 3 ^ (2 * k ^ 2 + 2 * d * k + k + d) := by
  unfold DescriptorCoefficients
  simp only [Fintype.card_prod, f3_matrix_card, Fintype.card_fun,
    Fintype.card_fin, ZMod.card, ← pow_add]
  congr 1
  ring

/-- Exact cancellation of the candidate count with the packed-action atom factor. -/
theorem descriptor_count_power_identity {N k R : ℕ} (hk : 1 ≤ k) (hkR : k * R ≤ N)
    (A : ℕ) :
    (3 : ℝ) ^ A * (2 : ℝ) ^ N * 3 ^ ((k - 1) * N) *
        (1 / 3 : ℝ) ^ (k * (N - k * R)) =
      (2 / 3 : ℝ) ^ N * 3 ^ (A + k ^ 2 * R) := by
  have he : (k - 1) * N + N = k * (N - k * R) + k ^ 2 * R := by
    have h₁ := Nat.sub_add_cancel hk
    have h₂ := Nat.sub_add_cancel hkR
    nlinarith
  have hp : (3 : ℝ) ^ ((k - 1) * N) * 3 ^ N =
      3 ^ (k * (N - k * R)) * 3 ^ (k ^ 2 * R) := by
    rw [← pow_add, ← pow_add, he]
  rw [div_pow, div_pow, one_pow, pow_add]
  field_simp
  exact hp

/-- The full finite descriptor event, including every binary output. -/
def packedDescriptorEvent {N k R d : ℕ} (diag : Fin N → ZMod 3)
    (V : Matrix (Fin N) (Fin d) (ZMod 3)) : Set (GraphSample N) :=
  {ω | ∃ (X : Matrix (Fin N) (Fin k) (ZMod 3))
    (E M : Matrix (Fin k) (Fin k) (ZMod 3))
    (F B : Matrix (Fin d) (Fin k) (ZMod 3))
    (a : Fin k → ZMod 3) (q : Fin d → ZMod 3) (z : Fin N → Bool),
      fieldGraphMatrix (ZMod 3) N diag ω * (X * E + V * F) = X * M + V * B ∧
      DisjointRowBases (fun i => (X * E + V * F) i) R ∧ a ≠ 0 ∧
      boolVector z = X.mulVec a + V.mulVec q}

/-- The manuscript's exact finite packed-descriptor count and probability bound. -/
theorem finite_descriptor_probability {N k R d : ℕ} {α : ℝ}
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) (hk : 1 ≤ k) (hR : 1 ≤ R) (hkR : k * R ≤ N)
    (p : EdgeParameters N) (hp : Admissible α p) (diag : Fin N → ZMod 3)
    (V : Matrix (Fin N) (Fin d) (ZMod 3)) :
    eventProbability p (packedDescriptorEvent (k := k) (R := R) diag V) ≤
      (2 / 3 : ℝ) ^ N * 3 ^ (2 * k ^ 2 + 2 * d * k + k + d + k ^ 2 * R) *
        (1 + 2 * (kappa α) ^ R) ^ (k * (N - k * R)) := by
  let A := 2 * k ^ 2 + 2 * d * k + k + d
  let S := Σ c : DescriptorCoefficients k d,
    BinaryOutputCandidate c.2.2.1 (V.mulVec c.2.2.2)
  let C := (1 / 3 : ℝ) ^ (k * (N - k * R)) *
    (1 + 2 * (kappa α) ^ R) ^ (k * (N - k * R))
  let Evt : S → Set (GraphSample N) := fun s =>
    {ω | fieldGraphMatrix (ZMod 3) N diag ω * (s.2.val.1 * s.1.1.1 + V * s.1.2.1.1) =
        s.2.val.1 * s.1.1.2 + V * s.1.2.1.2 ∧
      DisjointRowBases (fun i => (s.2.val.1 * s.1.1.1 + V * s.1.2.1.1) i) R}
  have hC : 0 ≤ C := by
    have hkap := kappa_nonneg α
    dsimp [C]
    positivity
  have hEvt (s : S) : eventProbability p (Evt s) ≤ C := by
    by_cases hpk : DisjointRowBases (fun i => (s.2.val.1 * s.1.1.1 + V * s.1.2.1.1) i) R
    · exact (measureReal_mono (fun _ h => h.1)).trans
        (packed_action_probability hα hαhalf hk hR p hp diag _ _ hpk hkR)
    · have he : Evt s = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro ω hω
        exact hpk hω.2
      rw [he]
      simpa [eventProbability] using hC
  have hsub : packedDescriptorEvent (k := k) (R := R) diag V ⊆ ⋃ s : S, Evt s := by
    rintro ω ⟨X, E, M, F, B, a, q, z, hact, hpk, ha, hz⟩
    exact Set.mem_iUnion.mpr ⟨⟨((E, M), (F, B), (a, q)), ⟨(X, z), ha, hz⟩⟩, hact, hpk⟩
  have hcard : Fintype.card S ≤ 3 ^ A * (2 ^ N * 3 ^ ((k - 1) * N)) := by
    calc
      _ = ∑ c : DescriptorCoefficients k d,
          Fintype.card (BinaryOutputCandidate c.2.2.1 (V.mulVec c.2.2.2)) := Fintype.card_sigma
      _ ≤ ∑ _c : DescriptorCoefficients k d, 2 ^ N * 3 ^ ((k - 1) * N) :=
        Finset.sum_le_sum (fun c _ => binary_output_candidate_card _ _)
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, descriptor_coefficients_card]
  calc
    _ ≤ eventProbability p (⋃ s : S, Evt s) := measureReal_mono hsub
    _ ≤ ∑ s : S, eventProbability p (Evt s) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _s : S, C := Finset.sum_le_sum (fun s _ => hEvt s)
    _ = (Fintype.card S : ℝ) * C := by simp
    _ ≤ ((3 : ℝ) ^ A * (2 ^ N * 3 ^ ((k - 1) * N))) * C :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hC
    _ = ((3 : ℝ) ^ A * 2 ^ N * 3 ^ ((k - 1) * N) *
        (1 / 3 : ℝ) ^ (k * (N - k * R))) *
          (1 + 2 * (kappa α) ^ R) ^ (k * (N - k * R)) := by dsimp [C]; ring
    _ = _ := by rw [descriptor_count_power_identity hk hkR A]

end AdaptiveOrthogonalRigidity
