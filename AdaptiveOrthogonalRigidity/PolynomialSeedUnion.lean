import AdaptiveOrthogonalRigidity.PolynomialSeedFibers

open MeasureTheory Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable abbrev LowF3Polynomial (d : ℕ) := Polynomial.degreeLT (ZMod 3) (d + 1)

noncomputable instance lowF3PolynomialFintype (d : ℕ) : Fintype (LowF3Polynomial d) :=
  Fintype.ofEquiv (Fin (d + 1) → ZMod 3) (Polynomial.degreeLTEquiv (ZMod 3) (d + 1)).toEquiv.symm

theorem lowF3Polynomial_card (d : ℕ) : Fintype.card (LowF3Polynomial d) = 3 ^ (d + 1) := by
  rw [Fintype.card_congr (Polynomial.degreeLTEquiv (ZMod 3) (d + 1)).toEquiv]
  simp

theorem lowF3Polynomial_degree {d : ℕ} (q : LowF3Polynomial d) : q.val.natDegree ≤ d := by
  apply Polynomial.natDegree_le_of_degree_le
  apply Polynomial.mem_degreeLE.mp
  have h := q.property
  change q.val ∈ Polynomial.degreeLT (ZMod 3) (d + 1) at h
  rw [Polynomial.degreeLT_succ_eq_degreeLE] at h
  exact h

noncomputable def seedPolynomialFailure {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (d : ℕ) (M : Matrix ι ι (ZMod 3)) (v : ι → ZMod 3) : Set (ι × κ → Bool) :=
  {Y | ∃ q : Option κ → LowF3Polynomial d, (∃ j : κ, (q (some j)).val ≠ 0) ∧
    (Polynomial.aeval M (q none).val).mulVec v +
      ∑ j, (Polynomial.aeval M (q (some j)).val).mulVec (boolVector (fun i => Y (i, j))) = 0}

/-- All coefficient tuples are counted before conditioning on the fresh seed
columns. Coefficients may be chosen adaptively from the complete rectangle. -/
theorem polynomial_seed_union_bound {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (d h : ℕ) (M : Matrix ι ι (ZMod 3)) (v : ι → ZMod 3)
    (hgood : ∀ q : Polynomial (ZMod 3), q ≠ 0 → q.natDegree ≤ d →
      Module.finrank (ZMod 3) (Polynomial.aeval M q).mulVecLin.ker ≤ h)
    {α : ℝ} (hα : 0 ≤ α) (hαhalf : α ≤ 1 / 2)
    (p : ι × κ → unitInterval) (hp : ∀ ij, α ≤ (p ij : ℝ) ∧ (p ij : ℝ) ≤ 1 - α) :
    (cubeMeasure p).real (seedPolynomialFailure d M v) ≤
      (3 : ℝ) ^ ((d + 1) * (Fintype.card κ + 1)) *
        (beta α) ^ ((Fintype.card ι : ℝ) - h) := by
  let E (q : Option κ → LowF3Polynomial d) : Set (ι × κ → Bool) :=
    {Y | (∃ j : κ, (q (some j)).val ≠ 0) ∧
      (Polynomial.aeval M (q none).val).mulVec v +
        ∑ j, (Polynomial.aeval M (q (some j)).val).mulVec (boolVector (fun i => Y (i, j))) = 0}
  let D := (beta α) ^ ((Fintype.card ι : ℝ) - h)
  have hE (q : Option κ → LowF3Polynomial d) : (cubeMeasure p).real (E q) ≤ D := by
    by_cases hex : ∃ j : κ, (q (some j)).val ≠ 0
    · obtain ⟨j, hj⟩ := hex
      have hsub : E q ⊆ {Y | ∑ k, (Polynomial.aeval M (q (some k)).val).mulVec
          (boolVector (fun i => Y (i, k))) = -(Polynomial.aeval M (q none).val).mulVec v} := by
        intro Y hY
        exact eq_neg_of_add_eq_zero_right hY.2
      exact (measureReal_mono hsub).trans (matrix_seed_relation_bound hα hαhalf p hp
        (fun k => Polynomial.aeval M (q (some k)).val) j h
        (hgood _ hj (lowF3Polynomial_degree _)) _)
    · have he : E q = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro Y hY
        exact hex hY.1
      rw [he, measureReal_empty]
      exact Real.rpow_nonneg (by dsimp [beta]; linarith) _
  have hsub : seedPolynomialFailure d M v ⊆ ⋃ q, E q := by
    rintro Y ⟨q, hq⟩
    exact Set.mem_iUnion.mpr ⟨q, hq⟩
  calc
    _ ≤ (cubeMeasure p).real (⋃ q, E q) := measureReal_mono hsub
    _ ≤ ∑ q, (cubeMeasure p).real (E q) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _q : Option κ → LowF3Polynomial d, D := Finset.sum_le_sum (fun q _ => hE q)
    _ = _ := by simp [D, lowF3Polynomial_card, ← pow_mul]

end AdaptiveOrthogonalRigidity
