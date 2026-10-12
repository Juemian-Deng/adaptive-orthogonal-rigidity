import AdaptiveOrthogonalRigidity.GramAtoms

open MeasureTheory
open scoped BigOperators

namespace AdaptiveOrthogonalRigidity

def F3Binary (z : ZMod 3) : Prop := z = 0 ∨ z = 1

def AffineCanonical {ι : Type*} [DecidableEq ι] (c : ZMod 3) (a : ι → ZMod 3) : Prop :=
  (a = 0 ∧ F3Binary c) ∨ ∃ i,
    (a = Pi.single i 1 ∧ c = 0) ∨ (a = Pi.single i (-1) ∧ c = 1)

def affineCubeValue {ι : Type*} [Fintype ι] (c : ZMod 3) (a : ι → ZMod 3)
    (x : ι → Bool) : ZMod 3 := c + a ⬝ᵥ boolVector x

private theorem two_variable_forbidden : ∀ c a b : ZMod 3, a ≠ 0 → b ≠ 0 →
    ∃ ab : Bool × Bool, ¬ F3Binary (c + a * bitValue ab.1 + b * bitValue ab.2) := by unfold F3Binary bitValue; decide

private theorem one_variable_forbidden : ∀ c a : ZMod 3, a ≠ 0 →
    ¬ ((a = 1 ∧ c = 0) ∨ (a = -1 ∧ c = 1)) →
    ∃ v : Bool, ¬ F3Binary (c + a * bitValue v) := by unfold F3Binary bitValue; decide

theorem affineCubeValue_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ZMod 3) (a : ι → ZMod 3) (i j : ι) (hij : i ≠ j)
    (r : OtherCoordinates i j → Bool) (u v : Bool) :
    affineCubeValue c a (patchTwo i j r u v) =
      affineCubeValue c a (patchTwo i j r false false) + a i * bitValue u + a j * bitValue v := by
  unfold affineCubeValue
  rw [boolVector_patchTwo i j hij]
  simp only [dotProduct_add, dotProduct_single]
  ring

/-- Every noncanonical affine F3 functional misses a Boolean value with mass
at least alpha squared in the genuine heterogeneous product cube. -/
theorem affine_cube_atom {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : ι → unitInterval) (hp : ∀ i, α ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ 1 - α)
    (c : ZMod 3) (a : ι → ZMod 3) (hcan : ¬ AffineCanonical c a) :
    (cubeMeasure p).real {x | F3Binary (affineCubeValue c a x)} ≤ 1 - α ^ 2 := by
  classical
  by_cases htwo : ∃ i j, i ≠ j ∧ a i ≠ 0 ∧ a j ≠ 0
  · obtain ⟨i, j, hij, hi, hj⟩ := htwo
    apply cube_event_le_of_pair_missing p i j hij hα (hp i) (hp j)
    intro r
    obtain ⟨uv, huv⟩ := two_variable_forbidden (affineCubeValue c a (patchTwo i j r false false))
      (a i) (a j) hi hj
    refine ⟨uv, ?_⟩
    change ¬ F3Binary (affineCubeValue c a (patchTwo i j r uv.1 uv.2))
    rwa [affineCubeValue_pair c a i j hij]
  · by_cases ha : a = 0
    · have hc : ¬ F3Binary c := fun hc => hcan (Or.inl ⟨ha, hc⟩)
      have hempty : {x | F3Binary (affineCubeValue c a x)} = (∅ : Set (ι → Bool)) := by
        ext x
        simp [affineCubeValue, ha, hc]
      rw [hempty, measureReal_empty]
      nlinarith
    · have hex : ∃ i, a i ≠ 0 := by
        by_contra! h
        exact ha (funext h)
      obtain ⟨i, hi⟩ := hex
      have hs : a = Pi.single i (a i) := by
        funext j
        by_cases hj : j = i
        · subst j; simp
        · have hz : a j = 0 := by
            by_contra hz
            exact htwo ⟨i, j, Ne.symm hj, hi, hz⟩
          simp [hj, hz]
      have hbad : ¬ ((a i = 1 ∧ c = 0) ∨ (a i = -1 ∧ c = 1)) := by
        rintro (⟨ha1, hc⟩ | ⟨ha1, hc⟩)
        · exact hcan (Or.inr ⟨i, Or.inl ⟨by simpa only [ha1] using hs, hc⟩⟩)
        · exact hcan (Or.inr ⟨i, Or.inr ⟨by simpa only [ha1] using hs, hc⟩⟩)
      obtain ⟨v, hv⟩ := one_variable_forbidden c (a i) hi hbad
      have hprob := cube_atom_le_of_single_missing p i hα (hp i)
        (fun x => decide (F3Binary (affineCubeValue c a x))) true (by
          intro r
          refine ⟨v, ?_⟩
          have heq : affineCubeValue c a (singleAssignmentEquiv i (r, v)) = c + a i * bitValue v := by
            unfold affineCubeValue
            conv_lhs => rw [hs]
            simp [single_dotProduct, boolVector, singleAssignmentEquiv, patchOne]
          rw [heq]
          intro hh
          exact hv (of_decide_eq_true hh))
      have hprob' : (cubeMeasure p).real {x | F3Binary (affineCubeValue c a x)} ≤ 1 - α := by
        simpa using hprob
      exact hprob'.trans (by nlinarith [mul_nonneg hα (sub_nonneg.mpr hα1)])

end AdaptiveOrthogonalRigidity
