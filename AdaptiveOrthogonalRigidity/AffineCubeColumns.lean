import AdaptiveOrthogonalRigidity.AffineCubeProbability

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

def CanonicalBoolColumn {ι κ : Type*} (Y : ι → κ → Bool) (z : ι → Bool) : Prop :=
  z = (fun _ => false) ∨ z = (fun _ => true) ∨
    ∃ j, z = (fun i => Y i j) ∨ z = (fun i => !(Y i j))

theorem bitValue_f3_injective : Function.Injective (bitValue (R := ZMod 3)) := by
  intro a b h
  cases a <;> cases b
  · rfl
  · norm_num [bitValue] at h
  · norm_num [bitValue] at h
  · rfl

theorem bitValue_not {R : Type*} [Ring R] (b : Bool) :
    bitValue (R := R) (!b) = 1 - bitValue b := by cases b <;> simp [bitValue]

theorem affineCanonical_column {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (Y : ι → κ → Bool) (c : ZMod 3) (a : κ → ZMod 3) (h : AffineCanonical c a) :
    ∃ z : ι → Bool, CanonicalBoolColumn Y z ∧
      ∀ i, affineCubeValue c a (Y i) = bitValue (z i) := by
  rcases h with ⟨ha, hc | hc⟩ | ⟨j, ⟨ha, hc⟩ | ⟨ha, hc⟩⟩
  · exact ⟨fun _ => false, Or.inl rfl, by simp [affineCubeValue, ha, hc, bitValue]⟩
  · exact ⟨fun _ => true, Or.inr (Or.inl rfl), by simp [affineCubeValue, ha, hc, bitValue]⟩
  · exact ⟨fun i => Y i j, Or.inr (Or.inr ⟨j, Or.inl rfl⟩), by
      simp [affineCubeValue, ha, hc, single_dotProduct, boolVector]⟩
  · refine ⟨fun i => !(Y i j), Or.inr (Or.inr ⟨j, Or.inr rfl⟩), ?_⟩
    intro i
    simp [affineCubeValue, ha, hc, single_dotProduct, boolVector, bitValue_not, sub_eq_add_neg]

def augmentedCubeMatrix {ι κ : Type*} (Y : ι → κ → Bool) : Matrix ι (Option κ) (ZMod 3) :=
  fun i j => j.elim 1 (fun j => bitValue (Y i j))

theorem augmentedCubeMatrix_mulVec {ι κ : Type*} [Fintype κ]
    (Y : ι → κ → Bool) (q : Option κ → ZMod 3) (i : ι) :
    (augmentedCubeMatrix Y).mulVec q i = affineCubeValue (q none) (fun j => q (some j)) (Y i) := by
  simp [Matrix.mulVec, dotProduct, augmentedCubeMatrix, affineCubeValue,
    boolVector, Fintype.sum_option, mul_comm]

/-- A binary vector in the augmented F3 column span which is not on the exact
canonical Boolean list necessarily has a noncanonical affine coefficient. -/
theorem noncanonical_column_affine_witness {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (Y : ι → κ → Bool) (z : ι → Bool)
    (hz : boolVector (R := ZMod 3) z ∈ Set.range (augmentedCubeMatrix Y).mulVec)
    (hnot : ¬ CanonicalBoolColumn Y z) :
    ∃ c : ZMod 3, ∃ a : κ → ZMod 3, ¬ AffineCanonical c a ∧
      ∀ i, F3Binary (affineCubeValue c a (Y i)) := by
  obtain ⟨q, hq⟩ := hz
  refine ⟨q none, fun j => q (some j), ?_, ?_⟩
  · intro hc
    obtain ⟨w, hw, heval⟩ := affineCanonical_column Y _ _ hc
    have hzw : z = w := by
      funext i
      apply bitValue_f3_injective
      have hi := congrFun hq i
      rw [augmentedCubeMatrix_mulVec] at hi
      exact hi.symm.trans (heval i)
    exact hnot (hzw.symm ▸ hw)
  · intro i
    have hi := congrFun hq i
    rw [augmentedCubeMatrix_mulVec] at hi
    rw [hi]
    cases z i <;> simp [boolVector, bitValue, F3Binary]

/-- The full affine binary-cube lemma on a prescribed original graph cut. -/
theorem original_graph_binary_column_bound {n : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : EdgeParameters n) (hp : Admissible α p)
    (left : ι ↪ Fin n) (right : κ ↪ Fin n) (hdisj : ∀ i j, left i ≠ right j) :
    eventProbability p {ω | let Y := fun i j => ω (edgeOfDistinct (left i) (right j) (hdisj i j))
      ∃ z : ι → Bool, boolVector (R := ZMod 3) z ∈ Set.range (augmentedCubeMatrix Y).mulVec ∧
        ¬ CanonicalBoolColumn Y z} ≤
      (3 : ℝ) ^ (Fintype.card κ + 1) * (gamma α) ^ Fintype.card ι := by
  refine (measureReal_mono ?_ (by finiteness)).trans
    (original_graph_affine_cube hα hα1 p hp left right hdisj)
  rintro ω ⟨z, hz, hnot⟩
  exact noncanonical_column_affine_witness _ z hz hnot

end AdaptiveOrthogonalRigidity
