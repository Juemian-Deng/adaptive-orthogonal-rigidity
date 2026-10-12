import AdaptiveOrthogonalRigidity.FiniteBounds
import AdaptiveOrthogonalRigidity.AffineCubeAtom
import AdaptiveOrthogonalRigidity.OriginalEdgeCuts

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Failure event before any coefficient is chosen: a noncanonical affine
functional takes Boolean values on every independently sampled row. -/
def affineCubeFailure {ι κ : Type*} [Fintype κ] [DecidableEq κ] :
    Set ((Σ _i : ι, κ) → Bool) :=
  {X | ∃ c : ZMod 3, ∃ a : κ → ZMod 3, ¬ AffineCanonical c a ∧
    ∀ i, F3Binary (affineCubeValue c a (fun j => X ⟨i, j⟩))}

theorem affine_cube_failure_bound {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : (Σ _i : ι, κ) → unitInterval)
    (hp : ∀ e, α ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - α) :
    (cubeMeasure p).real (affineCubeFailure (ι := ι) (κ := κ)) ≤
      (3 : ℝ) ^ (Fintype.card κ + 1) * (gamma α) ^ Fintype.card ι := by
  let C := (gamma α) ^ Fintype.card ι
  have hC : 0 ≤ C := pow_nonneg (by unfold gamma; nlinarith) _
  let E (q : (ZMod 3) × (κ → ZMod 3)) : Set ((Σ _i : ι, κ) → Bool) :=
    {X | ¬ AffineCanonical q.1 q.2 ∧ ∀ i, F3Binary (affineCubeValue q.1 q.2 (fun j => X ⟨i, j⟩))}
  have hE (q : (ZMod 3) × (κ → ZMod 3)) : (cubeMeasure p).real (E q) ≤ C := by
    by_cases hq : AffineCanonical q.1 q.2
    · simpa [E, hq] using hC
    · have ht := cube_family_event_le (fun _i : ι => κ) p
        (fun _i => {x | F3Binary (affineCubeValue q.1 q.2 x)}) (gamma α)
        (fun i => affine_cube_atom hα hα1 (fun j => p ⟨i, j⟩) (fun j => hp ⟨i, j⟩) q.1 q.2 hq)
      exact (measureReal_mono (show E q ⊆ _ from fun X hX => hX.2)).trans ht
  calc
    _ ≤ (cubeMeasure p).real (⋃ q : (ZMod 3) × (κ → ZMod 3), E q) := by
      refine measureReal_mono ?_ (by finiteness)
      rintro X ⟨c, a, hca, hX⟩
      exact Set.mem_iUnion.mpr ⟨(c, a), hca, hX⟩
    _ ≤ ∑ q : (ZMod 3) × (κ → ZMod 3), (cubeMeasure p).real (E q) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _q : (ZMod 3) × (κ → ZMod 3), C := Finset.sum_le_sum (fun q _ => hE q)
    _ = _ := by simp [C, Fintype.card_prod, ZMod.card, pow_succ, mul_comm]

def rowColumnIndexEquiv (ι κ : Type*) : (Σ _i : ι, κ) ≃ ι × κ where
  toFun e := (e.1, e.2)
  invFun e := ⟨e.1, e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact specialization to unordered original graph edges; no transformed
random-matrix independence or graph-independent coefficient is assumed. -/
theorem original_graph_affine_cube {n : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : EdgeParameters n) (hp : Admissible α p)
    (left : ι ↪ Fin n) (right : κ ↪ Fin n) (hdisj : ∀ i j, left i ≠ right j) :
    eventProbability p {ω | ∃ c : ZMod 3, ∃ a : κ → ZMod 3, ¬ AffineCanonical c a ∧
      ∀ i, F3Binary (affineCubeValue c a (fun j => ω (edgeOfDistinct (left i) (right j) (hdisj i j))))} ≤
      (3 : ℝ) ^ (Fintype.card κ + 1) * (gamma α) ^ Fintype.card ι := by
  let f : (Σ _i : ι, κ) ↪ Edge n :=
    (rowColumnIndexEquiv ι κ).toEmbedding.trans (cutEdgeEmbedding left right hdisj)
  exact (cube_injective_projection_probability p f (affineCubeFailure (ι := ι) (κ := κ))).trans_le
    (affine_cube_failure_bound hα hα1 (fun e => p (f e)) (fun e => hp (f e)))

end AdaptiveOrthogonalRigidity
