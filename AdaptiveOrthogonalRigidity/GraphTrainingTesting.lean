import AdaptiveOrthogonalRigidity.OriginalEdgeCuts

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

def rectangleSplitIndexEquiv {ι σ τ : Type*} (ρ : σ → Type*) (κ : τ → Type*) :
    ((Σ t, ι × κ t) ⊕ (Σ s, ι × ρ s)) ≃
      (ι × ((Σ t, κ t) ⊕ (Σ s, ρ s))) where
  toFun x := match x with
    | Sum.inl ⟨t, i, k⟩ => (i, Sum.inl ⟨t, k⟩)
    | Sum.inr ⟨s, i, k⟩ => (i, Sum.inr ⟨s, k⟩)
  invFun x := match x.2 with
    | Sum.inl ⟨t, k⟩ => Sum.inl ⟨t, x.1, k⟩
    | Sum.inr ⟨s, k⟩ => Sum.inr ⟨s, x.1, k⟩
  left_inv x := by rcases x with ⟨t, i, k⟩ | ⟨s, i, k⟩ <;> rfl
  right_inv x := by rcases x with ⟨i, ⟨t, k⟩ | ⟨s, k⟩⟩ <;> rfl

noncomputable def rectangleSplitEdgeEmbedding {n : ℕ} {ι σ τ : Type*}
    (ρ : σ → Type*) (κ : τ → Type*)
    (left : ι ↪ Fin n) (right : ((Σ t, κ t) ⊕ (Σ s, ρ s)) ↪ Fin n)
    (hdisj : ∀ i j, left i ≠ right j) :
    ((Σ t, ι × κ t) ⊕ (Σ s, ι × ρ s)) ↪ Edge n :=
  (rectangleSplitIndexEquiv ρ κ).toEmbedding.trans (cutEdgeEmbedding left right hdisj)

def adjacencyRectangle {n : ℕ} {ι κ : Type*} (ω : GraphSample n)
    (left : ι → Fin n) (right : κ → Fin n) : Matrix ι κ ℝ :=
  fun i j => adjacency ω (left i) (right j)

/-- Fixed disjoint original vertex blocks have the complete adaptive
training/testing bound, with the same heterogeneous unordered-edge law. -/
theorem original_graph_training_testing {n : ℕ} {ι σ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    (ρ : σ → Type*) (κ : τ → Type*)
    [∀ s, Fintype (ρ s)] [∀ s, DecidableEq (ρ s)] [∀ s, Nonempty (ρ s)]
    [∀ t, Fintype (κ t)] [∀ t, DecidableEq (κ t)] [∀ t, Nonempty (κ t)]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (b : ℕ)
    (p : EdgeParameters n) (hp : Admissible α p)
    (left : ι ↪ Fin n) (right : ((Σ t, κ t) ⊕ (Σ s, ρ s)) ↪ Fin n)
    (hdisj : ∀ i j, left i ≠ right j) :
    eventProbability p {ω | ∃ u : ι → ℝ, (∑ i, u i ^ 2 = 1) ∧ ¬ IsSignedCoordinate u ∧
      (∀ s, ∃ m : ℕ, m ≤ b ∧
        quadraticValue (adjacencyRectangle ω left (fun k => right (Sum.inr ⟨s, k⟩)) *
          (adjacencyRectangle ω left (fun k => right (Sum.inr ⟨s, k⟩))).transpose) u = m) ∧
      ∀ t, ∃ k : ℤ,
        quadraticValue (adjacencyRectangle ω left (fun k => right (Sum.inl ⟨t, k⟩)) *
          (adjacencyRectangle ω left (fun k => right (Sum.inl ⟨t, k⟩))).transpose) u = k} ≤
      (3 : ℝ) ^ (Fintype.card ι * (Fintype.card ι + 1) / 2) * (1 - α ^ 2) ^ Fintype.card σ +
        (b + 1 : ℝ) ^ (Fintype.card ι * (Fintype.card ι + 1) / 2) *
          (1 - α ^ 2) ^ Fintype.card τ := by
  let f := rectangleSplitEdgeEmbedding ρ κ left right hdisj
  let E : Set (((Σ t, ι × κ t) ⊕ (Σ s, ι × ρ s)) → Bool) :=
    {X | ∃ u : ι → ℝ, (∑ i, u i ^ 2 = 1) ∧ ¬ IsSignedCoordinate u ∧
      (∀ s, ∃ m : ℕ, m ≤ b ∧
        quadraticValue (gramSymmetric (R := ℝ) (fun e => X (Sum.inr ⟨s, e⟩))).val u = m) ∧
      ∀ t, ∃ k : ℤ,
        quadraticValue (gramSymmetric (R := ℝ) (fun e => X (Sum.inl ⟨t, e⟩))).val u = k}
  have htrain (ω : GraphSample n) (s : σ) :
      cubeMatrix (R := ℝ) (fun e => ω (f (Sum.inr ⟨s, e⟩))) =
        adjacencyRectangle ω left (fun k => right (Sum.inr ⟨s, k⟩)) := by
    ext i k
    exact (adjacency_edgeOfDistinct ω (left i) (right (Sum.inr ⟨s, k⟩))
      (hdisj i (Sum.inr ⟨s, k⟩))).symm
  have htest (ω : GraphSample n) (t : τ) :
      cubeMatrix (R := ℝ) (fun e => ω (f (Sum.inl ⟨t, e⟩))) =
        adjacencyRectangle ω left (fun k => right (Sum.inl ⟨t, k⟩)) := by
    ext i k
    exact (adjacency_edgeOfDistinct ω (left i) (right (Sum.inl ⟨t, k⟩))
      (hdisj i (Sum.inl ⟨t, k⟩))).symm
  have hb := adaptive_rectangle_training_testing ρ κ hα hα1 b (fun e => p (f e)) (fun e => hp (f e))
  change (cubeMeasure (fun e => p (f e))).real E ≤ _ at hb
  rw [← cube_injective_projection_probability p f E] at hb
  simp only [E, Set.mem_ofPred_eq, gramSymmetric, htrain, htest] at hb
  exact hb

end AdaptiveOrthogonalRigidity
