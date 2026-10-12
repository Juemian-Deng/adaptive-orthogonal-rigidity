import AdaptiveOrthogonalRigidity.TrainingTesting
import AdaptiveOrthogonalRigidity.NecessaryNorms

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

noncomputable def injectionSplitEquiv {ι ν : Type*} (f : ι ↪ ν) :
    (ι ⊕ {k : ν // k ∉ Set.range f}) ≃ ν :=
  (Equiv.sumCongr (Equiv.ofInjective f f.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range f))

@[simp] theorem injectionSplitEquiv_inl {ι ν : Type*} (f : ι ↪ ν) (i : ι) :
    injectionSplitEquiv f (Sum.inl i) = f i := by
  rfl

/-- Arbitrary injective selections of original bit coordinates retain their
heterogeneous product law exactly, including for existential real events. -/
theorem cube_injective_projection_probability {ι ν : Type*}
    [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
    (p : ν → unitInterval) (f : ι ↪ ν) (E : Set (ι → Bool)) :
    (cubeMeasure p).real {X | (fun i => X (f i)) ∈ E} =
      (cubeMeasure (fun i => p (f i))).real E := by
  rw [cube_event_probability_split p (injectionSplitEquiv f)]
  have he (x : ι → Bool) (r : {k : ν // k ∉ Set.range f} → Bool) :
      (fun i => splitAssignmentEquiv (injectionSplitEquiv f) (x, r) (f i)) = x := by
    funext i
    change Sum.elim x r ((injectionSplitEquiv f).symm (f i)) = x i
    rw [← injectionSplitEquiv_inl f i]
    rw [Equiv.symm_apply_apply]
    rfl
  simp only [Set.mem_ofPred_eq, he, injectionSplitEquiv_inl]
  rw [← Finset.sum_mul, cubeWeight_sum, one_mul]
  rfl

def edgeOfDistinct {n : ℕ} (i j : Fin n) (hij : i ≠ j) : Edge n :=
  if h : i < j then ⟨(i, j), h⟩ else ⟨(j, i), lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hij)⟩

theorem edgeOfDistinct_endpoints {n : ℕ} (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l)
    (he : edgeOfDistinct i j hij = edgeOfDistinct k l hkl) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  have h := congrArg Subtype.val he
  unfold edgeOfDistinct at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inr ⟨h.2, h.1⟩
  · exact Or.inl ⟨h.2, h.1⟩

theorem adjacency_edgeOfDistinct {n : ℕ} (ω : GraphSample n) (i j : Fin n) (hij : i ≠ j) :
    adjacency ω i j = bitValue (ω (edgeOfDistinct i j hij)) := by
  unfold adjacency edgeOfDistinct
  split_ifs with h h'
  · rfl
  · rfl
  · exact False.elim (hij (le_antisymm (le_of_not_gt h') (le_of_not_gt h)))

/-- A directed cut cannot identify two unordered original edges, because a
swapped identification would put a vertex on both sides of the cut. -/
noncomputable def cutEdgeEmbedding {n : ℕ} {ι κ : Type*}
    (left : ι ↪ Fin n) (right : κ ↪ Fin n)
    (hdisj : ∀ i j, left i ≠ right j) : (ι × κ) ↪ Edge n where
  toFun q := edgeOfDistinct (left q.1) (right q.2) (hdisj q.1 q.2)
  inj' := by
    intro a b he
    rcases edgeOfDistinct_endpoints _ _ _ _ _ _ he with h | h
    · exact Prod.ext (left.injective h.1) (right.injective h.2)
    · exact False.elim (hdisj a.1 b.2 h.1)

/-- The complete original adjacency rectangle has exactly the independent bit
law; its heterogeneous parameters are read from the same unordered edges. -/
theorem original_cut_event_probability {n : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (p : EdgeParameters n) (left : ι ↪ Fin n) (right : κ ↪ Fin n)
    (hdisj : ∀ i j, left i ≠ right j) (E : Set ((ι × κ) → Bool)) :
    eventProbability p {ω | (fun e => ω (cutEdgeEmbedding left right hdisj e)) ∈ E} =
      (cubeMeasure (fun e => p (cutEdgeEmbedding left right hdisj e))).real E :=
  cube_injective_projection_probability p (cutEdgeEmbedding left right hdisj) E

theorem original_cut_matrix {n : ℕ} {ι κ : Type*} (ω : GraphSample n)
    (left : ι ↪ Fin n) (right : κ ↪ Fin n) (hdisj : ∀ i j, left i ≠ right j) :
    (fun i j => adjacency ω (left i) (right j)) =
      cubeMatrix (R := ℝ) (fun e => ω (cutEdgeEmbedding left right hdisj e)) := by
  funext i j
  exact adjacency_edgeOfDistinct ω (left i) (right j) (hdisj i j)

def familyCutIndexEquiv {σ κ : Type*} (ι : σ → Type*) :
    (Σ s, ι s × κ) ≃ ((Σ s, ι s) × κ) where
  toFun q := (⟨q.1, q.2.1⟩, q.2.2)
  invFun q := ⟨q.1.1, q.1.2, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def familyCutEdgeEmbedding {n : ℕ} {σ κ : Type*} (ι : σ → Type*)
    (left : (Σ s, ι s) ↪ Fin n) (right : κ ↪ Fin n)
    (hdisj : ∀ i j, left i ≠ right j) : (Σ s, ι s × κ) ↪ Edge n :=
  (familyCutIndexEquiv ι).toEmbedding.trans (cutEdgeEmbedding left right hdisj)

/-- Whole left-block events are independent although all blocks share the right
vertex set. Each event is arbitrary, so existential real vectors are included. -/
theorem original_left_block_events_independent {n : ℕ} {σ κ : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]
    (ι : σ → Type*) [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
    (p : EdgeParameters n) (left : (Σ s, ι s) ↪ Fin n) (right : κ ↪ Fin n)
    (hdisj : ∀ i j, left i ≠ right j) (E : ∀ s, Set (ι s × κ → Bool)) :
    eventProbability p {ω | ∀ s,
      (fun e => ω (familyCutEdgeEmbedding ι left right hdisj ⟨s, e⟩)) ∈ E s} =
      ∏ s, (cubeMeasure (fun e => p (familyCutEdgeEmbedding ι left right hdisj ⟨s, e⟩))).real (E s) := by
  exact (cube_injective_projection_probability p (familyCutEdgeEmbedding ι left right hdisj)
    {X | ∀ s, (fun e => X ⟨s, e⟩) ∈ E s}).trans
      (cube_family_event_probability (fun s => ι s × κ) _ E)

end AdaptiveOrthogonalRigidity
