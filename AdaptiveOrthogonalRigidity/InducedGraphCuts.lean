import AdaptiveOrthogonalRigidity.GraphRelabeling
import AdaptiveOrthogonalRigidity.KrylovProbability

open MeasureTheory Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

def inducedEdgeEmbedding {N n : ℕ} (left : Fin N ↪ Fin n) : Edge N ↪ Edge n where
  toFun q := edgeOfDistinct (left q.val.1) (left q.val.2) (left.injective.ne (ne_of_lt q.property))
  inj' := by
    intro q r h
    rcases edgeOfDistinct_endpoints _ _ _ _ _ _ h with h | h
    · exact Subtype.ext (Prod.ext (left.injective h.1) (left.injective h.2))
    · have h1 := left.injective h.1
      have h2 := left.injective h.2
      have hlt := r.property
      rw [← h1, ← h2] at hlt
      exact False.elim ((not_lt_of_ge q.property.le) hlt)

/-- Bulk edges and cut edges are disjoint original unordered coordinates. -/
noncomputable def cutBulkEdgeEmbedding {N n : ℕ} {κ : Type*}
    (left : Fin N ↪ Fin n) (right : κ ↪ Fin n) (hdisj : ∀ i j, left i ≠ right j) :
    ((Fin N × κ) ⊕ Edge N) ↪ Edge n where
  toFun := Sum.elim (cutEdgeEmbedding left right hdisj) (inducedEdgeEmbedding left)
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl ((cutEdgeEmbedding left right hdisj).injective h)
      | inr b =>
        rcases edgeOfDistinct_endpoints (left a.1) (right a.2) (left b.val.1) (left b.val.2)
          (hdisj a.1 a.2) (left.injective.ne (ne_of_lt b.property)) h with he | he
        · exact False.elim (hdisj b.val.2 a.2 he.2.symm)
        · exact False.elim (hdisj b.val.1 a.2 he.2.symm)
    | inr a =>
      cases b with
      | inl b =>
        rcases edgeOfDistinct_endpoints (left a.val.1) (left a.val.2) (left b.1) (right b.2)
          (left.injective.ne (ne_of_lt a.property)) (hdisj b.1 b.2) h with he | he
        · exact False.elim (hdisj a.val.2 b.2 he.2)
        · exact False.elim (hdisj a.val.1 b.2 he.1)
      | inr b => exact congrArg Sum.inr ((inducedEdgeEmbedding left).injective h)

theorem fieldGraphMatrix_induced {K : Type*} [Zero K] [One K] {N n : ℕ}
    (left : Fin N ↪ Fin n) (diag : Fin n → K) (ω : GraphSample n) :
    fieldGraphMatrix K N (fun i => diag (left i)) (fun e => ω (inducedEdgeEmbedding left e)) =
      (fieldGraphMatrix K n diag ω).submatrix left left := by
  ext i j
  simp only [Matrix.submatrix_apply]
  by_cases hij : i < j
  · rw [fieldGraphMatrix_upper N _ _ i j hij,
      fieldGraphMatrix_offdiag n diag ω (left i) (left j) (left.injective.ne (ne_of_lt hij))]
    rfl
  · by_cases hji : j < i
    · rw [← (fieldGraphMatrix_isSymm N (fun i => diag (left i)) (fun e => ω (inducedEdgeEmbedding left e))).apply i j,
        ← (fieldGraphMatrix_isSymm n diag ω).apply (left i) (left j),
        fieldGraphMatrix_upper N _ _ j i hji,
        fieldGraphMatrix_offdiag n diag ω (left j) (left i) (left.injective.ne (ne_of_lt hji))]
      rfl
    · have heq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      subst j
      simp only [fieldGraphMatrix_diag]

/-- The exact finite Krylov bound embedded into an original graph's prescribed
principal block and cross block. All unused graph edges are integrated out. -/
theorem original_graph_krylov_bound {N n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (left : Fin N ↪ Fin n) (right : κ ↪ Fin n) (hdisj : ∀ i j, left i ≠ right j)
    (d t : ℕ) (diag : Fin N → ZMod 3) (v : Fin N → ZMod 3) (hv : v ≠ 0)
    {α : ℝ} (hα : 0 ≤ α) (hαhalf : α ≤ 1 / 2)
    (p : EdgeParameters n) (hp : Admissible α p) :
    eventProbability p {ω | (fun e => ω (cutBulkEdgeEmbedding left right hdisj e)) ∈
      blockKrylovFailure N d diag v} ≤
      ((3 : ℝ) ^ ((d + 1) * (Fintype.card κ + 1)) + markPairCount d) *
        (beta α) ^ ((N : ℝ) - 1 - d * t) +
      2 * rootCount d * (2 : ℝ) ^ N * (beta α) ^ (((t : ℝ) ^ 2 - 1) / 4) := by
  rw [show eventProbability p {ω | (fun e => ω (cutBulkEdgeEmbedding left right hdisj e)) ∈
      blockKrylovFailure N d diag v} =
      (cubeMeasure (fun e => p (cutBulkEdgeEmbedding left right hdisj e))).real
        (blockKrylovFailure N d diag v) from
    cube_injective_projection_probability p (cutBulkEdgeEmbedding left right hdisj) _]
  exact block_krylov_probability_bound N d t diag v hv hα hαhalf _
    (fun e => hp (cutBulkEdgeEmbedding left right hdisj e))

end AdaptiveOrthogonalRigidity
