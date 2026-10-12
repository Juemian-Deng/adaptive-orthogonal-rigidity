import AdaptiveOrthogonalRigidity.LastGraphCoordinates

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

def relabelEdgeEmbedding {n : ℕ} (e : Equiv.Perm (Fin n)) : Edge n ↪ Edge n where
  toFun q := edgeOfDistinct (e q.val.1) (e q.val.2) (e.injective.ne (ne_of_lt q.property))
  inj' := by
    intro q r h
    rcases edgeOfDistinct_endpoints _ _ _ _ _ _ h with h | h
    · exact Subtype.ext (Prod.ext (e.injective h.1) (e.injective h.2))
    · have h1 := e.injective h.1
      have h2 := e.injective h.2
      have hlt := r.property
      rw [← h1, ← h2] at hlt
      exact False.elim ((not_lt_of_ge q.property.le) hlt)

def relabelGraph {n : ℕ} (e : Equiv.Perm (Fin n)) (ω : GraphSample n) : GraphSample n :=
  fun q => ω (relabelEdgeEmbedding e q)

theorem fieldGraphMatrix_offdiag {K : Type*} [Zero K] [One K] (n : ℕ)
    (diag : Fin n → K) (ω : GraphSample n) (i j : Fin n) (hij : i ≠ j) :
    fieldGraphMatrix K n diag ω i j = bitValue (ω (edgeOfDistinct i j hij)) := by
  by_cases h : i < j
  · rw [fieldGraphMatrix_upper n diag ω i j h]
    simp only [edgeOfDistinct, dite_eq_left h]
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hij)
    rw [← (fieldGraphMatrix_isSymm n diag ω).apply i j, fieldGraphMatrix_upper n diag ω j i hji]
    simp only [edgeOfDistinct, dite_eq_right h]

theorem fieldGraphMatrix_relabel {K : Type*} [Zero K] [One K] (n : ℕ)
    (e : Equiv.Perm (Fin n)) (diag : Fin n → K) (ω : GraphSample n) :
    fieldGraphMatrix K n (diag ∘ e) (relabelGraph e ω) = (fieldGraphMatrix K n diag ω).submatrix e e := by
  ext i j
  simp only [Matrix.submatrix_apply]
  by_cases hij : i < j
  · rw [fieldGraphMatrix_upper n _ _ i j hij,
      fieldGraphMatrix_offdiag n diag ω (e i) (e j) (e.injective.ne (ne_of_lt hij))]
    rfl
  · by_cases hji : j < i
    · rw [← (fieldGraphMatrix_isSymm n (diag ∘ e) (relabelGraph e ω)).apply i j,
        ← (fieldGraphMatrix_isSymm n diag ω).apply (e i) (e j),
        fieldGraphMatrix_upper n _ _ j i hji,
        fieldGraphMatrix_offdiag n diag ω (e j) (e i) (e.injective.ne (ne_of_lt hji))]
      rfl
    · have heq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      subst j
      simp only [fieldGraphMatrix_diag, Function.comp_apply]

theorem fieldGraphMatrix_relabel_aeval {K : Type*} [Field K] (n : ℕ)
    (e : Equiv.Perm (Fin n)) (diag : Fin n → K) (ω : GraphSample n)
    (q : Polynomial K) (v : Fin n → K) :
    (Polynomial.aeval (fieldGraphMatrix K n (diag ∘ e) (relabelGraph e ω)) q).mulVec (v ∘ e) =
      (Polynomial.aeval (fieldGraphMatrix K n diag ω) q).mulVec v ∘ e := by
  let M := fieldGraphMatrix K n diag ω
  have h (v : Fin n → K) : (M.mulVec v) ∘ e = (M.submatrix e e).mulVec (v ∘ e) := by
    rw [Matrix.submatrix_mulVec_equiv]
    have hv : (v ∘ e) ∘ e.symm = v := by funext i; simp [Function.comp_def]
    rw [hv]
  rw [fieldGraphMatrix_relabel]
  have he := linearMap_aeval_intertwine (LinearMap.funLeft K K e) M.mulVecLin (M.submatrix e e).mulVecLin h q v
  rw [← matrix_mulVecLin_aeval, ← matrix_mulVecLin_aeval] at he
  exact he.symm

end AdaptiveOrthogonalRigidity
