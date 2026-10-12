import AdaptiveOrthogonalRigidity.RestrictedBlocks

open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- A binary row has an integer squared norm between zero and its length. -/
theorem binary_row_squared_norm {κ : Type*} [Fintype κ] [DecidableEq κ]
    (v : κ → ℝ) (hv : ∀ k, v k = 0 ∨ v k = 1) :
    ∃ m : ℕ, m ≤ Fintype.card κ ∧ ∑ k, v k ^ 2 = m := by
  let s := Finset.univ.filter (fun k => v k = 1)
  refine ⟨s.card, Finset.card_le_card (Finset.filter_subset _ _), ?_⟩
  have h (k : κ) : v k ^ 2 = if v k = 1 then 1 else 0 := by
    rcases hv k with hk | hk <;> simp [hk]
  simp_rw [h]
  simp [s]

/-- Eliminating the unknown right orthogonal block does not enumerate any real
entries: its binary output row has exactly the input Gram squared norm. -/
theorem transformed_row_gram_norm {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (X : Matrix ι κ ℝ) (V : Matrix κ κ ℝ)
    (hV : V * V.transpose = 1) (u : ι → ℝ) :
    quadraticValue (X * X.transpose) u =
      ∑ k, (Matrix.vecMul (Matrix.vecMul u X) V k) ^ 2 := by
  have hgram : (X * V) * (X * V).transpose = X * X.transpose := by
    rw [Matrix.transpose_mul]
    calc
      X * V * (V.transpose * X.transpose) = X * (V * V.transpose) * X.transpose := by
        simp only [Matrix.mul_assoc]
      _ = X * X.transpose := by rw [hV, Matrix.mul_one]
  rw [← hgram, quadratic_gram_eq_sum_squares]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  change Matrix.vecMul u (X * V) k = Matrix.vecMul (Matrix.vecMul u X) V k
  rw [← Matrix.vecMul_vecMul]

theorem binary_transformed_row_integer_norm {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (X : Matrix ι κ ℝ) (V : Matrix κ κ ℝ)
    (hV : V * V.transpose = 1) (u : ι → ℝ)
    (hbinary : ∀ k, Matrix.vecMul (Matrix.vecMul u X) V k = 0 ∨
      Matrix.vecMul (Matrix.vecMul u X) V k = 1) :
    ∃ m : ℕ, m ≤ Fintype.card κ ∧ quadraticValue (X * X.transpose) u = m := by
  rw [transformed_row_gram_norm X V hV u]
  exact binary_row_squared_norm _ hbinary

def blockSubmatrix {n : ℕ} (A : RealMatrix n) (s : Setoid (Fin n)) (i j : Fin n) :
    Matrix {k // s.r i k} {k // s.r j k} ℝ := fun k l => A k.val l.val

theorem physical_block_row_orthogonal {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (s : Setoid (Fin n)) (hs : ∀ i j, ¬ s.r i j → Q i j = 0) (j : Fin n) :
    blockSubmatrix Q s j j * (blockSubmatrix Q s j j).transpose = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, blockSubmatrix]
  rw [sum_subtype_eq_of_zero (s.r j) (fun k => Q a.val k * Q b.val k)]
  · have h := congrFun (congrFun hQ.2 a.val) b.val
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Subtype.ext_iff] using h
  · intro k hk
    rw [hs a.val k (fun h => hk (s.trans a.property h)), zero_mul]

theorem physical_block_column_orthogonal {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (s : Setoid (Fin n)) (hs : ∀ i j, ¬ s.r i j → Q i j = 0) (j : Fin n) :
    (blockSubmatrix Q s j j).transpose * blockSubmatrix Q s j j = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, blockSubmatrix]
  rw [sum_subtype_eq_of_zero (s.r j) (fun k => Q k a.val * Q k b.val)]
  · have h := congrFun (congrFun hQ.1 a.val) b.val
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Subtype.ext_iff] using h
  · intro k hk
    rw [hs k a.val (fun h => hk (s.trans a.property (s.symm h))), zero_mul]

/-- Restricting a block-diagonal conjugation retains the complete binary
rectangle between the two chosen physical blocks. -/
theorem physical_conjugate_rectangle {n : ℕ} (A Q : RealMatrix n)
    (s : Setoid (Fin n)) (hs : ∀ i j, ¬ s.r i j → Q i j = 0) (i j : Fin n) :
    blockSubmatrix (conjugate A Q) s i j =
      (blockSubmatrix Q s i i).transpose * blockSubmatrix A s i j * blockSubmatrix Q s j j := by
  ext a b
  simp only [blockSubmatrix, conjugate, Matrix.mul_apply, Matrix.transpose_apply]
  rw [← sum_subtype_eq_of_zero (s.r j)
    (fun k => (∑ l, Q l a.val * A l k) * Q k b.val)]
  · apply Finset.sum_congr rfl
    intro k _
    congr 1
    rw [sum_subtype_eq_of_zero (s.r i) (fun l => Q l a.val * A l k.val)]
    intro l hl
    rw [hs l a.val (fun h => hl (s.trans a.property (s.symm h))), zero_mul]
  · intro k hk
    rw [hs k b.val (fun h => hk (s.trans b.property (s.symm h))), mul_zero]

/-- Each original physical-block rectangle supplies the necessary bounded
integer norm, for the actual restricted witness column. -/
theorem physical_witness_integer_norm {n : ℕ} (A Q B : RealMatrix n)
    (hQ : Orthogonal Q) (hB : Ordinary B) (hBQA : B = conjugate A Q)
    (s : Setoid (Fin n)) (hs : ∀ i j, ¬ s.r i j → Q i j = 0) (i j : Fin n) :
    ∃ m : ℕ, m ≤ Fintype.card {k : Fin n // s.r j k} ∧
      quadraticValue (blockSubmatrix A s i j * (blockSubmatrix A s i j).transpose)
        (restrictedColumn Q s i) = m := by
  apply binary_transformed_row_integer_norm (blockSubmatrix A s i j)
    (blockSubmatrix Q s j j) (physical_block_row_orthogonal Q hQ s hs j)
    (restrictedColumn Q s i)
  intro k
  have heq := physical_conjugate_rectangle A Q s hs i j
  have hent := congrFun (congrFun heq ⟨i, s.refl i⟩) k
  have hrow : Matrix.vecMul (Matrix.vecMul (restrictedColumn Q s i) (blockSubmatrix A s i j))
      (blockSubmatrix Q s j j) k = B i k.val := by
    rw [hBQA]
    simpa [blockSubmatrix, restrictedColumn, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Matrix.transpose_apply] using hent.symm
  rw [hrow]
  exact hB.2.2 i k.val

/-- Necessary Gram constraints indexed only by a physical partition and the
original graph. The same unknown unit vector must satisfy every right block. -/
def blockGramEvent (n b : ℕ) : Set (GraphSample n) :=
  {ω | ∃ s : Setoid (Fin n),
    (∀ i, Nat.card {j : Fin n // s.r i j} ≤ b) ∧
    (∃ i, 2 ≤ Nat.card {j : Fin n // s.r i j}) ∧
    ∀ i, 2 ≤ Nat.card {j : Fin n // s.r i j} →
      ∃ u : {k : Fin n // s.r i k} → ℝ,
        (∑ k, u k ^ 2 = 1) ∧ ¬ IsSignedCoordinate u ∧
        ∀ j, ∃ m : ℕ, m ≤ Fintype.card {k : Fin n // s.r j k} ∧
          quadraticValue (blockSubmatrix (adjacency ω) s i j *
            (blockSubmatrix (adjacency ω) s i j).transpose) u = m}

/-- No real witness is enumerated or fixed before sampling: all full adaptive
block witnesses imply the partition-only necessary event. -/
theorem blockEvent_subset_blockGramEvent (n b : ℕ) : blockEvent n b ⊆ blockGramEvent n b := by
  intro ω hω
  obtain ⟨Q, B, hQ, hB, hBQA, hnoniso, s, hsize, hs, hnon⟩ :=
    blockEvent_subset_noncoordinateBlockEvent n b hω
  refine ⟨s, hsize, ?_, ?_⟩
  · exact physical_witness_nontrivial_block (adjacency ω) Q B
      (adjacency_ordinary ω) hQ hB hBQA hnoniso s hs
  · intro i hi
    refine ⟨restrictedColumn Q s i, restrictedColumn_norm Q hQ s hs i,
      restrictedColumn_noncoordinate Q s hs i (hnon i hi), ?_⟩
    intro j
    exact physical_witness_integer_norm (adjacency ω) Q B hQ hB hBQA s hs i j

end AdaptiveOrthogonalRigidity
