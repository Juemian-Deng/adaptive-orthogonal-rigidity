import AdaptiveOrthogonalRigidity.BoundaryDescriptors

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Packing uses actual row sets and is preserved by a bijective relabelling
of those original rows. No fresh randomness is introduced. -/
theorem disjointRowBases_reindex {K ι ν : Type*} [Field K] [Fintype ι] [Fintype ν]
    [DecidableEq ι] [DecidableEq ν] {k R : ℕ}
    (u : ι → Fin k → K) (e : ν ≃ ι) (h : DisjointRowBases u R) :
    DisjointRowBases (fun i => u (e i)) R := by
  obtain ⟨I, hd, hI, hc⟩ := h
  refine ⟨fun a => (I a).map e.symm.toEmbedding, ?_, ?_, ?_⟩
  · intro a b hab
    exact (Finset.disjoint_map e.symm.toEmbedding).mpr (hd hab)
  · intro a
    have hmem (i : (I a).map e.symm.toEmbedding) : e i.val ∈ I a := by
      obtain ⟨j, hj, he⟩ := Finset.mem_map.mp i.property
      have hij : e i.val = j := by rw [← he]; exact e.apply_symm_apply j
      rw [hij]
      exact hj
    let f : (I a).map e.symm.toEmbedding → I a := fun i => ⟨e i.val, hmem i⟩
    have hf : Function.Injective f := by
      intro i j he
      apply Subtype.ext
      apply e.injective
      exact congrArg Subtype.val he
    exact (hI a).comp f hf
  · intro a
    simpa only [Finset.card_map] using hc a

/-- Change only row and input labels in a full packed descriptor. The same
state columns and the same selected binary output are retained. -/
theorem packed_descriptor_reindex {ι τ : Type*} [Fintype ι] [Fintype τ]
    [DecidableEq ι] [DecidableEq τ] {N d k R : ℕ}
    (e : Fin N ≃ ι) (f : Fin d ≃ τ)
    (C : Matrix ι ι (ZMod 3)) (V : Matrix ι τ (ZMod 3))
    (X : Matrix ι (Fin k) (ZMod 3))
    (E M : Matrix (Fin k) (Fin k) (ZMod 3))
    (F B : Matrix τ (Fin k) (ZMod 3))
    (a : Fin k → ZMod 3) (q : τ → ZMod 3) (z : ι → Bool)
    (hact : C * (X * E + V * F) = X * M + V * B)
    (hpk : DisjointRowBases (fun i => (X * E + V * F) i) R)
    (ha : a ≠ 0) (hz : boolVector z = X.mulVec a + V.mulVec q) :
    ∃ (X' : Matrix (Fin N) (Fin k) (ZMod 3))
      (E' M' : Matrix (Fin k) (Fin k) (ZMod 3))
      (F' B' : Matrix (Fin d) (Fin k) (ZMod 3))
      (a' : Fin k → ZMod 3) (q' : Fin d → ZMod 3) (z' : Fin N → Bool),
      C.submatrix e e * (X' * E' + V.submatrix e f * F') = X' * M' + V.submatrix e f * B' ∧
      DisjointRowBases (fun i => (X' * E' + V.submatrix e f * F') i) R ∧ a' ≠ 0 ∧
      boolVector z' = X'.mulVec a' + (V.submatrix e f).mulVec q' := by
  let X' := X.submatrix e id
  let F' := F.submatrix f id
  let B' := B.submatrix f id
  have hu : X' * E + V.submatrix e f * F' = (X * E + V * F).submatrix e id := by
    dsimp [X', F']
    rw [Matrix.submatrix_mul_equiv]
    have hh : X.submatrix e id * E = (X * E).submatrix e id := by
      simpa only [Equiv.coe_refl, Matrix.submatrix_id_id] using
        Matrix.submatrix_mul_equiv X E e (Equiv.refl _) id
    rw [hh, Matrix.submatrix_add]
    rfl
  have hw : X' * M + V.submatrix e f * B' = (X * M + V * B).submatrix e id := by
    dsimp [X', B']
    rw [Matrix.submatrix_mul_equiv]
    have hh : X.submatrix e id * M = (X * M).submatrix e id := by
      simpa only [Equiv.coe_refl, Matrix.submatrix_id_id] using
        Matrix.submatrix_mul_equiv X M e (Equiv.refl _) id
    rw [hh, Matrix.submatrix_add]
    rfl
  refine ⟨X', E, M, F', B', a, (fun j => q (f j)), (fun i => z (e i)), ?_, ?_, ha, ?_⟩
  · rw [hu, hw, Matrix.submatrix_mul_equiv, hact]
  · rw [hu]
    exact disjointRowBases_reindex _ e hpk
  · rw [Matrix.submatrix_mulVec_equiv]
    have heq : ((fun j => q (f j)) ∘ f.symm) = q := by ext j; simp
    rw [heq]
    ext i
    exact congrFun hz (e i)

end AdaptiveOrthogonalRigidity
