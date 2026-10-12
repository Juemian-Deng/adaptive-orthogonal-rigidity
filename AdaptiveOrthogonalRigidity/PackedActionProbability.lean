import AdaptiveOrthogonalRigidity.PackedFourierBound
import AdaptiveOrthogonalRigidity.OriginalEdgeCuts
import AdaptiveOrthogonalRigidity.FieldGraphMatrix

open MeasureTheory Matrix
open scoped BigOperators Classical
noncomputable section
namespace AdaptiveOrthogonalRigidity

abbrev OutsidePackedRows {N : ℕ} {P : Type*} (f : P ↪ Fin N) :=
  {i : Fin N // i ∉ Set.range f}

/-- Each remaining row uses its own original edges to the selected packed rows. -/
def packedOutsideCut {N : ℕ} {P : Type*} (f : P ↪ Fin N) :
    (Σ _h : OutsidePackedRows f, P) ↪ Edge N :=
  (Equiv.sigmaEquivProd _ _).toEmbedding.trans
    (cutEdgeEmbedding ⟨Subtype.val, Subtype.val_injective⟩ f
      (fun h t he => h.property ⟨t, he.symm⟩))

@[simp] theorem packed_split_injected {ι ν : Type*} (f : ι ↪ ν)
    (x : ι → Bool) (r : {e : ν // e ∉ Set.range f} → Bool) (i : ι) :
    splitAssignmentEquiv (injectionSplitEquiv f) (x, r) (f i) = x i := by
  change Sum.elim x r ((injectionSplitEquiv f).symm (f i)) = x i
  rw [← injectionSplitEquiv_inl f i, Equiv.symm_apply_apply]
  rfl

@[simp] theorem packed_injectionSplit_inr {ι ν : Type*} (f : ι ↪ ν)
    (e : {e : ν // e ∉ Set.range f}) : injectionSplitEquiv f (Sum.inr e) = e.val := rfl

@[simp] theorem packed_split_remaining {ι ν : Type*} (f : ι ↪ ν)
    (x : ι → Bool) (r : {e : ν // e ∉ Set.range f} → Bool)
    (e : {e : ν // e ∉ Set.range f}) :
    splitAssignmentEquiv (injectionSplitEquiv f) (x, r) e.val = r e := by
  change Sum.elim x r ((injectionSplitEquiv f).symm e.val) = r e
  rw [← packed_injectionSplit_inr f e, Equiv.symm_apply_apply]
  rfl

private theorem packed_fieldGraphMatrix_offdiag {K : Type*} [Zero K] [One K] (N : ℕ)
    (diag : Fin N → K) (ω : GraphSample N) (i j : Fin N) (hij : i ≠ j) :
    fieldGraphMatrix K N diag ω i j = bitValue (ω (edgeOfDistinct i j hij)) := by
  by_cases h : i < j
  · rw [fieldGraphMatrix_upper N diag ω i j h]
    simp only [edgeOfDistinct, dite_eq_left h]
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hij)
    rw [← (fieldGraphMatrix_isSymm N diag ω).apply i j, fieldGraphMatrix_upper N diag ω j i hji]
    simp only [edgeOfDistinct, dite_eq_right h]

theorem packed_split_graph_cut {N : ℕ} {P : Type*} (f : P ↪ Fin N)
    (diag : Fin N → ZMod 3) (x : (Σ _h : OutsidePackedRows f, P) → Bool)
    (r : {e : Edge N // e ∉ Set.range (packedOutsideCut f)} → Bool)
    (h : OutsidePackedRows f) (t : P) :
    fieldGraphMatrix (ZMod 3) N diag
      (splitAssignmentEquiv (injectionSplitEquiv (packedOutsideCut f)) (x, r)) h.val (f t) =
        bitValue (x ⟨h, t⟩) := by
  have hne : h.val ≠ f t := fun he => h.property ⟨t, he.symm⟩
  rw [packed_fieldGraphMatrix_offdiag N diag _ _ _ hne]
  change bitValue (splitAssignmentEquiv (injectionSplitEquiv (packedOutsideCut f))
    (x, r) (packedOutsideCut f ⟨h, t⟩)) = _
  rw [packed_split_injected]

/-- Edges between two remaining rows lie outside the exposed packed cut. -/
theorem packed_outside_edge_not_cut {N : ℕ} {P : Type*} (f : P ↪ Fin N)
    (h l : OutsidePackedRows f) (hne : h.val ≠ l.val) :
    edgeOfDistinct h.val l.val hne ∉ Set.range (packedOutsideCut f) := by
  rintro ⟨⟨h', t⟩, he⟩
  change edgeOfDistinct h'.val (f t) (fun hh => h'.property ⟨t, hh.symm⟩) = edgeOfDistinct h.val l.val hne at he
  rcases edgeOfDistinct_endpoints _ _ _ _ _ _ he with hh | hh
  · exact l.property ⟨t, hh.2⟩
  · exact h.property ⟨t, hh.2⟩

theorem packed_split_graph_remaining {N : ℕ} {P : Type*} (f : P ↪ Fin N)
    (diag : Fin N → ZMod 3) (x : (Σ _h : OutsidePackedRows f, P) → Bool)
    (r : {e : Edge N // e ∉ Set.range (packedOutsideCut f)} → Bool)
    (h l : OutsidePackedRows f) :
    fieldGraphMatrix (ZMod 3) N diag
      (splitAssignmentEquiv (injectionSplitEquiv (packedOutsideCut f)) (x, r)) h.val l.val =
    fieldGraphMatrix (ZMod 3) N diag
      (splitAssignmentEquiv (injectionSplitEquiv (packedOutsideCut f)) ((fun _ => false), r)) h.val l.val := by
  by_cases he : h.val = l.val
  · rw [he, fieldGraphMatrix_diag, fieldGraphMatrix_diag]
  · rw [packed_fieldGraphMatrix_offdiag N diag _ _ _ he,
      packed_fieldGraphMatrix_offdiag N diag _ _ _ he]
    have hn := packed_outside_edge_not_cut f h l he
    have hx := packed_split_remaining (packedOutsideCut f) x r
      ⟨edgeOfDistinct h.val l.val he, hn⟩
    have h0 := packed_split_remaining (packedOutsideCut f) (fun _ => false) r
      ⟨edgeOfDistinct h.val l.val he, hn⟩
    rw [hx, h0]

/-- Exact row decomposition after conditioning on all original edges outside the packed cut. -/
theorem packed_action_split_row {N k : ℕ} {P : Type*} [Fintype P] (f : P ↪ Fin N)
    (diag : Fin N → ZMod 3) (U : Matrix (Fin N) (Fin k) (ZMod 3))
    (x : (Σ _h : OutsidePackedRows f, P) → Bool)
    (r : {e : Edge N // e ∉ Set.range (packedOutsideCut f)} → Bool)
    (h : OutsidePackedRows f) :
    (fieldGraphMatrix (ZMod 3) N diag
      (splitAssignmentEquiv (injectionSplitEquiv (packedOutsideCut f)) (x, r)) * U) h.val =
      f3RowSum (fun t => U (f t)) (fun t => x ⟨h, t⟩) +
        ∑ l : OutsidePackedRows f, fieldGraphMatrix (ZMod 3) N diag
          (splitAssignmentEquiv (injectionSplitEquiv (packedOutsideCut f)) ((fun _ => false), r))
          h.val l.val • U l.val := by
  ext j
  simp only [Matrix.mul_apply, f3RowSum, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← (injectionSplitEquiv f).sum_comp (fun i : Fin N =>
    fieldGraphMatrix (ZMod 3) N diag
      (splitAssignmentEquiv (injectionSplitEquiv (packedOutsideCut f)) (x, r)) h.val i * U i j)]
  simp only [Fintype.sum_sum_type, injectionSplitEquiv_inl, packed_injectionSplit_inr,
    packed_split_graph_cut, packed_split_graph_remaining]

/-- The manuscript's packed-action estimate under the original heterogeneous graph law. -/
theorem packed_action_probability {N k R : ℕ} {α : ℝ}
    (_hα : 0 < α) (_hαhalf : α ≤ 1 / 2) (_hk : 1 ≤ k) (hR : 1 ≤ R)
    (p : EdgeParameters N) (hp : Admissible α p) (diag : Fin N → ZMod 3)
    (U W : Matrix (Fin N) (Fin k) (ZMod 3))
    (hpack : DisjointRowBases (fun i => U i) R) (_hkR : k * R ≤ N) :
    eventProbability p {ω | fieldGraphMatrix (ZMod 3) N diag ω * U = W} ≤
      (1 / 3 : ℝ) ^ (k * (N - k * R)) *
        (1 + 2 * (kappa α) ^ R) ^ (k * (N - k * R)) := by
  obtain ⟨I, hdis, hli, hcard⟩ := hpack
  let P := Σ a : Fin R, I a
  let f : P ↪ Fin N := {
    toFun := fun t => t.2.val
    inj' := by
      rintro ⟨a, i⟩ ⟨b, j⟩ he
      change i.val = j.val at he
      have hab : a = b := by
        by_contra hn
        exact Finset.disjoint_left.mp (hdis hn) i.property (he.symm ▸ j.property)
      subst b
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext he))
  }
  let H := OutsidePackedRows f
  let cut := packedOutsideCut f
  let C := (1 / 3 : ℝ) ^ k * (1 + 2 * (kappa α) ^ R) ^ k
  have hP : Fintype.card P = R * k := by
    simp [P, Fintype.card_sigma, hcard]
  have hH : Fintype.card H = N - k * R := by
    have hs := Fintype.card_congr (injectionSplitEquiv f)
    simp only [Fintype.card_sum, Fintype.card_fin] at hs
    rw [hP, Nat.mul_comm R k] at hs
    dsimp [H, OutsidePackedRows]
    omega
  suffices hh : eventProbability p {ω | fieldGraphMatrix (ZMod 3) N diag ω * U = W} ≤ C ^ Fintype.card H by
    apply hh.trans_eq
    dsimp [C]
    rw [mul_pow, ← pow_mul, ← pow_mul, hH]
  change (cubeMeasure p).real {ω | fieldGraphMatrix (ZMod 3) N diag ω * U = W} ≤ _
  apply cube_event_le_of_split_bound p (injectionSplitEquiv cut)
  intro r
  let z : H → Fin k → ZMod 3 := fun h => W h.val -
    ∑ l : H, fieldGraphMatrix (ZMod 3) N diag
      (splitAssignmentEquiv (injectionSplitEquiv cut) ((fun _ => false), r)) h.val l.val • U l.val
  have hsub : {x | fieldGraphMatrix (ZMod 3) N diag
      (splitAssignmentEquiv (injectionSplitEquiv cut) (x, r)) * U = W} ⊆
      {x | ∀ h : H, f3RowSum (fun t : P => U (f t)) (fun t => x ⟨h, t⟩) = z h} := by
    intro x hx h
    have hr := congrArg (fun M : Matrix (Fin N) (Fin k) (ZMod 3) => M h.val) hx
    rw [packed_action_split_row] at hr
    exact eq_sub_iff_add_eq.mpr hr
  change (cubeMeasure (fun q => p (cut q))).real _ ≤ _
  apply (measureReal_mono hsub).trans
  apply cube_family_event_le (fun _h : H => P) (fun q => p (cut q))
    (fun h => {x | f3RowSum (fun t : P => U (f t)) x = z h}) C
  intro h
  exact f3_basis_family_atom hR (fun a => I a) (fun _a i => U i.val) hli
    (fun a => by simpa using hcard a) (fun t => p (cut ⟨h, t⟩))
    (fun t => hp (cut ⟨h, t⟩)) (z h)

end AdaptiveOrthogonalRigidity
