import AdaptiveOrthogonalRigidity.IntegerLift
import AdaptiveOrthogonalRigidity.GramAtoms

open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

theorem symmetric_trace_values_determine {ι δ : Type*} [Fintype ι] [DecidableEq ι]
    (G : δ → SymmetricSpace ℝ ι) (hspan : Submodule.span ℝ (Set.range G) = ⊤)
    (T U : SymmetricSpace ℝ ι)
    (hvalues : ∀ i, (T.val * (G i).val).trace = (U.val * (G i).val).trace) : T = U := by
  apply sub_eq_zero.mp
  apply symmetric_trace_nondegenerate (by norm_num : (2 : ℝ) ≠ 0)
  intro K
  let f := symmetricTracePair ℝ ι (T - U)
  have hker : Submodule.span ℝ (Set.range G) ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (((T - U).val) * (G i).val).trace = 0
    simp [Matrix.sub_mul, Matrix.trace_sub, hvalues i]
  rw [hspan] at hker
  exact hker (Submodule.mem_top : K ∈ (⊤ : Submodule ℝ (SymmetricSpace ℝ ι)))

def boundedTraceCandidates {ι δ : Type*} [Fintype ι]
    (G : δ → SymmetricSpace ℝ ι) (b : ℕ) : Set (SymmetricSpace ℝ ι) :=
  {T | ∀ i, ∃ m : ℕ, m ≤ b ∧ (T.val * (G i).val).trace = m}

noncomputable def boundedTraceCode {ι δ : Type*} [Fintype ι]
    (G : δ → SymmetricSpace ℝ ι) (b : ℕ) (T : boundedTraceCandidates G b) : δ → Fin (b + 1) :=
  fun i => ⟨Classical.choose (T.property i), Nat.lt_succ_of_le (Classical.choose_spec (T.property i)).1⟩

theorem boundedTraceCode_value {ι δ : Type*} [Fintype ι]
    (G : δ → SymmetricSpace ℝ ι) (b : ℕ) (T : boundedTraceCandidates G b) (i : δ) :
    (T.val.val * (G i).val).trace = ((boundedTraceCode G b T i).val : ℝ) :=
  (Classical.choose_spec (T.property i)).2

theorem boundedTraceCode_injective {ι δ : Type*} [Fintype ι] [DecidableEq ι]
    (G : δ → SymmetricSpace ℝ ι) (hspan : Submodule.span ℝ (Set.range G) = ⊤) (b : ℕ) :
    Function.Injective (boundedTraceCode G b) := by
  intro T U hcode
  apply Subtype.ext
  apply symmetric_trace_values_determine G hspan T.val U.val
  intro i
  rw [boundedTraceCode_value, boundedTraceCode_value, hcode]

/-- Finite projector identification uses only trace values on a genuine spanning
list. It does not assume a height bound or enumerate arbitrary real entries. -/
theorem bounded_trace_candidates_finite {ι δ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype δ] [DecidableEq δ]
    (G : δ → SymmetricSpace ℝ ι) (hspan : Submodule.span ℝ (Set.range G) = ⊤) (b : ℕ) :
    (boundedTraceCandidates G b).Finite := by
  have : Finite (boundedTraceCandidates G b) :=
    Finite.of_injective (boundedTraceCode G b) (boundedTraceCode_injective G hspan b)
  exact Set.toFinite _

theorem bounded_trace_candidates_card {ι δ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype δ] [DecidableEq δ]
    (G : δ → SymmetricSpace ℝ ι) (hspan : Submodule.span ℝ (Set.range G) = ⊤) (b : ℕ) :
    Nat.card (boundedTraceCandidates G b) ≤ (b + 1) ^ Fintype.card δ := by
  have : Finite (boundedTraceCandidates G b) :=
    (bounded_trace_candidates_finite G hspan b).to_subtype
  let := Fintype.ofFinite (boundedTraceCandidates G b)
  rw [Nat.card_eq_fintype_card]
  have h := Fintype.card_le_of_injective _ (boundedTraceCode_injective G hspan b)
  simpa using h

def vectorProjector {ι : Type*} (u : ι → ℝ) : SymmetricSpace ℝ ι :=
  ⟨fun i j => u i * u j, Matrix.IsSymm.ext (fun _ _ => mul_comm _ _)⟩

theorem vectorProjector_trace {ι : Type*} [Fintype ι] (u : ι → ℝ) (G : Matrix ι ι ℝ) :
    ((vectorProjector u).val * G).trace = quadraticValue G u := by
  change (∑ i, ∑ j, u i * u j * G j i) = ∑ i, u i * (∑ j, G i j * u j)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

def IsNoncoordinateProjector {ι : Type*} [Fintype ι] (T : SymmetricSpace ℝ ι) : Prop :=
  ∃ u : ι → ℝ, (∑ i, u i ^ 2 = 1) ∧ ¬ IsSignedCoordinate u ∧ T = vectorProjector u

/-- Complete integer-training finite-candidate bound. Spanning is required only
modulo three; the real identification and selected training list are proved. -/
theorem integer_training_candidates_bound {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    (G : τ → SymmetricSpace ℤ ι)
    (hspan : Submodule.span (ZMod 3) (Set.range (fun t => castSymmetric (ZMod 3) (G t))) = ⊤)
    (b : ℕ) :
    (boundedTraceCandidates (fun t => castSymmetric ℝ (G t)) b).Finite ∧
      Nat.card (boundedTraceCandidates (fun t => castSymmetric ℝ (G t)) b) ≤
        (b + 1) ^ (Fintype.card ι * (Fintype.card ι + 1) / 2) := by
  obtain ⟨select, hs⟩ := integer_symmetric_spanning_selection G hspan
  let Gs := fun i => castSymmetric ℝ (G (select i))
  have hsub : boundedTraceCandidates (fun t => castSymmetric ℝ (G t)) b ⊆
      boundedTraceCandidates Gs b := by
    intro T hT i
    exact hT (select i)
  have hfin := bounded_trace_candidates_finite Gs hs b
  refine ⟨hfin.subset hsub, ?_⟩
  have hc := bounded_trace_candidates_card Gs hs b
  have : Finite (boundedTraceCandidates Gs b) := hfin.to_subtype
  have hle : Nat.card (boundedTraceCandidates (fun t => castSymmetric ℝ (G t)) b) ≤
      Nat.card (boundedTraceCandidates Gs b) :=
    Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
  apply hle.trans
  simpa only [Sym2.card, Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm] using hc

end AdaptiveOrthogonalRigidity
