import AdaptiveOrthogonalRigidity.CompatibleCoverCounting
import AdaptiveOrthogonalRigidity.OriginalEdgeCuts
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Compatible-displacement rectangles and support covers

All matching endpoints are distinct original labelled vertices. Compatibility
uses ordinary real adjacency matrices. The deterministic cover is obtained from
an actual maximum support matching.
-/

open scoped BigOperators Classical
noncomputable section
namespace AdaptiveOrthogonalRigidity

/-- Two injective endpoint lists with disjoint images. -/
abbrev CoverEndpoints (n m : ℕ) :=
  {lr : (Fin m → Fin n) × (Fin m → Fin n) //
    Function.Injective lr.1 ∧ Function.Injective lr.2 ∧ ∀ i j, lr.1 i ≠ lr.2 j}

namespace CoverEndpoints
variable {n m : ℕ}
def left (e : CoverEndpoints n m) : Fin m ↪ Fin n := ⟨e.val.1, e.property.1⟩
def right (e : CoverEndpoints n m) : Fin m ↪ Fin n := ⟨e.val.2, e.property.2.1⟩
theorem disjoint (e : CoverEndpoints n m) : ∀ i j, e.left i ≠ e.right j := e.property.2.2

theorem order_le (e : CoverEndpoints n m) : m ≤ n := by
  simpa using Fintype.card_le_of_injective e.left e.left.injective
end CoverEndpoints

theorem coverEndpoints_card_le (n m : ℕ) :
    Fintype.card (CoverEndpoints n m) ≤ n ^ (2 * m) := by
  calc
    _ ≤ Fintype.card ((Fin m → Fin n) × (Fin m → Fin n)) := Fintype.card_subtype_le _
    _ = _ := by simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ← pow_add, ← two_mul]

/-- A compatible displacement is allowed to depend on the sampled graph. -/
def CompatibleDisplacement {n : ℕ} (A D : RealMatrix n) : Prop :=
  (∀ i j, D i j = D j i) ∧ (∀ i, D i i = 0) ∧
    (∀ i j, D i j = -1 ∨ D i j = 0 ∨ D i j = 1) ∧ Ordinary (A + D)

/-- A k-edge support matching, oriented and ordered only for its rectangle. -/
def HasSupportMatching {n : ℕ} (D : RealMatrix n) (k : ℕ) : Prop :=
  ∃ e : CoverEndpoints n k, ∀ i, D (e.left i) (e.right i) ≠ 0

/-- The exact fully adaptive bad event in the compatible-displacement cover. -/
def compatibleCoverBadEvent (n : ℕ) (lam : ℝ) : Set (GraphSample n) :=
  {ω | ∃ D : RealMatrix n, D ≠ 0 ∧ CompatibleDisplacement (adjacency ω) D ∧
    ∃ k : ℕ, (k : ℝ) ≥ lam * D.rank ∧ HasSupportMatching D k}

/-- Compatibility of a prescribed ternary rectangle on original endpoint sets. -/
def coverRectangleEvent {n m : ℕ} (e : CoverEndpoints n m) (N : CoverMatrix m) : Set (GraphSample n) :=
  {ω | ∀ i j, adjacency ω (e.left i) (e.right j) + coverValue (N i j) = 0 ∨
    adjacency ω (e.left i) (e.right j) + coverValue (N i j) = 1}

/-- Any actual displacement matching has order at most the ambient vertex set. -/
theorem HasSupportMatching.order_le {n k : ℕ} {D : RealMatrix n}
    (h : HasSupportMatching D k) : k ≤ n := by obtain ⟨e, _⟩ := h; exact e.order_le

/-- The empty matching always exists, including at order zero. -/
theorem hasSupportMatching_zero {n : ℕ} (D : RealMatrix n) : HasSupportMatching D 0 := by
  refine ⟨⟨(Fin.elim0, Fin.elim0), ?_⟩, ?_⟩
  · exact ⟨by intro i; exact Fin.elim0 i, by intro i; exact Fin.elim0 i,
      by intro i; exact Fin.elim0 i⟩
  · intro i; exact Fin.elim0 i


/-- Add a support edge whose endpoints avoid all existing matching endpoints. -/
def CoverEndpoints.cons {n k : ℕ} (e : CoverEndpoints n k) (i j : Fin n)
    (hij : i ≠ j) (hi : ∀ a, i ≠ e.left a ∧ i ≠ e.right a)
    (hj : ∀ a, j ≠ e.left a ∧ j ≠ e.right a) : CoverEndpoints n (k + 1) := by
  refine ⟨(Fin.cons i e.left, Fin.cons j e.right), ?_, ?_, ?_⟩
  · exact Fin.cons_injective_of_injective (by rintro ⟨a, ha⟩; exact (hi a).1 ha.symm)
      e.left.injective
  · exact Fin.cons_injective_of_injective (by rintro ⟨a, ha⟩; exact (hj a).2 ha.symm)
      e.right.injective
  · intro a b
    cases a using Fin.cases <;> cases b using Fin.cases
    · exact hij
    · exact (hi _).2
    · exact Ne.symm (hj _).1
    · exact e.disjoint _ _

/-- Endpoints of a maximum support matching cover every support edge. -/
theorem exists_matching_endpoint_cover {n : ℕ} (D : RealMatrix n)
    (hdiag : ∀ i, D i i = 0) :
    ∃ (k : ℕ) (e : CoverEndpoints n k) (S : Finset (Fin n)),
      (∀ a, D (e.left a) (e.right a) ≠ 0) ∧ S.card ≤ 2 * k ∧
      ∀ i ∉ S, ∀ j ∉ S, D i j = 0 := by
  let C := (Finset.range (n + 1)).filter (HasSupportMatching D)
  have hC : C.Nonempty := ⟨0, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), hasSupportMatching_zero D⟩⟩
  obtain ⟨k, hk, hmax⟩ := C.exists_max_image id hC
  obtain ⟨e, he⟩ := (Finset.mem_filter.mp hk).2
  let S := Finset.univ.image e.left ∪ Finset.univ.image e.right
  have hcard : S.card ≤ 2 * k := by
    have h₁ : (Finset.univ.image e.left).card ≤ k := by
      simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := e.left))
    have h₂ : (Finset.univ.image e.right).card ≤ k := by
      simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := e.right))
    exact (Finset.card_union_le _ _).trans (by omega)
  refine ⟨k, e, S, he, hcard, ?_⟩
  intro i hi j hj
  by_contra hn
  have hij : i ≠ j := by rintro rfl; exact hn (hdiag i)
  have hix (a : Fin k) : i ≠ e.left a ∧ i ≠ e.right a := by
    constructor
    · intro h; apply hi; exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, h.symm⟩)
    · intro h; apply hi; exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, h.symm⟩)
  have hjx (a : Fin k) : j ≠ e.left a ∧ j ≠ e.right a := by
    constructor
    · intro h; apply hj; exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, h.symm⟩)
    · intro h; apply hj; exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, h.symm⟩)
  let e' := e.cons i j hij hix hjx
  have he' : HasSupportMatching D (k + 1) := by
    refine ⟨e', ?_⟩
    intro a
    cases a using Fin.cases
    · exact hn
    · exact he _
  have hk' : k + 1 ∈ C := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le he'.order_le), he'⟩
  have hh := hmax (k + 1) hk'
  dsimp only [id] at hh
  omega

/-- Outside the exact bad event, every nonzero compatible displacement is
supported on fewer than twice lambda times its real rank vertices. -/
theorem support_cover_of_not_bad {n : ℕ} {lam : ℝ} {ω : GraphSample n}
    (hgood : ω ∉ compatibleCoverBadEvent n lam) (D : RealMatrix n)
    (hD : D ≠ 0) (hcomp : CompatibleDisplacement (adjacency ω) D) :
    ∃ S : Finset (Fin n), (S.card : ℝ) < 2 * lam * D.rank ∧
      ∀ i ∉ S, ∀ j ∉ S, D i j = 0 := by
  obtain ⟨k, e, S, he, hcard, hcover⟩ := exists_matching_endpoint_cover D hcomp.2.1
  have hk : (k : ℝ) < lam * D.rank := by
    by_contra hn
    exact hgood ⟨D, hD, hcomp, k, le_of_not_gt hn, e, he⟩
  refine ⟨S, ?_, hcover⟩
  have hc : (S.card : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hcard
  nlinarith

end AdaptiveOrthogonalRigidity
