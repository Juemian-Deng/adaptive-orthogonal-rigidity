import AdaptiveOrthogonalRigidity.SymmetricSpace
import Mathlib.LinearAlgebra.Matrix.Nonsingular

open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

theorem integer_det_real_ne_zero_of_mod_three {δ : Type*} [Fintype δ] [DecidableEq δ]
    (A : Matrix δ δ ℤ) (h3 : (A.map (fun z => (z : ZMod 3))).det ≠ 0) :
    (A.map (fun z => (z : ℝ))).det ≠ 0 := by
  rw [← Int.cast_det] at h3 ⊢
  have hZ : A.det ≠ 0 := by
    intro hz
    exact h3 (by rw [hz, Int.cast_zero])
  exact_mod_cast hZ

/-- A spanning integer family modulo three has a selected square subfamily
whose determinant is nonzero over the reals. This retains actual training vectors. -/
theorem integer_family_nonsingular_selection {δ τ : Type*} [Fintype δ] [DecidableEq δ]
    (v : τ → δ → ℤ)
    (hspan : Submodule.span (ZMod 3) (Set.range (fun t i => (v t i : ZMod 3))) = ⊤) :
    ∃ select : δ → τ,
      (Matrix.of (fun i j => (v (select i) j : ℝ))).det ≠ 0 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨s, hs, hsp, hli⟩ := exists_linearIndependent (ZMod 3)
    (Set.range (fun t i => (v t i : ZMod 3)))
  let b : Module.Basis s (ZMod 3) (δ → ZMod 3) := Module.Basis.mk hli (by
    rw [Subtype.range_coe_subtype]
    simpa [hspan] using hsp.ge)
  have hcard : Fintype.card δ = Fintype.card s := by
    simpa using Module.finrank_eq_card_basis b
  let e : δ ≃ s := Fintype.equivOfCardEq hcard
  have hex (i : δ) : ∃ t, (fun j => (v t j : ZMod 3)) = (e i).val := hs (e i).property
  choose select hselect using hex
  let A : Matrix δ δ ℤ := fun i j => v (select i) j
  have hlin : LinearIndependent (ZMod 3) (A.map (fun z => (z : ZMod 3))).row := by
    have heq : (A.map (fun z => (z : ZMod 3))).row = fun i => (e i).val := by
      funext i
      exact hselect i
    rw [heq]
    exact hli.comp e e.injective
  have hdet : (A.map (fun z => (z : ZMod 3))).det ≠ 0 :=
    Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.Nonsingular.of_linearIndependent_row hlin)
  exact ⟨select, integer_det_real_ne_zero_of_mod_three A hdet⟩


theorem integer_family_real_spanning_selection {δ τ : Type*} [Fintype δ] [DecidableEq δ]
    (v : τ → δ → ℤ)
    (hspan : Submodule.span (ZMod 3) (Set.range (fun t i => (v t i : ZMod 3))) = ⊤) :
    ∃ select : δ → τ,
      Submodule.span ℝ (Set.range (fun i j => (v (select i) j : ℝ))) = ⊤ := by
  obtain ⟨select, hdet⟩ := integer_family_nonsingular_selection v hspan
  have hli := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  refine ⟨select, ?_⟩
  have hb := (basisOfPiSpaceOfLinearIndependent hli).span_eq
  rw [coe_basisOfPiSpaceOfLinearIndependent] at hb
  exact hb

theorem linearEquiv_spanning_iff {R V W τ : Type*} [CommRing R]
    [AddCommGroup V] [AddCommGroup W] [Module R V] [Module R W]
    (e : V ≃ₗ[R] W) (v : τ → V) :
    Submodule.span R (Set.range (fun t => e (v t))) = ⊤ ↔
      Submodule.span R (Set.range v) = ⊤ := by
  rw [← Submodule.map_eq_top_iff (e := e), Submodule.map_span, ← Set.range_comp]
  rfl

def castSymmetric (R : Type*) [CommRing R] {ι : Type*} (H : SymmetricSpace ℤ ι) :
    SymmetricSpace R ι := ⟨H.val.map (fun z => (z : R)), H.property.map _⟩

theorem castSymmetric_coordinates {R ι : Type*} [CommRing R]
    (H : SymmetricSpace ℤ ι) (e : Sym2 ι) :
    symmetricCoordinateEquiv R ι (castSymmetric R H) e =
      (symmetricCoordinateEquiv ℤ ι H e : R) := by
  induction e using Sym2.inductionOn with
  | _ i j => rfl

/-- Integer symmetric training matrices that span modulo three contain exactly
d_s selected real spanning matrices. The selection is from the original list. -/
theorem integer_symmetric_spanning_selection {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    (G : τ → SymmetricSpace ℤ ι)
    (hspan : Submodule.span (ZMod 3) (Set.range (fun t => castSymmetric (ZMod 3) (G t))) = ⊤) :
    ∃ select : Sym2 ι → τ,
      Submodule.span ℝ (Set.range (fun i => castSymmetric ℝ (G (select i)))) = ⊤ := by
  have h3 := (linearEquiv_spanning_iff (symmetricCoordinateEquiv (ZMod 3) ι)
    (fun t => castSymmetric (ZMod 3) (G t))).mpr hspan
  have hcoords (t : τ) : symmetricCoordinateEquiv (ZMod 3) ι (castSymmetric (ZMod 3) (G t)) =
      fun e => (symmetricCoordinateEquiv ℤ ι (G t) e : ZMod 3) := by
    funext e
    exact castSymmetric_coordinates (G t) e
  simp only [hcoords] at h3
  obtain ⟨select, hs⟩ := integer_family_real_spanning_selection
    (fun t => symmetricCoordinateEquiv ℤ ι (G t)) h3
  refine ⟨select, (linearEquiv_spanning_iff (symmetricCoordinateEquiv ℝ ι) _).mp ?_⟩
  have hcoordsR (t : τ) : symmetricCoordinateEquiv ℝ ι (castSymmetric ℝ (G t)) =
      fun e => (symmetricCoordinateEquiv ℤ ι (G t) e : ℝ) := by
    funext e
    exact castSymmetric_coordinates (G t) e
  simpa only [hcoordsR] using hs

end AdaptiveOrthogonalRigidity
