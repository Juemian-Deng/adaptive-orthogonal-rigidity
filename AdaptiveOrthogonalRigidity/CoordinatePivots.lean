import AdaptiveOrthogonalRigidity.IntegerLift
import Mathlib.LinearAlgebra.Quotient.Basic

open scoped BigOperators Classical

noncomputable section

namespace AdaptiveOrthogonalRigidity

/-- Select actual coordinate columns, over an arbitrary field, rather than
assuming a pivot set or changing the Bernoulli coordinates. -/
theorem spanning_family_pivots {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι] (v : ι → V)
    (hspan : Submodule.span K (Set.range v) = ⊤) :
    ∃ f : Fin (Module.finrank K V) ↪ ι, LinearIndependent K (fun j => v (f j)) := by
  obtain ⟨s, hs, hsp, hli⟩ := exists_linearIndependent K (Set.range v)
  have hfinite : s.Finite := (Set.finite_range v).subset hs
  let := hfinite.fintype
  let b : Module.Basis s K V := Module.Basis.mk hli (by
    rw [Subtype.range_coe_subtype]
    simpa [hspan] using hsp.ge)
  have hcard : Fintype.card (Fin (Module.finrank K V)) = Fintype.card s := by
    simpa using Module.finrank_eq_card_basis b
  let e : Fin (Module.finrank K V) ≃ s := Fintype.equivOfCardEq hcard
  have hex (j : s) : ∃ i, v i = j.val := hs j.property
  choose select hselect using hex
  have hinj : Function.Injective select := by
    intro i j h
    apply Subtype.ext
    rw [← hselect i, ← hselect j, h]
  let f : Fin (Module.finrank K V) ↪ ι := e.toEmbedding.trans ⟨select, hinj⟩
  refine ⟨f, ?_⟩
  have heq : (fun j => v (f j)) = fun j => (e j).val := funext (fun j => hselect (e j))
  rw [heq]
  exact hli.comp e e.injective

/-- A linear system has exactly rank-many independent actual coordinate
columns, also over extension fields. -/
theorem linearMap_coordinate_pivots {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (L : (ι → K) →ₗ[K] V) :
    ∃ f : Fin (Module.finrank K L.range) ↪ ι,
      LinearIndependent K (fun j => L (Pi.single (f j) 1)) := by
  have hsurj : Function.Surjective L.rangeRestrict := by
    rintro ⟨y, x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  have hspan : Submodule.span K (Set.range (fun i => L.rangeRestrict (Pi.single i 1))) = ⊤ := by
    have hb := (Pi.basisFun K ι).span_eq
    have hm := congrArg (Submodule.map L.rangeRestrict) hb
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
      LinearMap.range_eq_top.mpr hsurj] at hm
    simpa only [Function.comp_def, Pi.basisFun_apply] using hm
  obtain ⟨f, hf⟩ := spanning_family_pivots (fun i => L.rangeRestrict (Pi.single i 1)) hspan
  refine ⟨f, Fintype.linearIndependent_iff.mpr ?_⟩
  intro g hg i
  apply Fintype.linearIndependent_iff.mp hf g _ i
  apply Subtype.ext
  simpa using hg

end AdaptiveOrthogonalRigidity
