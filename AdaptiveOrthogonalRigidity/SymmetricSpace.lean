import AdaptiveOrthogonalRigidity.F3QuadraticAtom
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas

open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

def symmetricSubspace (R ι : Type*) [CommRing R] : Submodule R (Matrix ι ι R) where
  carrier := {H | H.IsSymm}
  zero_mem' := Matrix.isSymm_zero
  add_mem' := by
    intro H G hH hG
    exact (Matrix.transpose_add H G).trans (congrArg₂ (· + ·) hH hG)
  smul_mem' := by
    intro c H hH
    exact (Matrix.transpose_smul c H).trans (congrArg (c • ·) hH)

abbrev SymmetricSpace (R ι : Type*) [CommRing R] := symmetricSubspace R ι

def symmetricCoordinateEquiv (R ι : Type*) [CommRing R] :
    SymmetricSpace R ι ≃ₗ[R] (Sym2 ι → R) where
  toFun H := Sym2.lift ⟨H.val, fun i j => (H.property.apply i j).symm⟩
  invFun f := ⟨fun i j => f (Sym2.mk i j), by
    apply Matrix.IsSymm.ext
    intro i j
    exact congrArg f Sym2.eq_swap⟩
  left_inv H := by rfl
  right_inv f := by
    funext e
    induction e using Sym2.inductionOn with
    | _ i j => rfl
  map_add' H G := by
    funext e
    induction e using Sym2.inductionOn with
    | _ i j => rfl
  map_smul' c H := by
    funext e
    induction e using Sym2.inductionOn with
    | _ i j => rfl

theorem symmetric_space_card {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Fintype.card (SymmetricSpace (ZMod 3) ι) =
      3 ^ (Fintype.card ι * (Fintype.card ι + 1) / 2) := by
  rw [Fintype.card_congr (symmetricCoordinateEquiv (ZMod 3) ι).toEquiv,
    Fintype.card_fun, Sym2.card, Nat.choose_two_right]
  simp [ZMod.card, Nat.mul_comm]

theorem symmetric_space_finrank {R ι : Type*} [Field R] [Fintype ι] [DecidableEq ι] :
    Module.finrank R (SymmetricSpace R ι) = Fintype.card ι * (Fintype.card ι + 1) / 2 := by
  rw [(symmetricCoordinateEquiv R ι).finrank_eq, Module.finrank_pi, Sym2.card, Nat.choose_two_right]
  simp [Nat.mul_comm]

/-- The trace pairing restricted to symmetric matrices. -/
def symmetricTracePair (R ι : Type*) [CommRing R] [Fintype ι] :
    SymmetricSpace R ι →ₗ[R] Module.Dual R (SymmetricSpace R ι) where
  toFun H :=
    { toFun := fun G => (H.val * G.val).trace
      map_add' := by intro G K; simp [Matrix.mul_add, Matrix.trace_add]
      map_smul' := by intro c G; simp [Matrix.trace_smul] }
  map_add' := by
    intro H G
    ext K
    simp [Matrix.add_mul, Matrix.trace_add]
  map_smul' := by
    intro c H
    ext G
    simp [Matrix.trace_smul]

/-- In characteristic different from two, the trace pairing on symmetric
matrices is nondegenerate, including on off-diagonal coordinates. -/
theorem symmetric_trace_nondegenerate {R ι : Type*} [Field R] [Fintype ι]
    [DecidableEq ι] (htwo : (2 : R) ≠ 0) (H : SymmetricSpace R ι)
    (hzero : ∀ G : SymmetricSpace R ι, (H.val * G.val).trace = 0) : H = 0 := by
  apply Subtype.ext
  ext i j
  let G : SymmetricSpace R ι := ⟨Matrix.single i j 1 + Matrix.single j i 1, by
    simp [symmetricSubspace, Matrix.IsSymm, Matrix.transpose_add, Matrix.transpose_single, add_comm]⟩
  have h := hzero G
  have hs := H.property.apply i j
  have hz : (2 : R) * H.val i j = 0 := by
    simpa [G, Matrix.mul_add, Matrix.trace_add, Matrix.trace_mul_single,
      hs, two_mul] using h
  exact (mul_eq_zero.mp hz).resolve_left htwo

theorem symmetricTracePair_injective {R ι : Type*} [Field R] [Fintype ι]
    [DecidableEq ι] (htwo : (2 : R) ≠ 0) :
    Function.Injective (symmetricTracePair R ι) := by
  intro H G heq
  apply sub_eq_zero.mp
  apply symmetric_trace_nondegenerate htwo
  intro K
  have hp : symmetricTracePair R ι (H - G) = 0 := by rw [map_sub, heq, sub_self]
  exact congrArg (fun f : Module.Dual R (SymmetricSpace R ι) => f K) hp

theorem symmetricTracePair_surjective {R ι : Type*} [Field R] [Fintype ι]
    [DecidableEq ι] (htwo : (2 : R) ≠ 0) :
    Function.Surjective (symmetricTracePair R ι) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    (symmetricTracePair_injective htwo)
  exact Subspace.dual_finrank_eq.symm

/-- Failure to span has a nonzero symmetric trace-annihilator. There are
exactly 3^d possible coefficient matrices over F3, counted above. -/
theorem exists_symmetric_trace_annihilator {R ι τ : Type*} [Field R] [Fintype ι]
    [DecidableEq ι] (htwo : (2 : R) ≠ 0) (G : τ → SymmetricSpace R ι)
    (hspan : Submodule.span R (Set.range G) ≠ ⊤) :
    ∃ H : SymmetricSpace R ι, H ≠ 0 ∧ ∀ t, (H.val * (G t).val).trace = 0 := by
  obtain ⟨f, hf, hker⟩ := Submodule.exists_le_ker_of_lt_top
    (Submodule.span R (Set.range G)) (lt_top_iff_ne_top.mpr hspan)
  obtain ⟨H, hH⟩ := symmetricTracePair_surjective htwo f
  refine ⟨H, ?_, ?_⟩
  · intro h0
    apply hf
    rw [← hH, h0, map_zero]
  · intro t
    have hmem := hker (Submodule.subset_span (Set.mem_range_self t))
    have hz : f (G t) = 0 := hmem
    rw [← hH] at hz
    exact hz

end AdaptiveOrthogonalRigidity
