import AdaptiveOrthogonalRigidity.ConditionalProduct
import AdaptiveOrthogonalRigidity.BorderMatrix

open scoped Classical

namespace AdaptiveOrthogonalRigidity

def edgeCastSucc {n : ℕ} (e : Edge n) : Edge (n + 1) :=
  ⟨(e.val.1.castSucc, e.val.2.castSucc), e.property⟩

def edgeToLast {n : ℕ} (i : Fin n) : Edge (n + 1) :=
  ⟨(i.castSucc, Fin.last n), i.isLt⟩

def edgeSuccSum (n : ℕ) : Fin n ⊕ Edge n → Edge (n + 1) :=
  Sum.elim edgeToLast edgeCastSucc

theorem edgeSuccSum_bijective (n : ℕ) : Function.Bijective (edgeSuccSum n) := by
  constructor
  · intro a b h
    have h1 := congrArg (fun e : Edge (n + 1) => e.val.1.val) h
    have h2 := congrArg (fun e : Edge (n + 1) => e.val.2.val) h
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (Fin.ext h1)
      | inr e =>
        change n = e.val.2.val at h2
        exact False.elim (by have := e.val.2.isLt; omega)
    | inr e =>
      cases b with
      | inl j =>
        change e.val.2.val = n at h2
        exact False.elim (by have := e.val.2.isLt; omega)
      | inr f =>
        apply congrArg Sum.inr
        apply Subtype.ext
        exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  · intro e
    by_cases hj : e.val.2.val = n
    · let i : Fin n := ⟨e.val.1.val, by have := e.property; change e.val.1.val < e.val.2.val at this; omega⟩
      refine ⟨Sum.inl i, Subtype.ext ?_⟩
      exact Prod.ext (Fin.ext rfl) (Fin.ext hj.symm)
    · have hjlt : e.val.2.val < n := by have := e.val.2.isLt; omega
      let e' : Edge n := ⟨(⟨e.val.1.val, lt_trans e.property hjlt⟩, ⟨e.val.2.val, hjlt⟩), e.property⟩
      refine ⟨Sum.inr e', Subtype.ext ?_⟩
      exact Prod.ext (Fin.ext rfl) (Fin.ext rfl)

noncomputable def edgeSuccEquiv (n : ℕ) : Fin n ⊕ Edge n ≃ Edge (n + 1) :=
  Equiv.ofBijective (edgeSuccSum n) (edgeSuccSum_bijective n)

def graphDropLast {n : ℕ} (ω : GraphSample (n + 1)) : GraphSample n := fun e => ω (edgeCastSucc e)
def graphLastStar {n : ℕ} (ω : GraphSample (n + 1)) : Fin n → Bool := fun i => ω (edgeToLast i)

theorem graphDropLast_split {n : ℕ} (x : Fin n → Bool) (ω : GraphSample n) :
    graphDropLast (splitAssignmentEquiv (edgeSuccEquiv n) (x, ω)) = ω := by
  funext e
  change Sum.elim x ω ((edgeSuccEquiv n).symm ((edgeSuccEquiv n) (Sum.inr e))) = ω e
  rw [Equiv.symm_apply_apply]
  rfl

theorem graphLastStar_split {n : ℕ} (x : Fin n → Bool) (ω : GraphSample n) :
    graphLastStar (splitAssignmentEquiv (edgeSuccEquiv n) (x, ω)) = x := by
  funext i
  change Sum.elim x ω ((edgeSuccEquiv n).symm ((edgeSuccEquiv n) (Sum.inl i))) = x i
  rw [Equiv.symm_apply_apply]
  rfl

end AdaptiveOrthogonalRigidity
