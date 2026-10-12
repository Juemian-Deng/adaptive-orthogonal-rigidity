import AdaptiveOrthogonalRigidity.PolynomialSeedUnion

open MeasureTheory Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The random-seed part of a Krylov relation, with bulk and seed entries
living in disjoint original-coordinate summands. The mark is prescribed. -/
theorem graph_seed_polynomial_bound {κ : Type*} [Fintype κ] [DecidableEq κ]
    (n d t : ℕ) (diag : Fin n → ZMod 3) (v : Fin n → ZMod 3)
    {α : ℝ} (hα : 0 ≤ α) (hαhalf : α ≤ 1 / 2)
    (p : ((Fin n × κ) ⊕ Edge n) → unitInterval)
    (hp : ∀ e, α ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - α) :
    (cubeMeasure p).real {X | (fun ij => X (Sum.inl ij)) ∈ seedPolynomialFailure d
      (fieldGraphMatrix (ZMod 3) n diag (fun e => X (Sum.inr e))) v} ≤
      (rootCount d : ℝ) * (2 : ℝ) ^ n * (beta α) ^ (((t : ℝ) ^ 2 - 1) / 4) +
        (3 : ℝ) ^ ((d + 1) * (Fintype.card κ + 1)) * (beta α) ^ ((n : ℝ) - d * t) := by
  let E : Set (((Fin n × κ) ⊕ Edge n) → Bool) :=
    {X | (fun ij => X (Sum.inl ij)) ∈ seedPolynomialFailure d
      (fieldGraphMatrix (ZMod 3) n diag (fun e => X (Sum.inr e))) v}
  let C : ℝ := (3 : ℝ) ^ ((d + 1) * (Fintype.card κ + 1)) * (beta α) ^ ((n : ℝ) - d * t)
  have hC : 0 ≤ C := mul_nonneg (pow_nonneg (by norm_num) _)
    (Real.rpow_nonneg (by dsimp [beta]; linarith) _)
  have hsplit := cube_event_le_bad_plus_good p (Equiv.refl _) E
    (polynomialKernelFailure n d t diag) C hC (by
      intro r hr
      have hgood (q : Polynomial (ZMod 3)) (hq : q ≠ 0) (hd : q.natDegree ≤ d) :
          Module.finrank (ZMod 3) (Polynomial.aeval (fieldGraphMatrix (ZMod 3) n diag r) q).mulVecLin.ker ≤ d * t := by
        by_contra h
        exact hr ⟨q, hq, hd, lt_of_not_ge h⟩
      have h := polynomial_seed_union_bound d (d * t) (fieldGraphMatrix (ZMod 3) n diag r) v hgood
        hα hαhalf (fun ij => p (Sum.inl ij)) (fun ij => hp (Sum.inl ij))
      change (cubeMeasure (fun ij => p (Sum.inl ij))).real
        (seedPolynomialFailure d (fieldGraphMatrix (ZMod 3) n diag r) v) ≤ C
      simpa only [C, Fintype.card_fin, Nat.cast_mul] using h)
  exact hsplit.trans (add_le_add
    (polynomial_kernel_bound n d t diag hα hαhalf (fun e => p (Sum.inr e)) (fun e => hp (Sum.inr e)))
    (le_refl C))

end AdaptiveOrthogonalRigidity
