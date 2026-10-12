import AdaptiveOrthogonalRigidity.OrthogonalAlgebra
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace AdaptiveOrthogonalRigidity

theorem row_norm_sq {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q) (i : Fin n) :
    ∑ j, Q i j ^ 2 = 1 := by
  have h := congr_fun (congr_fun hQ.2 i) i
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, pow_two] using h

theorem column_norm_sq {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q) (j : Fin n) :
    ∑ i, Q i j ^ 2 = 1 := by
  have h := congr_fun (congr_fun hQ.1 j) j
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, pow_two] using h

/-- Actual connected support components have equally many row and column vertices.
The argument uses the same rectangular sum of squared entries in both orders. -/
theorem support_component_balance {n : ℕ} (Q : RealMatrix n) (hQ : Orthogonal Q)
    (v : Fin n ⊕ Fin n) :
    Nat.card {i : Fin n // SupportReachable Q v (Sum.inl i)} =
      Nat.card {j : Fin n // SupportReachable Q v (Sum.inr j)} := by
  classical
  let I := Finset.univ.filter (fun i => SupportReachable Q v (Sum.inl i))
  let J := Finset.univ.filter (fun j => SupportReachable Q v (Sum.inr j))
  have hrow (i : Fin n) (hi : i ∈ I) : ∑ j ∈ J, Q i j ^ 2 = 1 := by
    calc
      ∑ j ∈ J, Q i j ^ 2 = ∑ j : Fin n, Q i j ^ 2 := by
        apply Finset.sum_subset (Finset.subset_univ J)
        intro j _ hj
        have hz : Q i j = 0 := by
          by_contra hn
          apply hj
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          exact Relation.ReflTransGen.tail (Finset.mem_filter.mp hi).2 hn
        simp [hz]
      _ = 1 := row_norm_sq Q hQ i
  have hcol (j : Fin n) (hj : j ∈ J) : ∑ i ∈ I, Q i j ^ 2 = 1 := by
    calc
      ∑ i ∈ I, Q i j ^ 2 = ∑ i : Fin n, Q i j ^ 2 := by
        apply Finset.sum_subset (Finset.subset_univ I)
        intro i _ hi
        have hz : Q i j = 0 := by
          by_contra hn
          apply hi
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          exact Relation.ReflTransGen.tail (Finset.mem_filter.mp hj).2 hn
        simp [hz]
      _ = 1 := column_norm_sq Q hQ j
  have hrows : (∑ i ∈ I, ∑ j ∈ J, Q i j ^ 2) = (I.card : ℝ) := by
    calc
      _ = ∑ _i ∈ I, (1 : ℝ) := Finset.sum_congr rfl (fun i hi => hrow i hi)
      _ = _ := by simp
  have hcols : (∑ j ∈ J, ∑ i ∈ I, Q i j ^ 2) = (J.card : ℝ) := by
    calc
      _ = ∑ _j ∈ J, (1 : ℝ) := Finset.sum_congr rfl (fun j hj => hcol j hj)
      _ = _ := by simp
  have hreal : (I.card : ℝ) = (J.card : ℝ) :=
    hrows.symm.trans (Finset.sum_comm.trans hcols)
  have hnat : I.card = J.card := by exact_mod_cast hreal
  simpa [I, J, Nat.card_eq_fintype_card, Fintype.card_subtype] using hnat

end AdaptiveOrthogonalRigidity
