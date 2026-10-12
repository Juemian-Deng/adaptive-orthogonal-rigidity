import AdaptiveOrthogonalRigidity.IntegerLift
import AdaptiveOrthogonalRigidity.KrylovColumns

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Rectangular column independence modulo three lifts to real independence
through a genuine nonzero integer square minor, not through a nonexistent F3→R map. -/
theorem integer_columns_real_independent {ι τ : Type*} [Fintype ι] [Fintype τ]
    [DecidableEq ι] [DecidableEq τ] (M : Matrix ι τ ℤ)
    (h3 : LinearIndependent (ZMod 3) (M.map (fun z => (z : ZMod 3))).col) :
    LinearIndependent ℝ (M.map (fun z => (z : ℝ))).col := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have ht : LinearIndependent (ZMod 3) (M.map (fun z => (z : ZMod 3))).transpose.row := by
    simpa only [Matrix.row_transpose] using h3
  have hr := ht.rank_matrix
  rw [Matrix.rank_transpose, Matrix.rank_eq_finrank_span_row] at hr
  have hs : Submodule.span (ZMod 3) (Set.range (fun i j => (M i j : ZMod 3))) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_pi]
    exact hr
  obtain ⟨select, hdet⟩ := integer_family_nonsingular_selection (fun i j => M i j) hs
  apply LinearIndependent.of_comp (LinearMap.funLeft ℝ ℝ select)
  exact Matrix.linearIndependent_cols_of_det_ne_zero hdet

def integerKrylovMatrix {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℕ) (M : Matrix ι ι ℤ) (V : τ → ι → ℤ) : Matrix ι (Fin (d + 1) × τ) ℤ :=
  fun i j => ((M ^ j.1.val).mulVec (V j.2)) i

theorem integerKrylovMatrix_cast {K ι τ : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d : ℕ) (M : Matrix ι ι ℤ) (V : τ → ι → ℤ) :
    ((integerKrylovMatrix d M V).map (Int.castRingHom K)).col =
      krylovColumns d (M.map (Int.castRingHom K)) (fun j i => (V j i : K)) := by
  funext j i
  change (((M ^ j.1.val).mulVec (V j.2)) i : K) = _
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, krylovColumns]
  have hp : (M ^ j.1.val).map (Int.castRingHom K) = (M.map (Int.castRingHom K)) ^ j.1.val :=
    (Int.castRingHom K).mapMatrix.map_pow M j.1.val
  exact Finset.sum_congr rfl (fun k _ => by rw [← hp]; rfl)

/-- The complete original integer Krylov matrix maps to both the F3 and real
power-column matrices, so mod-three full column rank implies real full column rank. -/
theorem integer_krylov_real_independent {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ] (d : ℕ) (M : Matrix ι ι ℤ) (V : τ → ι → ℤ)
    (h3 : LinearIndependent (ZMod 3) (krylovColumns d (M.map (Int.castRingHom (ZMod 3)))
      (fun j i => (V j i : ZMod 3)))) :
    LinearIndependent ℝ (krylovColumns d (M.map (Int.castRingHom ℝ)) (fun j i => (V j i : ℝ))) := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [← integerKrylovMatrix_cast] at h3 ⊢
  exact integer_columns_real_independent (integerKrylovMatrix d M V) h3

end AdaptiveOrthogonalRigidity
