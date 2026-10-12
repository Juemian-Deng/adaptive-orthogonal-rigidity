import AdaptiveOrthogonalRigidity.KernelDimensions
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.LinearAlgebra.Eigenspace.Basic

open scoped BigOperators

namespace AdaptiveOrthogonalRigidity

/-- A splitting polynomial is bounded by the sum of the nullities of its
linear factors. The scalar leading coefficient creates no extra kernel. -/
theorem split_polynomial_kernel_bound {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (p : Polynomial K) (hp : p ≠ 0)
    (hsplit : p.Splits) (t : ℕ)
    (hroot : ∀ a ∈ p.roots, Module.finrank K (LinearMap.ker (T - a • 1)) ≤ t) :
    Module.finrank K (LinearMap.ker (Polynomial.aeval T p)) ≤ p.natDegree * t := by
  classical
  let L := p.roots.toList.map (fun a => Polynomial.X - Polynomial.C a)
  have hprod : L.prod = (p.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod := by
    dsimp [L]
    rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
  have hpform : p = Polynomial.C p.leadingCoeff * L.prod := hsplit.eq_prod_roots.trans (by rw [hprod])
  have heval : Polynomial.aeval T p = p.leadingCoeff •
      (p.roots.toList.map (fun a => T - a • 1)).prod := by
    conv_lhs => rw [hpform]
    rw [map_mul, Polynomial.aeval_C, map_list_prod]
    simp only [L, List.map_map, Function.comp_def, map_sub, Polynomial.aeval_X,
      Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rw [heval, LinearMap.ker_smul _ _ (Polynomial.leadingCoeff_ne_zero.mpr hp)]
  have h := kernel_list_prod_finrank_le (p.roots.toList.map (fun a => T - a • 1)) t (by
    intro A hA
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
    exact hroot a (by simpa using ha))
  simpa only [List.length_map, Multiset.length_toList, ← hsplit.natDegree_eq_card_roots] using h

end AdaptiveOrthogonalRigidity
