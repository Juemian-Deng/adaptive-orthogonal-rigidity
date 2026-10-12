import AdaptiveOrthogonalRigidity.CoordinatePivots
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace AdaptiveOrthogonalRigidity

/-- The elementary kernel-product inequality avoids a primary-decomposition
assumption when bounding polynomial kernels over a splitting field. -/
theorem kernel_comp_finrank_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A B : Module.End K V) :
    Module.finrank K (LinearMap.ker (A.comp B)) ≤
      Module.finrank K A.ker + Module.finrank K B.ker := by
  let F : (LinearMap.ker (A.comp B)) →ₗ[K] A.ker := {
    toFun x := ⟨B x.val, x.property⟩
    map_add' _ _ := Subtype.ext (map_add B _ _)
    map_smul' _ _ := Subtype.ext (map_smul B _ _) }
  let G : F.ker →ₗ[K] B.ker := {
    toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hG : Function.Injective G := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : B.ker => z.val) h
  have hk := LinearMap.finrank_le_finrank_of_injective hG
  have hr : Module.finrank K F.range ≤ Module.finrank K A.ker := Submodule.finrank_le _
  have hd := F.finrank_range_add_finrank_ker
  omega

theorem kernel_pow_finrank_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A : Module.End K V) (k : ℕ) :
    Module.finrank K (LinearMap.ker (A ^ k)) ≤ k * Module.finrank K A.ker := by
  induction k with
  | zero =>
    simp [Module.End.one_eq_id]
  | succ k hk =>
    rw [pow_succ]
    have h := kernel_comp_finrank_le (A ^ k) A
    change Module.finrank K (LinearMap.ker (A ^ k * A)) ≤ _ at h
    exact h.trans (by nlinarith)

theorem kernel_list_prod_finrank_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (L : List (Module.End K V)) (t : ℕ)
    (hL : ∀ A ∈ L, Module.finrank K A.ker ≤ t) :
    Module.finrank K (LinearMap.ker L.prod) ≤ L.length * t := by
  induction L with
  | nil =>
    simp only [List.prod_nil, List.length_nil, Nat.zero_mul, Module.End.one_eq_id,
      LinearMap.ker_id]
    exact le_of_eq (finrank_bot K V : Module.finrank K (⊥ : Submodule K V) = 0)
  | cons A L ih =>
    have hA := hL A (by simp)
    have htail := ih (fun B hB => hL B (by simp [hB]))
    have h := kernel_comp_finrank_le A L.prod
    change Module.finrank K (LinearMap.ker (A * L.prod)) ≤ _ at h
    simp only [List.prod_cons, List.length_cons]
    exact h.trans (by nlinarith)

end AdaptiveOrthogonalRigidity
