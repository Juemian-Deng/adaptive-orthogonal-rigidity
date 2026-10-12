import AdaptiveOrthogonalRigidity.AffineFibers
import AdaptiveOrthogonalRigidity.KernelDimensions
import Mathlib.LinearAlgebra.Matrix.Dual

open Matrix MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Algebraic annihilator duality for the coordinate dot product, valid over
all fields, including finite extensions of F3. -/
theorem mem_transpose_range_iff_dot_kernel {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (x : ι → K) :
    x ∈ A.transpose.mulVecLin.range ↔ ∀ v, A.mulVec v = 0 → x ⬝ᵥ v = 0 := by
  constructor
  · rintro ⟨u, rfl⟩ v hv
    change A.transpose.mulVec u ⬝ᵥ v = 0
    rw [dotProduct_comm, dotProduct_transpose_mulVec, hv, dotProduct_zero]
  · intro h
    have hd : dotProductEquiv K ι x ∈ A.mulVecLin.ker.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro v hv
      exact h v hv
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hd
    obtain ⟨φ, hφ⟩ := hd
    let u := (dotProductEquiv K ι).symm φ
    refine ⟨u, ?_⟩
    apply (dotProductEquiv K ι).injective
    apply LinearMap.ext
    intro v
    have hfun := congrArg (fun ψ : Module.Dual K (ι → K) => ψ v) hφ
    have hu : φ = dotProductEquiv K ι u := (dotProductEquiv K ι).apply_symm_apply φ |>.symm
    rw [hu] at hfun
    change u ⬝ᵥ A.mulVec v = x ⬝ᵥ v at hfun
    change A.transpose.mulVec u ⬝ᵥ v = x ⬝ᵥ v
    rw [dotProduct_comm, dotProduct_transpose_mulVec]
    exact hfun

theorem symmetric_exists_kernel_pairing {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (hA : A.IsSymm) (x : ι → K)
    (hx : x ∉ A.mulVecLin.range) :
    ∃ v, A.mulVec v = 0 ∧ x ⬝ᵥ v ≠ 0 := by
  by_contra! h
  apply hx
  rw [← hA]
  exact (mem_transpose_range_iff_dot_kernel A x).mpr h

/-- The bordering operator in product coordinates, with arbitrary fixed diagonal. -/
def symmetricBorderMap {K ι : Type*} [Field K] [Fintype ι]
    (A : Matrix ι ι K) (x : ι → K) (a : K) : Module.End K ((ι → K) × K) where
  toFun v := (A.mulVec v.1 + v.2 • x, x ⬝ᵥ v.1 + a * v.2)
  map_add' v w := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.snd_add, Matrix.mulVec_add, add_smul]
      abel
    · simp only [Prod.fst_add, Prod.snd_add, dotProduct_add, mul_add]
      ring
  map_smul' c v := by
    apply Prod.ext
    · simp only [Prod.smul_fst, Prod.smul_snd, Matrix.mulVec_smul, smul_add, smul_smul, smul_eq_mul, RingHom.id_apply]
    · simp only [Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_eq_mul, RingHom.id_apply]
      ring

theorem symmetricBorderMap_kernel_iff {K ι : Type*} [Field K] [Fintype ι]
    (A : Matrix ι ι K) (x : ι → K) (a : K) (hx : x ∉ A.mulVecLin.range)
    (v : (ι → K) × K) :
    v ∈ (symmetricBorderMap A x a).ker ↔
      A.mulVec v.1 = 0 ∧ v.2 = 0 ∧ x ⬝ᵥ v.1 = 0 := by
  constructor
  · intro hv
    have h1 : A.mulVec v.1 + v.2 • x = 0 := congrArg Prod.fst hv
    have h2 : x ⬝ᵥ v.1 + a * v.2 = 0 := congrArg Prod.snd hv
    have ht : v.2 = 0 := by
      by_contra ht
      apply hx
      refine ⟨(-v.2⁻¹) • v.1, ?_⟩
      change A.mulVec ((-v.2⁻¹) • v.1) = x
      rw [Matrix.mulVec_smul, eq_neg_of_add_eq_zero_left h1]
      simp [smul_smul, ht]
    refine ⟨?_, ht, ?_⟩
    · simpa only [ht, zero_smul, add_zero] using h1
    · simpa only [ht, mul_zero, add_zero] using h2
  · rintro ⟨h1, ht, h2⟩
    change (A.mulVec v.1 + v.2 • x, x ⬝ᵥ v.1 + a * v.2) = (0, 0)
    simp [h1, ht, h2]

/-- A fresh border outside the old column space decreases corank by one,
equivalently increases rank by two. No assumption on its diagonal is used. -/
theorem symmetric_border_kernel_drop {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (hA : A.IsSymm)
    (x : ι → K) (a : K) (hx : x ∉ A.mulVecLin.range) :
    Module.finrank K (symmetricBorderMap A x a).ker + 1 = Module.finrank K A.mulVecLin.ker := by
  let F : Module.Dual K A.mulVecLin.ker := (dotProductEquiv K ι x).comp A.mulVecLin.ker.subtype
  have hF : F ≠ 0 := by
    obtain ⟨v, hv, hxv⟩ := symmetric_exists_kernel_pairing A hA x hx
    intro hz
    have h := congrArg (fun f : Module.Dual K A.mulVecLin.ker => f ⟨v, hv⟩) hz
    exact hxv h
  let e : (symmetricBorderMap A x a).ker ≃ₗ[K] F.ker := {
    toFun v := ⟨⟨v.val.1, ((symmetricBorderMap_kernel_iff A x a hx v.val).mp v.property).1⟩,
      ((symmetricBorderMap_kernel_iff A x a hx v.val).mp v.property).2.2⟩
    invFun v := ⟨(v.val.val, 0), (symmetricBorderMap_kernel_iff A x a hx _).mpr
      ⟨v.val.property, rfl, v.property⟩⟩
    left_inv v := by
      apply Subtype.ext
      change (v.val.1, 0) = v.val
      apply Prod.ext
      · rfl
      · exact ((symmetricBorderMap_kernel_iff A x a hx v.val).mp v.property).2.1.symm
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  rw [e.finrank_eq]
  exact Module.Dual.finrank_ker_add_one_of_ne_zero hF

/-- At an arbitrary bordering step, corank can increase by at most one. -/
theorem symmetric_border_kernel_growth {K ι : Type*} [Field K]
    [Fintype ι] (A : Matrix ι ι K) (x : ι → K) (a : K) :
    Module.finrank K (symmetricBorderMap A x a).ker ≤ Module.finrank K A.mulVecLin.ker + 1 := by
  let B := symmetricBorderMap A x a
  let P := LinearMap.fst K (ι → K) K
  have hsub : A.mulVecLin.range ≤ (P.comp B).range := by
    rintro y ⟨v, rfl⟩
    refine ⟨(v, 0), ?_⟩
    simp [P, B, symmetricBorderMap]
  have h1 := Submodule.finrank_mono hsub
  have h2 := Submodule.finrank_map_le P B.range
  rw [← LinearMap.range_comp] at h2
  have hA := A.mulVecLin.finrank_range_add_finrank_ker
  have hB := B.finrank_range_add_finrank_ker
  rw [Module.finrank_prod, Module.finrank_self] at hB
  change Module.finrank K B.ker ≤ _
  omega

/-- Conditional failure to decrease corank costs beta to the old corank;
the fresh vector consists of original independent Bernoulli coordinates. -/
theorem symmetric_border_nondecrease_probability {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (hA : A.IsSymm) (a : K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : ι → unitInterval) (hp : ∀ i, α ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ 1 - α) :
    (cubeMeasure p).real {x | Module.finrank K A.mulVecLin.ker ≤
      Module.finrank K (symmetricBorderMap A (boolVector x) a).ker} ≤
      (1 - α) ^ Module.finrank K A.mulVecLin.ker := by
  have hsub : {x : ι → Bool | Module.finrank K A.mulVecLin.ker ≤
      Module.finrank K (symmetricBorderMap A (boolVector x) a).ker} ⊆
      {x | boolVector x - (0 : ι → K) ∈ A.mulVecLin.range} := by
    intro x hx
    change Module.finrank K A.mulVecLin.ker ≤
      Module.finrank K (symmetricBorderMap A (boolVector x) a).ker at hx
    by_contra hnot
    have hnot' : boolVector x ∉ A.mulVecLin.range := by simpa using hnot
    have h := symmetric_border_kernel_drop A hA (boolVector x) a hnot'
    omega
  have h := affine_subspace_bound hα hα1 p hp A.mulVecLin.range (0 : ι → K)
  have hd := A.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at hd
  have heq : Fintype.card ι - Module.finrank K A.mulVecLin.range = Module.finrank K A.mulVecLin.ker := by omega
  rw [heq] at h
  exact (measureReal_mono hsub).trans h

end AdaptiveOrthogonalRigidity
