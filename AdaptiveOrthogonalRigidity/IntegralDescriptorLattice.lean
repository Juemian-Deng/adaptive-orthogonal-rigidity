import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Algebra.Rat
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Coordinatewise inclusion of the integer lattice into its rational space. -/
def descriptorIntegerCast (ι : Type*) : (ι → ℤ) →ₗ[ℤ] (ι → ℚ) where
  toFun := fun v i => (v i : ℚ)
  map_add' := by intro x y; funext i; simp
  map_smul' := by intro r x; funext i; simp

/-- The full saturated integer lattice of a rational subspace. -/
def descriptorIntegerLattice {ι : Type*} (H : Submodule ℚ (ι → ℚ)) :
    Submodule ℤ (ι → ℤ) :=
  (H.restrictScalars ℤ).comap (descriptorIntegerCast ι)

@[simp] theorem descriptorIntegerLattice_mem {ι : Type*}
    (H : Submodule ℚ (ι → ℚ)) (v : ι → ℤ) :
    v ∈ descriptorIntegerLattice H ↔ (fun i => (v i : ℚ)) ∈ H := Iff.rfl

/-- Saturation is proved directly, for every nonzero integer scalar. -/
theorem descriptorIntegerLattice_saturated {ι : Type*}
    (H : Submodule ℚ (ι → ℚ)) (a : ℤ) (ha : a ≠ 0) (v : ι → ℤ)
    (hv : a • v ∈ descriptorIntegerLattice H) : v ∈ descriptorIntegerLattice H := by
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  change (fun i => (v i : ℚ)) ∈ H
  have hh : (a : ℚ) • (fun i => (v i : ℚ)) ∈ H := by
    change (fun i => (a : ℚ) * (v i : ℚ)) ∈ H
    simpa only [descriptorIntegerLattice_mem, Pi.smul_apply, smul_eq_mul, Int.cast_mul] using hv
  have := H.smul_mem (a : ℚ)⁻¹ hh
  simpa only [smul_smul, inv_mul_cancel₀ haQ, one_smul] using this

/-- The quotient by the full integer lattice is torsion free. -/
theorem descriptorIntegerLattice_quotient_torsionFree {ι : Type*}
    (H : Submodule ℚ (ι → ℚ)) :
    Module.IsTorsionFree ℤ ((ι → ℤ) ⧸ descriptorIntegerLattice H) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro a x hx
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  induction x using Submodule.Quotient.induction_on with
  | _ v =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply descriptorIntegerLattice_saturated H a ha v
    exact (Submodule.Quotient.mk_eq_zero _).mp hx

/-- A saturated finite integer lattice has an integral linear retraction from
the ambient lattice. This replaces a cited Smith-normal-form assertion by a
checked free-quotient splitting. -/
theorem descriptorIntegerLattice_retraction {ι : Type*} [Fintype ι]
    (H : Submodule ℚ (ι → ℚ)) :
    ∃ P : (ι → ℤ) →ₗ[ℤ] descriptorIntegerLattice H,
      ∀ v : descriptorIntegerLattice H, P v.val = v := by
  let A := descriptorIntegerLattice H
  have : Module.IsTorsionFree ℤ ((ι → ℤ) ⧸ A) := descriptorIntegerLattice_quotient_torsionFree H
  have : Module.Free ℤ ((ι → ℤ) ⧸ A) := inferInstance
  obtain ⟨s, hs⟩ := A.mkQ.exists_rightInverse_of_surjective A.range_mkQ
  let p : Module.End ℤ (ι → ℤ) := LinearMap.id - s.comp A.mkQ
  have hp (v : ι → ℤ) : p v ∈ A := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change A.mkQ (v - s (A.mkQ v)) = 0
    rw [map_sub]
    have hh := LinearMap.congr_fun hs (A.mkQ v)
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using sub_eq_zero.mpr hh.symm
  refine ⟨p.codRestrict A hp, ?_⟩
  intro v
  apply Subtype.ext
  change v.val - s (A.mkQ v.val) = v.val
  rw [show A.mkQ v.val = 0 from (Submodule.Quotient.mk_eq_zero _).mpr v.property,
    map_zero, sub_zero]

noncomputable def descriptorLatticeBasisMatrix {ι σ : Type*} {H : Submodule ℚ (ι → ℚ)}
    (b : Module.Basis σ ℤ (descriptorIntegerLattice H)) : Matrix ι σ ℤ :=
  fun i j => (b j).val i

/-- Every integer basis matrix of a saturated rational lattice has an integer
left inverse, hence its reduction is independent at every prime. -/
theorem descriptor_lattice_basis_leftInverse {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (H : Submodule ℚ (ι → ℚ))
    (b : Module.Basis σ ℤ (descriptorIntegerLattice H)) :
    ∃ D : Matrix σ ι ℤ, D * descriptorLatticeBasisMatrix b = 1 := by
  obtain ⟨P, hP⟩ := descriptorIntegerLattice_retraction H
  let f : (ι → ℤ) →ₗ[ℤ] (σ → ℤ) := b.equivFun.toLinearMap.comp P
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.one_mulVec,
    LinearMap.toMatrix'_mulVec]
  change b.equivFun (P (b j).val) = Pi.single j 1
  rw [hP]
  funext i
  simpa only [Pi.single_apply, eq_comm] using b.equivFun_self j i

/-- Reduction of a saturated lattice basis is independent over every field,
in particular over F3; the proof maps its integral left inverse. -/
theorem descriptor_lattice_basis_reduction_independent {K ι σ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (H : Submodule ℚ (ι → ℚ)) (b : Module.Basis σ ℤ (descriptorIntegerLattice H)) :
    LinearIndependent K ((descriptorLatticeBasisMatrix b).map (Int.castRingHom K)).col := by
  obtain ⟨D, hD⟩ := descriptor_lattice_basis_leftInverse H b
  have hm : D.map (Int.castRingHom K) * (descriptorLatticeBasisMatrix b).map (Int.castRingHom K) = 1 := by
    have hh := congrArg (fun A => A.map (Int.castRingHom K)) hD
    simpa only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] using hh
  apply Matrix.mulVec_injective_iff.mp
  intro v w hvw
  have hh := congrArg (fun x => (D.map (Int.castRingHom K)).mulVec x) hvw
  simpa only [Matrix.mulVec_mulVec, hm, Matrix.one_mulVec] using hh

/-- Existence of a finite saturated lattice basis with independent reduction.
No Smith-normal-form assertion is assumed. -/
theorem descriptor_integer_lattice_basis (K : Type*) [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Submodule ℚ (ι → ℚ)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (descriptorIntegerLattice H)),
      LinearIndependent K
        ((descriptorLatticeBasisMatrix b).map (Int.castRingHom K)).col := by
  obtain ⟨n, ⟨b⟩⟩ := Submodule.nonempty_basis_of_pid (Pi.basisFun ℤ ι) (descriptorIntegerLattice H)
  exact ⟨n, b, descriptor_lattice_basis_reduction_independent (K := K) H b⟩

end AdaptiveOrthogonalRigidity
