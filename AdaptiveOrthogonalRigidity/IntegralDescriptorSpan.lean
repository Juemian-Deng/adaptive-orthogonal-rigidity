import AdaptiveOrthogonalRigidity.IntegralDescriptorLattice
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Dimension.Constructions

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Integer coordinates in an actual lattice basis reconstruct the original
ambient integer vector. -/
theorem descriptor_lattice_basis_coordinates {ι σ : Type*} [Fintype σ]
    (H : Submodule ℚ (ι → ℚ)) (b : Module.Basis σ ℤ (descriptorIntegerLattice H))
    (v : descriptorIntegerLattice H) :
    (descriptorLatticeBasisMatrix b).mulVec (b.equivFun v) = v.val := by
  have hh := congrArg (fun w : descriptorIntegerLattice H => w.val) (b.sum_repr v)
  rw [Matrix.mulVec_eq_sum]
  have hc (j : σ) : (descriptorLatticeBasisMatrix b).col j = (b j).val := rfl
  simpa only [op_smul_eq_smul, descriptorLatticeBasisMatrix, ← Matrix.col_def,
    Submodule.coe_sum, Submodule.coe_smul, Module.Basis.equivFun_apply, hc] using hh

/-- Clearing a common denominator puts every rational subspace vector in its
full integer lattice after multiplication by a nonzero integer. -/
theorem descriptor_lattice_clear_denominators {ι : Type*} [Fintype ι]
    (H : Submodule ℚ (ι → ℚ)) (w : ι → ℚ) (hw : w ∈ H) :
    ∃ (a : ℤ) (v : descriptorIntegerLattice H), a ≠ 0 ∧
      (fun i => (v.val i : ℚ)) = (a : ℚ) • w := by
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) w
  choose v hv using ha
  have he : (fun i => (v i : ℚ)) = (a.val : ℚ) • w := by
    funext i
    change (v i : ℚ) = (a.val : ℚ) * w i
    exact hv i
  have hmem : v ∈ descriptorIntegerLattice H := by
    rw [descriptorIntegerLattice_mem, he]
    exact H.smul_mem _ hw
  refine ⟨a.val, ⟨v, hmem⟩, ?_, he⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mp a.property

/-- Extending a full saturated integer lattice basis to Q spans precisely the
original rational subspace. The denominator-clearing direction is explicit. -/
theorem descriptor_lattice_basis_rational_range {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (H : Submodule ℚ (ι → ℚ)) (b : Module.Basis σ ℤ (descriptorIntegerLattice H)) :
    ((descriptorLatticeBasisMatrix b).map (Int.castRingHom ℚ)).mulVecLin.range = H := by
  apply le_antisymm
  · rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact (b j).property
  · intro w hw
    obtain ⟨a, v, ha, he⟩ := descriptor_lattice_clear_denominators H w hw
    have hmem : (fun i => (v.val i : ℚ)) ∈
        ((descriptorLatticeBasisMatrix b).map (Int.castRingHom ℚ)).mulVecLin.range := by
      refine ⟨fun j => ((b.equivFun v j : ℤ) : ℚ), ?_⟩
      funext i
      have hh := congrArg (fun z : ι → ℤ => (z i : ℚ)) (descriptor_lattice_basis_coordinates H b v)
      change ((descriptorLatticeBasisMatrix b).map (Int.castRingHom ℚ)).mulVec _ i = _
      exact (RingHom.map_mulVec (Int.castRingHom ℚ) (descriptorLatticeBasisMatrix b)
        (b.equivFun v) i).symm.trans hh
    rw [he] at hmem
    have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha
    have hh := (((descriptorLatticeBasisMatrix b).map (Int.castRingHom ℚ)).mulVecLin.range).smul_mem
      (a : ℚ)⁻¹ hmem
    simpa only [smul_smul, inv_mul_cancel₀ haQ, one_smul] using hh

/-- The rank of the saturated integer lattice is exactly the rational
subspace dimension; neither direction is assumed. -/
theorem descriptor_lattice_basis_card {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (H : Submodule ℚ (ι → ℚ)) (b : Module.Basis σ ℤ (descriptorIntegerLattice H)) :
    Fintype.card σ = Module.finrank ℚ H := by
  have hh := finrank_span_eq_card (descriptor_lattice_basis_reduction_independent (K := ℚ) H b)
  rw [← Matrix.range_mulVecLin, descriptor_lattice_basis_rational_range H b] at hh
  exact hh.symm

/-- A saturated rational subspace has an integer basis with the exact rational
dimension and independent reduction into any field. -/
theorem descriptor_integer_basis_exact_rank (K : Type*) [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Submodule ℚ (ι → ℚ)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (descriptorIntegerLattice H)),
      n = Module.finrank ℚ H ∧
      LinearIndependent K ((descriptorLatticeBasisMatrix b).map (Int.castRingHom K)).col := by
  obtain ⟨n, b, hb⟩ := descriptor_integer_lattice_basis K H
  refine ⟨n, b, ?_, hb⟩
  simpa only [Fintype.card_fin] using descriptor_lattice_basis_card H b

end AdaptiveOrthogonalRigidity
