import AdaptiveOrthogonalRigidity.RationalControlledEmbedded
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.Data.Matrix.ColumnRowPartitioned

open Matrix Polynomial
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- The actual embedded initial state/output orbit, retaining all outputs. -/
def embeddedOrbitSpan {K ι σ υ : Type*} [Field K] [Fintype σ] [DecidableEq σ]
    (X : Matrix ι σ K) (M : Matrix σ σ K) (L₀ : Matrix σ υ K) : Submodule K (ι → K) :=
  Submodule.span K (Set.range (fun aj : Fin (Fintype.card σ) × υ =>
    X.mulVec ((M ^ aj.1.val).mulVec (L₀.col aj.2))))

/-- Cayley-Hamilton places every later embedded coefficient in the initial
joint-output span, including the zero-dimensional case. -/
theorem embedded_orbit_mem_initial_span {K ι σ υ : Type*} [Field K]
    [Fintype σ] [DecidableEq σ]
    (X : Matrix ι σ K) (M : Matrix σ σ K) (L₀ : Matrix σ υ K) (n : ℕ) (j : υ) :
    X.mulVec ((M ^ n).mulVec (L₀.col j)) ∈ embeddedOrbitSpan X M L₀ := by
  by_cases hk : Fintype.card σ = 0
  · have : IsEmpty σ := Fintype.card_eq_zero_iff.mp hk
    have hz : X.mulVec ((M ^ n).mulVec (L₀.col j)) = 0 := by
      funext i
      simp [Matrix.mulVec, dotProduct]
    rw [hz]
    exact Submodule.zero_mem _
  let q : Polynomial K := Polynomial.X ^ n %ₘ M.charpoly
  have hM : M.charpoly ≠ 1 := by
    intro he
    have hd := congrArg Polynomial.natDegree he
    exact hk (by simpa only [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_one] using hd)
  have hq : q.natDegree < Fintype.card σ := by
    simpa only [Matrix.charpoly_natDegree_eq_dim] using
      Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ n) M.charpoly_monic hM
  rw [M.pow_eq_aeval_mod_charpoly n,
    Polynomial.aeval_eq_sum_range' (n := Fintype.card σ) hq,
    Matrix.sum_mulVec, Matrix.mulVec_sum]
  apply Submodule.sum_mem
  intro a ha
  rw [Matrix.smul_mulVec, Matrix.mulVec_smul]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(⟨a, Finset.mem_range.mp ha⟩, j), rfl⟩

/-- The joint embedded output span satisfies the same controlled inclusion. -/
theorem embedded_orbit_span_controlled {K ι σ τ υ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ]
    (C : Matrix ι ι K) (X : Matrix ι σ K) (M : Matrix σ σ K)
    (V : Matrix ι τ K) (F : Matrix τ σ K) (L₀ : Matrix σ υ K)
    (h : C * X = X * M + V * F) :
    ∀ w ∈ embeddedOrbitSpan X M L₀,
      C.mulVec w ∈ embeddedOrbitSpan X M L₀ ⊔ V.mulVecLin.range := by
  change embeddedOrbitSpan X M L₀ ≤
    (embeddedOrbitSpan X M L₀ ⊔ V.mulVecLin.range).comap C.mulVecLin
  apply Submodule.span_le.mpr
  rintro _ ⟨aj, rfl⟩
  have hh := congrArg (fun A => A.mulVec ((M ^ aj.1.val).mulVec (L₀.col aj.2))) h
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec] at hh
  change C.mulVec (X.mulVec ((M ^ aj.1.val).mulVec (L₀.col aj.2))) ∈
    embeddedOrbitSpan X M L₀ ⊔ V.mulVecLin.range
  rw [hh]
  apply Submodule.add_mem
  · apply Submodule.mem_sup_left
    rw [Matrix.mulVec_mulVec (L₀.col aj.2) M (M ^ aj.1.val), ← pow_succ']
    exact embedded_orbit_mem_initial_span X M L₀ (aj.1.val + 1) aj.2
  · exact Submodule.mem_sup_right ⟨_, rfl⟩

/-- Rational/base-field subspace sum membership descends by a genuine finite
linear system, rather than by any cast from a positive-characteristic field. -/
theorem matrix_range_sup_descends {K L ι α β : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype α] [Fintype β]
    (A : Matrix ι α K) (B : Matrix ι β K) (z : ι → K)
    (hz : (fun i => algebraMap K L (z i)) ∈
      (A.map (algebraMap K L)).mulVecLin.range ⊔ (B.map (algebraMap K L)).mulVecLin.range) :
    z ∈ A.mulVecLin.range ⊔ B.mulVecLin.range := by
  obtain ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, he⟩ := Submodule.mem_sup.mp hz
  obtain ⟨v, hv⟩ := descend_finite_linear_system (L := L) (Matrix.fromCols A B) z (by
    refine ⟨Sum.elim a b, ?_⟩
    rw [Matrix.fromCols_map, Matrix.fromCols_mulVec_sumElim]
    exact he)
  rw [Matrix.fromCols_mulVec] at hv
  exact Submodule.mem_sup.mpr ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, hv⟩

/-- The coordinatewise field inclusion as a base-field linear map. -/
def controlledScalarExtensionMap (K L ι : Type*) [Field K] [Field L] [Algebra K L] :
    (ι → K) →ₗ[K] (ι → L) :=
  LinearMap.pi (fun i => (Algebra.linearMap K L).comp (LinearMap.proj i))

/-- A rational/base-field space contained in an extension-field space cannot
have larger dimension. The proof uses genuine scalar-extension independence. -/
theorem controlled_base_subspace_finrank_le {K L ι : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype ι]
    (S : Submodule K (ι → K)) (H : Submodule L (ι → L))
    (h : ∀ w ∈ S, (fun i => algebraMap K L (w i)) ∈ H) :
    Module.finrank K S ≤ Module.finrank L H := by
  let b := Module.finBasis K S
  have hb : LinearIndependent K (fun i => ((b i : S) : ι → K)) :=
    b.linearIndependent.map' S.subtype S.ker_subtype
  have he : LinearIndependent L (fun j => (algebraMap K L) ∘ ((b j : S) : ι → K)) :=
    linearIndependent_algebraMap_comp_iff.mpr hb
  let c : Fin (Module.finrank K S) → H := fun j => ⟨_, h (b j) (b j).property⟩
  have hc : LinearIndependent L c := by
    apply LinearIndependent.of_comp H.subtype
    exact he
  have hh := hc.fintype_card_le_finrank
  simpa only [Fintype.card_fin] using hh

/-- A realization over an arbitrary extension field admits a controlled
base-field subspace inside its original embedded state space. All output
columns are retained, and no rationality is assumed of X, M, F, L₀, or G. -/
theorem controlled_realization_base_subspace {K L ι σ τ υ : Type*}
    [Field K] [Field L] [Algebra K L]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [Fintype τ] [Fintype υ]
    (C : Matrix ι ι K) (V : Matrix ι τ K) (Z : Matrix ι υ K)
    (X : Matrix ι σ L) (M : Matrix σ σ L) (F : Matrix τ σ L)
    (L₀ : Matrix σ υ L) (G : Matrix τ υ L)
    (hX : C.map (algebraMap K L) * X = X * M + V.map (algebraMap K L) * F)
    (hZ : Z.map (algebraMap K L) = X * L₀ + V.map (algebraMap K L) * G)
    (hI : LinearIndependent L (krylovColumns (2 * Fintype.card σ)
      (C.map (algebraMap K L)) (V.map (algebraMap K L)).col))
    (H : Submodule L (ι → L)) (hH : X.mulVecLin.range ≤ H) :
    ∃ S : Submodule K (ι → K),
      Module.finrank K S ≤ Module.finrank L H ∧
      (∀ w ∈ S, (fun i => algebraMap K L (w i)) ∈ H) ∧
      (∀ w ∈ S, C.mulVec w ∈ S ⊔ V.mulVecLin.range) ∧
      Z.mulVecLin.range ≤ S ⊔ V.mulVecLin.range := by
  have hd := controlled_realization_embedded_columns_descend C V Z X M F L₀ G hX hZ hI
  choose W hW using fun aj : Fin (Fintype.card σ) × υ => hd aj.1 aj.2
  let A : Matrix ι (Fin (Fintype.card σ) × υ) K := fun i aj => W aj i
  have hcol : (A.map (algebraMap K L)).col =
      fun aj : Fin (Fintype.card σ) × υ => X.mulVec ((M ^ aj.1.val).mulVec (L₀.col aj.2)) := by
    funext aj
    exact hW aj
  have hArange : (A.map (algebraMap K L)).mulVecLin.range = embeddedOrbitSpan X M L₀ := by
    rw [Matrix.range_mulVecLin, hcol]
    rfl
  have hEH : embeddedOrbitSpan X M L₀ ≤ H := by
    apply Submodule.span_le.mpr
    rintro _ ⟨aj, rfl⟩
    exact hH ⟨_, rfl⟩
  have hcastE : ∀ w ∈ A.mulVecLin.range,
      (fun i => algebraMap K L (w i)) ∈ embeddedOrbitSpan X M L₀ := by
    rintro w ⟨u, rfl⟩
    rw [← hArange]
    refine ⟨fun j => algebraMap K L (u j), ?_⟩
    funext i
    exact (RingHom.map_mulVec (algebraMap K L) A u i).symm
  have hcastH : ∀ w ∈ A.mulVecLin.range, (fun i => algebraMap K L (w i)) ∈ H :=
    fun w hw => hEH (hcastE w hw)
  refine ⟨A.mulVecLin.range, controlled_base_subspace_finrank_le _ H hcastH, hcastH, ?_, ?_⟩
  · intro w hw
    apply matrix_range_sup_descends (L := L) A V (C.mulVec w)
    rw [hArange]
    have hh := embedded_orbit_span_controlled (C.map (algebraMap K L)) X M
      (V.map (algebraMap K L)) F L₀ hX _ (hcastE w hw)
    have he : (fun i => algebraMap K L (C.mulVec w i)) =
        (C.map (algebraMap K L)).mulVec (fun i => algebraMap K L (w i)) := by
      funext i
      exact RingHom.map_mulVec (algebraMap K L) C w i
    rwa [he]
  · rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    apply matrix_range_sup_descends (L := L) A V (Z.col j)
    rw [hArange]
    have he : (fun i => algebraMap K L (Z.col j i)) =
        X.mulVec (L₀.col j) + (V.map (algebraMap K L)).mulVec (G.col j) := by
      funext i
      exact congrFun (congrFun hZ i) j
    rw [he]
    apply Submodule.add_mem
    · apply Submodule.mem_sup_left
      simpa only [pow_zero, Matrix.one_mulVec] using embedded_orbit_mem_initial_span X M L₀ 0 j
    · exact Submodule.mem_sup_right ⟨_, rfl⟩

end AdaptiveOrthogonalRigidity
