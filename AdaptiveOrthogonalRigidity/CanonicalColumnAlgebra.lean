import AdaptiveOrthogonalRigidity.KrylovControlledSpace

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

def augmentedColumns {K ι κ : Type*} [One K] (Y : Matrix ι κ K) : Option κ → ι → K :=
  fun j => j.elim (fun _ => 1) (fun j => Y.col j)

def augmentedColumnMatrix {K ι κ : Type*} [One K] (Y : Matrix ι κ K) : Matrix ι (Option κ) K :=
  fun i j => augmentedColumns Y j i

theorem augmented_mulVec_zero_head {K ι κ : Type*} [CommRing K] [Fintype κ]
    (Y : Matrix ι κ K) (w : κ → K) :
    (augmentedColumnMatrix Y).mulVec (fun j => j.elim 0 w) = Y.mulVec w := by
  ext i
  simp [Matrix.mulVec, dotProduct, augmentedColumnMatrix, augmentedColumns, Fintype.sum_option]

theorem augmented_columns_independent_base {K ι κ : Type*} [Field K] [Fintype ι]
    [DecidableEq ι] (C : Matrix ι ι K) (Y : Matrix ι κ K) (r : ℕ)
    (hI : LinearIndependent K (krylovColumns r C (augmentedColumns Y))) :
    LinearIndependent K (augmentedColumns Y) := by
  let f : Option κ → Fin (r + 1) × Option κ := fun j => (⟨0, Nat.zero_lt_succ r⟩, j)
  have hf : Function.Injective f := fun a b h => congrArg Prod.snd h
  have hh := hI.comp f hf
  simpa only [f, Function.comp_def, krylovColumns, pow_zero, Matrix.one_mulVec] using hh

theorem independent_augmented_ones_not_range {K ι κ : Type*} [Field K]
    [Fintype κ] (Y : Matrix ι κ K)
    (hI : LinearIndependent K (augmentedColumns Y)) (w : κ → K) :
    Y.mulVec w ≠ fun _ => 1 := by
  intro heq
  have hinj : Function.Injective (augmentedColumnMatrix Y).mulVec :=
    Matrix.mulVec_injective_iff.mpr hI
  have hh : (augmentedColumnMatrix Y).mulVec (fun j => j.elim 0 w) =
      (augmentedColumnMatrix Y).mulVec (Pi.single none 1) := by
    rw [augmented_mulVec_zero_head, Matrix.mulVec_single_one, heq]
    rfl
  have h := congrFun (hinj hh) none
  simp at h

/-- The exact real canonical list used by the graph boundary argument. -/
def CanonicalRealColumn {ι κ : Type*} (Y : Matrix ι κ ℝ) (z : ι → ℝ) : Prop :=
  z = 0 ∨ z = (fun _ => 1) ∨ ∃ j, z = Y.col j ∨ z = (fun _ => 1) - Y.col j

/-- Independence of [1,Y] forces a nonzero coefficient vector of a canonical
column in col Y to be a positive coordinate vector. -/
theorem canonical_column_coefficients {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (Y : Matrix ι κ ℝ) (hI : LinearIndependent ℝ (augmentedColumns Y))
    (w : κ → ℝ) (hw : w ≠ 0) (hz : CanonicalRealColumn Y (Y.mulVec w)) :
    ∃ j, w = Pi.single j 1 := by
  have hY : LinearIndependent ℝ Y.col := hI.comp Option.some (Option.some_injective _)
  have hinj := Matrix.mulVec_injective_iff.mpr hY
  rcases hz with hz | hz | ⟨j, hz | hz⟩
  · exact False.elim (hw (hinj (by simpa only [Matrix.mulVec_zero] using hz)))
  · exact False.elim (independent_augmented_ones_not_range Y hI w hz)
  · refine ⟨j, hinj ?_⟩
    simpa only [Matrix.mulVec_single_one] using hz
  · apply False.elim
    apply independent_augmented_ones_not_range Y hI (w + Pi.single j 1)
    rw [Matrix.mulVec_add, Matrix.mulVec_single_one, hz, sub_add_cancel]

end AdaptiveOrthogonalRigidity
