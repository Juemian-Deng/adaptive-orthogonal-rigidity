import AdaptiveOrthogonalRigidity.OneCoordinateFiber
import Mathlib.Data.ZMod.Basic

open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

def bitValue {R : Type*} [Zero R] [One R] (b : Bool) : R := if b then 1 else 0

def boolVector {ι R : Type*} [Zero R] [One R] (x : ι → Bool) : ι → R :=
  fun i => bitValue (x i)

def quadraticValue {ι R : Type*} [Fintype ι] [CommRing R]
    (H : Matrix ι ι R) (v : ι → R) : R := v ⬝ᵥ H.mulVec v

def cubeQuadratic {ι R : Type*} [Fintype ι] [CommRing R]
    (H : Matrix ι ι R) (x : ι → Bool) : R := quadraticValue H (boolVector x)

theorem boolVector_patchTwo {ι R : Type*} [DecidableEq ι] [CommRing R]
    (i j : ι) (hij : i ≠ j) (r : OtherCoordinates i j → Bool) (a b : Bool) :
    boolVector (R := R) (patchTwo i j r a b) =
      boolVector (patchTwo i j r false false) +
        Pi.single i (bitValue a) + Pi.single j (bitValue b) := by
  funext k
  by_cases hi : k = i
  · subst k; simp [boolVector, patchTwo, hij, bitValue]
  · by_cases hj : k = j
    · subst k; simp [boolVector, patchTwo, hi, bitValue]
    · simp [boolVector, patchTwo, hi, hj, bitValue]

theorem quadratic_mixed_difference {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (H : Matrix ι ι R) (v : ι → R) (i j : ι) :
    quadraticValue H (v + Pi.single i 1 + Pi.single j 1) -
      quadraticValue H (v + Pi.single i 1) -
      quadraticValue H (v + Pi.single j 1) + quadraticValue H v = H i j + H j i := by
  simp [quadraticValue, Matrix.mulVec_add, dotProduct_add, add_dotProduct,
    single_dotProduct]
  ring

theorem cubeQuadratic_pair_mixed {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (H : Matrix ι ι R) (i j : ι) (hij : i ≠ j)
    (r : OtherCoordinates i j → Bool) :
    cubeQuadratic H (patchTwo i j r true true) -
      cubeQuadratic H (patchTwo i j r true false) -
      cubeQuadratic H (patchTwo i j r false true) +
      cubeQuadratic H (patchTwo i j r false false) = H i j + H j i := by
  unfold cubeQuadratic
  rw [boolVector_patchTwo i j hij r true true,
      boolVector_patchTwo i j hij r true false,
      boolVector_patchTwo i j hij r false true]
  simpa [bitValue] using
    quadratic_mixed_difference H (boolVector (patchTwo i j r false false)) i j

theorem cubeQuadratic_diagonal {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (H : Matrix ι ι R) (hdiag : ∀ i j, i ≠ j → H i j = 0)
    (x : ι → Bool) : cubeQuadratic H x = ∑ i, H i i * bitValue (x i) := by
  unfold cubeQuadratic quadraticValue dotProduct Matrix.mulVec
  apply Finset.sum_congr rfl
  intro i _
  change boolVector x i * (∑ j, H i j * boolVector x j) = H i i * bitValue (x i)
  have hs : ∑ j, H i j * boolVector (R := R) x j = H i i * boolVector x i := by
    apply Finset.sum_eq_single i
    · intro j _ hji; simp [hdiag i j (Ne.symm hji)]
    · simp
  rw [hs]
  cases hx : x i <;> simp [boolVector, bitValue, hx]

theorem cubeQuadratic_diagonal_single_difference {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R] (H : Matrix ι ι R)
    (hdiag : ∀ i j, i ≠ j → H i j = 0) (i : ι)
    (r : RemainingCoordinates i → Bool) :
    cubeQuadratic H (patchOne i r true) - cubeQuadratic H (patchOne i r false) = H i i := by
  rw [cubeQuadratic_diagonal H hdiag, cubeQuadratic_diagonal H hdiag, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp [patchOne, bitValue]
  · intro j _ hji; simp [patchOne, hji]
  · simp

end AdaptiveOrthogonalRigidity
