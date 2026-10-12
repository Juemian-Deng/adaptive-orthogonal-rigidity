import AdaptiveOrthogonalRigidity.Model
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic

/-! Exact numerical bounds from the manuscript. These definitions are not proofs
that they bound an event probability. Real exponents deliberately preserve
negative values in the Krylov estimate and fractional values in block epsilon. -/

open scoped BigOperators

namespace AdaptiveOrthogonalRigidity

noncomputable def beta (α : ℝ) : ℝ := 1 - α
noncomputable def gamma (α : ℝ) : ℝ := 1 - α ^ 2
noncomputable def coverRate (α : ℝ) : ℝ := Real.log (1 / beta α)
noncomputable def kappa (α : ℝ) : ℝ := Real.sqrt (1 - 3 * α * (1 - α))
noncomputable def coverEntropy (n : ℕ) : ℝ :=
  4 * Real.log n + 2 * Real.log (1 + 4 * (n : ℝ) ^ 2)

def boundaryCount (n b : ℕ) : ℕ :=
  ∑ s ∈ Finset.range (b + 1), n.choose s

def rootCount (d : ℕ) : ℕ := ∑ a ∈ Finset.Icc 1 d, a * 3 ^ a

def markPairCount (d : ℕ) : ℕ := ∑ a ∈ Finset.Icc 1 d, 3 ^ (2 * a - 1)

noncomputable def initialBoundary (lam : ℝ) (r : ℕ) : ℕ := ⌈4 * lam * r⌉₊

noncomputable def totalBoundary (lam : ℝ) (r R : ℕ) : ℕ :=
  initialBoundary lam r + R * r

noncomputable def krylovBound (α : ℝ) (n r t b : ℕ) : ℝ :=
  (boundaryCount n b : ℝ) *
    (((3 : ℝ) ^ ((2 * r + 1) * (b + 1)) + markPairCount (2 * r)) *
        (beta α) ^ ((n : ℝ) - b - 1 - 2 * r * t) +
      2 * rootCount (2 * r) * (2 : ℝ) ^ n *
        (beta α) ^ (((t : ℝ) ^ 2 - 1) / 4))

noncomputable def descriptorBound (α : ℝ) (n r R b : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (b + 1), (n.choose s : ℝ) *
    ∑ k ∈ Finset.Icc 1 r,
      (2 / 3 : ℝ) ^ (n - s) *
      (3 : ℝ) ^ (2 * k ^ 2 + 2 * (s + 1) * k + k + (s + 1) + k ^ 2 * R) *
      (1 + 2 * (kappa α) ^ R) ^ (k * (n - s - k * R))

noncomputable def cubeBound (α : ℝ) (n b : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (b + 1),
    (n.choose s : ℝ) * (3 : ℝ) ^ (s + 1) * (gamma α) ^ (n - s)

noncomputable def finiteMovementBound (α lam : ℝ) (n r R t : ℕ) : ℝ :=
  let b := totalBoundary lam r R
  (n : ℝ) ^ 4 * Real.exp (-coverRate α * lam ^ 2 / 2) +
    krylovBound α n r t b + descriptorBound α n r R b + cubeBound α n b

def symmetricDimension (b : ℕ) : ℕ := b * (b + 1) / 2

noncomputable def blockEpsilon (α : ℝ) (n b : ℕ) : ℝ :=
  2 * ((b : ℝ) + 1) ^ (symmetricDimension b) *
    (gamma α) ^ ((n : ℝ) / (4 * b) - 1)

noncomputable def blockCandidateCount (n b : ℕ) : ℝ :=
  ((b : ℝ) - 1) * (n : ℝ) ^ b

noncomputable def blockY (α : ℝ) (n b : ℕ) : ℝ :=
  blockCandidateCount n b * (blockEpsilon α n b) ^ (1 / 3 : ℝ)

def leftBlockCount (q : ℕ) : ℕ := if q = 1 then 1 else q / 2

noncomputable def finiteBlockSum (α : ℝ) (n b : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 (n / 2),
    (blockCandidateCount n b) ^ q *
      (min 1 (blockEpsilon α n b)) ^ (leftBlockCount q)

end AdaptiveOrthogonalRigidity
