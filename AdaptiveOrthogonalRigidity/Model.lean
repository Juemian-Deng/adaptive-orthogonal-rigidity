import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Bernoulli

/-!
# Original heterogeneous random graph model

This is the SECOND manuscript's model, independent of the earlier index/support
formalization. The definitions and accompanying foundation lemmas have been compiled. No
probability bound from the manuscript is asserted by this file.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace AdaptiveOrthogonalRigidity

/-- One coordinate for each unordered pair of distinct labelled vertices. -/
abbrev Edge (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}

/-- All simple labelled graphs, with no restriction on the sampled graph. -/
abbrev GraphSample (n : ℕ) := Edge n → Bool

abbrev RealMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def bitReal (b : Bool) : ℝ := if b then 1 else 0

/-- Reflect the upper-triangular independent bits and set the diagonal to zero. -/
def adjacency {n : ℕ} (ω : GraphSample n) : RealMatrix n := fun i j =>
  if h : i < j then bitReal (ω ⟨(i, j), h⟩)
  else if h' : j < i then bitReal (ω ⟨(j, i), h'⟩)
  else 0

/-- The usual real ordinary graph matrices. No loops, signs, or weights. -/
def Ordinary {n : ℕ} (A : RealMatrix n) : Prop :=
  (∀ i j, A i j = A j i) ∧
  (∀ i, A i i = 0) ∧
  (∀ i j, A i j = 0 ∨ A i j = 1)

/-- Both standard inverse identities for a real square orthogonal matrix. -/
def Orthogonal {n : ℕ} (Q : RealMatrix n) : Prop :=
  Q.transpose * Q = 1 ∧ Q * Q.transpose = 1

/-- Only an ordinary permutation, with its nonzero entries equal to +1. -/
def permutationMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) : RealMatrix n :=
  fun i j => if σ i = j then 1 else 0

def conjugate {n : ℕ} (A Q : RealMatrix n) : RealMatrix n :=
  Q.transpose * A * Q

/-- Isomorphism uses ordinary permutations, not signed permutations. -/
def OrdinarilyIsomorphic {n : ℕ} (A B : RealMatrix n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), B = conjugate A (permutationMatrix σ)

/-- Existential form of the minimum over the finite ordinary permutation group. -/
def MovementRankAtMost {n : ℕ} (Q : RealMatrix n) (r : ℕ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), (Q - permutationMatrix σ).rank ≤ r

/-- The actual bipartite nonzero-support graph: rows and columns are different vertices. -/
def SupportAdjacent {n : ℕ} (Q : RealMatrix n) :
    Fin n ⊕ Fin n → Fin n ⊕ Fin n → Prop
  | Sum.inl i, Sum.inr j => Q i j ≠ 0
  | Sum.inr j, Sum.inl i => Q i j ≠ 0
  | _, _ => False

/-- Since SupportAdjacent is symmetric, this is undirected component reachability. -/
def SupportReachable {n : ℕ} (Q : RealMatrix n)
    (v w : Fin n ⊕ Fin n) : Prop :=
  Relation.ReflTransGen (SupportAdjacent Q) v w

/-- The row size of every actual support component. Orthogonal balance is a separate lemma. -/
def SupportComponentCap {n : ℕ} (Q : RealMatrix n) (b : ℕ) : Prop :=
  ∀ v : Fin n ⊕ Fin n,
    Nat.card {i : Fin n // SupportReachable Q v (Sum.inl i)} ≤ b

/-- Fully adaptive movement-rank event: the real witness is chosen inside the event. -/
def movementEvent (n r : ℕ) : Set (GraphSample n) :=
  {ω | ∃ Q B : RealMatrix n,
    Orthogonal Q ∧ Ordinary B ∧ B = conjugate (adjacency ω) Q ∧
    ¬ OrdinarilyIsomorphic (adjacency ω) B ∧ MovementRankAtMost Q r}

/-- Fully adaptive bounded-component event, with no bound on the number of components. -/
def blockEvent (n b : ℕ) : Set (GraphSample n) :=
  {ω | ∃ Q B : RealMatrix n,
    Orthogonal Q ∧ Ordinary B ∧ B = conjugate (adjacency ω) Q ∧
    ¬ OrdinarilyIsomorphic (adjacency ω) B ∧ SupportComponentCap Q b}

/-- A deterministic heterogeneous edge array. Endpoints 0 and 1 are available in
this ambient type, then excluded by the positive-alpha admissibility condition. -/
abbrev EdgeParameters (n : ℕ) := Edge n → unitInterval

def Admissible {n : ℕ} (α : ℝ) (p : EdgeParameters n) : Prop :=
  ∀ e, α ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - α

/-- The genuine independent product of Bernoulli edge distributions. -/
noncomputable def graphMeasure {n : ℕ} (p : EdgeParameters n) :
    Measure (GraphSample n) :=
  Measure.pi (fun e => bernoulliMeasure true false (p e))

/-- Real-valued event probability. The underlying space is finite and discrete. -/
noncomputable def eventProbability {n : ℕ} (p : EdgeParameters n)
    (E : Set (GraphSample n)) : ℝ :=
  (graphMeasure p).real E

end AdaptiveOrthogonalRigidity
