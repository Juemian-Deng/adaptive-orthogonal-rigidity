import AdaptiveOrthogonalRigidity.FiniteDescriptorCount
import AdaptiveOrthogonalRigidity.BoundaryKrylov

open MeasureTheory Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

noncomputable def descriptorInputEquiv (κ : Type*) [Fintype κ] :
    Fin (Fintype.card κ + 1) ≃ Option κ := Fintype.equivOfCardEq (by simp)

/-- The full original constant mark and cross columns, only relabelled by Fin. -/
noncomputable def descriptorCutInputs {N : ℕ} {κ : Type*} [Fintype κ]
    (Y : (Fin N × κ) → Bool) : Matrix (Fin N) (Fin (Fintype.card κ + 1)) (ZMod 3) :=
  fun i j => (descriptorInputEquiv κ j).elim 1 (fun s => bitValue (Y (i, s)))

noncomputable def cutDescriptorFailure (N k R : ℕ) (κ : Type*) [Fintype κ] :
    Set (((Fin N × κ) ⊕ Edge N) → Bool) :=
  {ω | (fun e => ω (Sum.inr e)) ∈ packedDescriptorEvent (k := k) (R := R) (fun _ => 0)
    (descriptorCutInputs (fun q => ω (Sum.inl q)))}

/-- Fixed-cut Fubini: the packed descriptor bound is applied to the original
bulk law for each cross assignment, without conditioning on Krylov success. -/
theorem cut_descriptor_probability {N k R : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    {α : ℝ} (hα : 0 < α) (hαhalf : α ≤ 1 / 2) (hk : 1 ≤ k) (hR : 1 ≤ R)
    (hkR : k * R ≤ N) (p : ((Fin N × κ) ⊕ Edge N) → unitInterval)
    (hp : ∀ e, α ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - α) :
    (cubeMeasure p).real (cutDescriptorFailure N k R κ) ≤
      (2 / 3 : ℝ) ^ N * 3 ^ (2 * k ^ 2 + 2 * (Fintype.card κ + 1) * k +
        k + (Fintype.card κ + 1) + k ^ 2 * R) *
        (1 + 2 * (kappa α) ^ R) ^ (k * (N - k * R)) := by
  apply cube_event_le_of_split_bound p (Equiv.sumComm (Edge N) (Fin N × κ))
  intro Y
  have hh := finite_descriptor_probability hα hαhalf hk hR hkR
    (fun e => p (Sum.inr e)) (fun e => hp (Sum.inr e)) (fun _ => 0) (descriptorCutInputs Y)
  change (cubeMeasure (fun e => p (Sum.inr e))).real
    (packedDescriptorEvent (k := k) (R := R) (fun _ => 0) (descriptorCutInputs Y)) ≤ _
  exact hh

noncomputable def fixedBoundaryDescriptorFailure {n : ℕ} (S : Finset (Fin n)) (k R : ℕ) :
    Set (GraphSample n) :=
  {ω | (fun e => ω (boundaryKrylovCoordinates S e)) ∈ cutDescriptorFailure (n - S.card) k R S}

noncomputable def boundaryDescriptorFailure (n b r R : ℕ) : Set (GraphSample n) :=
  {ω | ∃ S : Finset (Fin n), S.card ≤ b ∧ ∃ k ∈ Finset.Icc 1 r,
    ω ∈ fixedBoundaryDescriptorFailure S k R}

/-- Original unordered-edge specialization retaining each heterogeneous parameter. -/
theorem fixed_boundary_descriptor_bound {n k R : ℕ} (S : Finset (Fin n))
    {α : ℝ} (hα : 0 < α) (hαhalf : α ≤ 1 / 2) (hk : 1 ≤ k) (hR : 1 ≤ R)
    (hkR : k * R ≤ n - S.card) (p : EdgeParameters n) (hp : Admissible α p) :
    eventProbability p (fixedBoundaryDescriptorFailure S k R) ≤
      (2 / 3 : ℝ) ^ (n - S.card) * 3 ^ (2 * k ^ 2 + 2 * (S.card + 1) * k +
        k + (S.card + 1) + k ^ 2 * R) *
        (1 + 2 * (kappa α) ^ R) ^ (k * (n - S.card - k * R)) := by
  rw [show eventProbability p (fixedBoundaryDescriptorFailure S k R) =
      (cubeMeasure (fun e => p (boundaryKrylovCoordinates S e))).real
        (cutDescriptorFailure (n - S.card) k R S) from
    cube_injective_projection_probability p (boundaryKrylovCoordinates S) _]
  simpa only [Fintype.card_coe] using cut_descriptor_probability hα hαhalf hk hR hkR
    (fun e => p (boundaryKrylovCoordinates S e)) (fun e => hp (boundaryKrylovCoordinates S e))

end AdaptiveOrthogonalRigidity
