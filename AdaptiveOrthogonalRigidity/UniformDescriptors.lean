import AdaptiveOrthogonalRigidity.BoundaryDescriptors

open MeasureTheory
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

noncomputable def descriptorStateBound (α : ℝ) (n s k R : ℕ) : ℝ :=
  (2 / 3 : ℝ) ^ (n - s) * 3 ^ (2 * k ^ 2 + 2 * (s + 1) * k + k + (s + 1) + k ^ 2 * R) *
    (1 + 2 * (kappa α) ^ R) ^ (k * (n - s - k * R))

/-- Exact D_n, uniformly over all original boundaries and positive state
sizes. The descriptor union includes all adaptive binary outputs. -/
theorem uniform_descriptor_bound {n b r R : ℕ} {α : ℝ}
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) (hR : 1 ≤ R) (hbudget : R * r ≤ n - b)
    (p : EdgeParameters n) (hp : Admissible α p) :
    eventProbability p (boundaryDescriptorFailure n b r R) ≤ descriptorBound α n r R b := by
  let Q := Finset.range (b + 1)
  let K := Finset.Icc 1 r
  let E (q : Q) : Set (GraphSample n) :=
    ⋃ S : (Finset.univ : Finset (Fin n)).powersetCard q.val,
      ⋃ k : K, fixedBoundaryDescriptorFailure S.val k.val R
  have hsub : boundaryDescriptorFailure n b r R ⊆ ⋃ q : Q, E q := by
    rintro ω ⟨S, hS, k, hk, hω⟩
    refine Set.mem_iUnion.mpr ⟨⟨S.card, Finset.mem_range.mpr (by omega)⟩, ?_⟩
    exact Set.mem_iUnion.mpr ⟨⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩,
      Set.mem_iUnion.mpr ⟨⟨k, hk⟩, hω⟩⟩
  have hE (q : Q) : eventProbability p (E q) ≤
      (n.choose q.val : ℝ) * ∑ k ∈ K, descriptorStateBound α n q.val k R := by
    have hq : q.val ≤ b := by have := Finset.mem_range.mp q.property; omega
    have hS (S : (Finset.univ : Finset (Fin n)).powersetCard q.val) :
        eventProbability p (⋃ k : K, fixedBoundaryDescriptorFailure S.val k.val R) ≤
          ∑ k ∈ K, descriptorStateBound α n q.val k R := by
      have hSc : S.val.card = q.val := (Finset.mem_powersetCard.mp S.property).2
      have hkbound (k : K) : eventProbability p (fixedBoundaryDescriptorFailure S.val k.val R) ≤
          descriptorStateBound α n q.val k.val R := by
        have hk := Finset.mem_Icc.mp k.property
        have hkb : k.val * R ≤ n - S.val.card := by
          calc
            _ ≤ r * R := Nat.mul_le_mul_right R hk.2
            _ = R * r := Nat.mul_comm _ _
            _ ≤ n - b := hbudget
            _ ≤ n - S.val.card := Nat.sub_le_sub_left (by omega : S.val.card ≤ b) n
        simpa only [descriptorStateBound, hSc] using
          fixed_boundary_descriptor_bound S.val hα hαhalf hk.1 hR hkb p hp
      calc
        _ ≤ ∑ k : K, eventProbability p (fixedBoundaryDescriptorFailure S.val k.val R) :=
          measureReal_iUnion_fintype_le _
        _ ≤ ∑ k : K, descriptorStateBound α n q.val k.val R :=
          Finset.sum_le_sum (fun k _ => hkbound k)
        _ = _ := by
          simp only [Finset.univ_eq_attach]
          exact Finset.sum_attach K (fun k => descriptorStateBound α n q.val k R)
    calc
      _ ≤ ∑ S : (Finset.univ : Finset (Fin n)).powersetCard q.val,
          eventProbability p (⋃ k : K, fixedBoundaryDescriptorFailure S.val k.val R) :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _S : (Finset.univ : Finset (Fin n)).powersetCard q.val,
          ∑ k ∈ K, descriptorStateBound α n q.val k R := Finset.sum_le_sum (fun S _ => hS S)
      _ = _ := by simp [Finset.card_powersetCard]
  calc
    _ ≤ eventProbability p (⋃ q : Q, E q) := measureReal_mono hsub
    _ ≤ ∑ q : Q, eventProbability p (E q) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ q : Q, (n.choose q.val : ℝ) * ∑ k ∈ K, descriptorStateBound α n q.val k R :=
      Finset.sum_le_sum (fun q _ => hE q)
    _ = descriptorBound α n r R b := by
      simp only [descriptorBound, descriptorStateBound, Q, K, Finset.univ_eq_attach]
      exact Finset.sum_attach (Finset.range (b + 1))
        (fun s => (n.choose s : ℝ) * ∑ k ∈ Finset.Icc 1 r, descriptorStateBound α n s k R)

end AdaptiveOrthogonalRigidity
