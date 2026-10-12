import AdaptiveOrthogonalRigidity.FieldGraphMatrix
import AdaptiveOrthogonalRigidity.CorankPaths

open scoped Classical

namespace AdaptiveOrthogonalRigidity

noncomputable def fieldCorankPath (K : Type*) [Field K] :
    (n : ℕ) → (Fin n → K) → GraphSample n → ℕ → ℕ
  | 0, _, _, _ => 0
  | n + 1, diag, ω, k => if k = n + 1 then fieldGraphCorank K (n + 1) diag ω
      else fieldCorankPath K n (fun i => diag i.castSucc) (graphDropLast ω) k

theorem fieldGraphCorank_zero {K : Type*} [Field K] (diag : Fin 0 → K) (ω : GraphSample 0) :
    fieldGraphCorank K 0 diag ω = 0 := by
  have h := Submodule.finrank_le (fieldGraphMatrix K 0 diag ω).mulVecLin.ker
  simp only [Module.finrank_pi, Fintype.card_fin] at h
  exact Nat.eq_zero_of_le_zero h

theorem fieldCorankPath_top {K : Type*} [Field K] (n : ℕ) (diag : Fin n → K) (ω : GraphSample n) :
    fieldCorankPath K n diag ω n = fieldGraphCorank K n diag ω := by
  cases n with
  | zero => exact (fieldGraphCorank_zero diag ω).symm
  | succ n => simp [fieldCorankPath]

theorem fieldCorankPath_zero {K : Type*} [Field K] (n : ℕ) (diag : Fin n → K) (ω : GraphSample n) :
    fieldCorankPath K n diag ω 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [fieldCorankPath, ite_eq_right (show (0 : ℕ) ≠ n + 1 by omega)]
    exact ih _ _

theorem fieldCorankPath_succ_lower {K : Type*} [Field K] (n k : ℕ) (hk : k ≤ n)
    (diag : Fin (n + 1) → K) (ω : GraphSample (n + 1)) :
    fieldCorankPath K (n + 1) diag ω k =
      fieldCorankPath K n (fun i => diag i.castSucc) (graphDropLast ω) k := by
  exact ite_eq_right (by omega)

theorem fieldCorankPath_growth {K : Type*} [Field K] (n : ℕ) (diag : Fin n → K) (ω : GraphSample n) :
    ∀ i < n, fieldCorankPath K n diag ω (i + 1) ≤ fieldCorankPath K n diag ω i + 1 := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    by_cases hin : i < n
    · rw [fieldCorankPath_succ_lower n (i + 1) (by omega), fieldCorankPath_succ_lower n i (by omega)]
      exact ih _ _ i hin
    · have hei : i = n := by omega
      subst i
      rw [fieldCorankPath_succ_lower n n le_rfl, fieldCorankPath_top, fieldCorankPath_top,
        fieldGraphCorank_succ]
      exact symmetric_border_kernel_growth _ _ _

noncomputable def markedCorankEvent (K : Type*) [Field K] :
    (n : ℕ) → (Fin n → K) → ℕ → Finset ℕ → Set (GraphSample n)
  | 0, _, _, _ => Set.univ
  | n + 1, diag, a, S => {ω |
      graphDropLast ω ∈ markedCorankEvent K n (fun i => diag i.castSucc) a S ∧
      (n ∈ S → a ≤ fieldGraphCorank K n (fun i => diag i.castSucc) (graphDropLast ω) ∧
        fieldGraphCorank K n (fun i => diag i.castSucc) (graphDropLast ω) ≤
          fieldGraphCorank K (n + 1) diag ω)}

theorem markedCorankEvent_iff {K : Type*} [Field K] (n : ℕ) (diag : Fin n → K)
    (ω : GraphSample n) (a : ℕ) (S : Finset ℕ) :
    ω ∈ markedCorankEvent K n diag a S ↔
      ∀ i ∈ S, i < n → a ≤ fieldCorankPath K n diag ω i ∧
        fieldCorankPath K n diag ω i ≤ fieldCorankPath K n diag ω (i + 1) := by
  induction n with
  | zero => simp [markedCorankEvent]
  | succ n ih =>
    change (_ ∧ _) ↔ _
    rw [ih]
    constructor
    · rintro ⟨hpast, hlast⟩ i hi hin
      by_cases hsmall : i < n
      · rw [fieldCorankPath_succ_lower n i (by omega), fieldCorankPath_succ_lower n (i + 1) (by omega)]
        exact hpast i hi hsmall
      · have hieq : i = n := by omega
        subst i
        rw [fieldCorankPath_succ_lower n n le_rfl, fieldCorankPath_top, fieldCorankPath_top]
        exact hlast hi
    · intro h
      constructor
      · intro i hi hin
        have hh := h i hi (by omega)
        rw [fieldCorankPath_succ_lower n i (by omega), fieldCorankPath_succ_lower n (i + 1) (by omega)] at hh
        exact hh
      · intro hn
        have hh := h n hn (by omega)
        rw [fieldCorankPath_succ_lower n n le_rfl, fieldCorankPath_top, fieldCorankPath_top] at hh
        exact hh

end AdaptiveOrthogonalRigidity
