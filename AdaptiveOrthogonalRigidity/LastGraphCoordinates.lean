import AdaptiveOrthogonalRigidity.FieldGraphAlgebra

open Matrix
open scoped BigOperators Classical

namespace AdaptiveOrthogonalRigidity

/-- Polynomial evaluation preserves an intertwining linear map. -/
theorem linearMap_aeval_intertwine {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : V →ₗ[K] W) (A : Module.End K V) (B : Module.End K W)
    (h : ∀ v, e (A v) = B (e v)) (q : Polynomial K) (v : V) :
    e ((Polynomial.aeval A q) v) = (Polynomial.aeval B q) (e v) := by
  have hp (k : ℕ) : e ((A ^ k) v) = (B ^ k) (e v) := by
    induction k with
    | zero => simp
    | succ k ih => simp only [pow_succ', Module.End.mul_apply, h, ih]
  simp only [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, hp]

def lastCoordinates (K : Type*) [Field K] (n : ℕ) :
    (Fin (n + 1) → K) ≃ₗ[K] ((Fin n → K) × K) :=
  (LinearEquiv.funCongrLeft K K finSuccEquivLast.symm).trans (optionCoordinates K (Fin n))

theorem lastCoordinates_apply {K : Type*} [Field K] (n : ℕ) (v : Fin (n + 1) → K) :
    lastCoordinates K n v = (fun i => v i.castSucc, v (Fin.last n)) := by
  simp [lastCoordinates, optionCoordinates, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply]

theorem lastCoordinates_fieldGraph {K : Type*} [Field K] (n : ℕ)
    (diag : Fin (n + 1) → K) (ω : GraphSample (n + 1)) (v : Fin (n + 1) → K) :
    lastCoordinates K n ((fieldGraphMatrix K (n + 1) diag ω).mulVec v) =
      symmetricBorderMap (fieldGraphMatrix K n (fun i => diag i.castSucc) (graphDropLast ω))
        (boolVector (graphLastStar ω)) (diag (Fin.last n)) (lastCoordinates K n v) := by
  let M := borderMatrix (fieldGraphMatrix K n (fun i => diag i.castSucc) (graphDropLast ω))
    (boolVector (graphLastStar ω)) (diag (Fin.last n))
  have heq : ((M.submatrix finSuccEquivLast finSuccEquivLast).mulVec v) ∘ finSuccEquivLast.symm =
      M.mulVec (v ∘ finSuccEquivLast.symm) := by
    rw [Matrix.submatrix_mulVec_equiv]
    funext i
    simp
  change optionCoordinates K (Fin n)
    (((M.submatrix finSuccEquivLast finSuccEquivLast).mulVec v) ∘ finSuccEquivLast.symm) = _
  rw [heq]
  exact borderMatrix_mulVec_coordinates _ _ _ _

theorem lastCoordinates_fieldGraph_aeval {K : Type*} [Field K] (n : ℕ)
    (diag : Fin (n + 1) → K) (ω : GraphSample (n + 1)) (q : Polynomial K) (v : Fin (n + 1) → K) :
    lastCoordinates K n ((Polynomial.aeval (fieldGraphMatrix K (n + 1) diag ω) q).mulVec v) =
      (Polynomial.aeval
        (symmetricBorderMap (fieldGraphMatrix K n (fun i => diag i.castSucc) (graphDropLast ω))
          (boolVector (graphLastStar ω)) (diag (Fin.last n))) q) (lastCoordinates K n v) := by
  change lastCoordinates K n ((Polynomial.aeval (fieldGraphMatrix K (n + 1) diag ω) q).mulVecLin v) = _
  rw [matrix_mulVecLin_aeval]
  exact linearMap_aeval_intertwine (lastCoordinates K n).toLinearMap _ _
    (lastCoordinates_fieldGraph n diag ω) q v

end AdaptiveOrthogonalRigidity
