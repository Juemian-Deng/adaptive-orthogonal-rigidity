import AdaptiveOrthogonalRigidity.DescriptorColumnSpace
import AdaptiveOrthogonalRigidity.CoordinateAlgebra
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# One-step joint-output regular descriptor reduction

Equation columns, rather than output columns, are selected. Singular leading
matrices E are allowed throughout. Rank loss is proved from the actual restricted
dynamic-input rank, with all retained outputs controlled simultaneously.
-/

open Matrix
open scoped BigOperators Classical
noncomputable section
namespace AdaptiveOrthogonalRigidity

/-- The original-field embedding factors through constant polynomials. -/
theorem descriptor_ratFunc_C {K : Type*} [Field K] (a : K) :
    algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a) = algebraMap K (RatFunc K) a := by
  rw [Polynomial.C_eq_algebraMap]
  exact (IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K) a).symm

/-- The regular polynomial pencil has nonzero determinant over the rational function field. -/
theorem regularPencil_ratFunc_det {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {E M : Matrix ι ι K} (hreg : regularPencil E M) :
    ((descriptorPencil E M).map (algebraMap (Polynomial K) (RatFunc K))).det ≠ 0 := by
  have heq := (algebraMap (Polynomial K) (RatFunc K)).map_det (descriptorPencil E M)
  change algebraMap (Polynomial K) (RatFunc K) (descriptorPencil E M).det =
    ((descriptorPencil E M).map (algebraMap (Polynomial K) (RatFunc K))).det at heq
  rw [← heq]
  exact fun h => hreg ((RatFunc.algebraMap_injective K) (by simpa using h))

/-- Scalar extension keeps the same affine pencil, with no inversion of E. -/
theorem descriptorPencil_map_ratFunc {K ι : Type*} [Field K] (E M : Matrix ι ι K) :
    (descriptorPencil E M).map (algebraMap (Polynomial K) (RatFunc K)) =
      algebraMap (Polynomial K) (RatFunc K) Polynomial.X • E.map (algebraMap K (RatFunc K)) -
        M.map (algebraMap K (RatFunc K)) := by
  apply Matrix.ext
  intro i j
  simp only [descriptorPencil, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, map_sub, map_mul, descriptor_ratFunc_C]

/-- A projection with an identity actual-column submatrix has full row rank
also after extending coefficients. -/
theorem descriptor_projection_map_rank {K L ι : Type*} [Field K] [Field L]
    [Fintype ι] {r : ℕ} (c : K →+* L) (P : Matrix (Fin r) ι K)
    (f : Fin r ↪ ι) (hf : P.submatrix id f = 1) : (P.map c).rank = r := by
  have hsub : (P.map c).submatrix id f = 1 := by
    rw [Matrix.submatrix_map, hf]
    exact Matrix.map_one _ (map_zero c) (map_one c)
  apply Nat.le_antisymm (by simpa using (P.map c).rank_le_card_height)
  have hle := (P.map c).rank_submatrix_le id f
  simpa only [hsub, Matrix.rank_one, Fintype.card_fin] using hle

/-- Choose genuine original equation columns giving a regular reduced square pencil. -/
theorem regularPencil_select_equation_columns {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {r : ℕ}
    (E M : Matrix ι ι K) (hreg : regularPencil E M)
    (P : Matrix (Fin r) ι K) (f : Fin r ↪ ι) (hf : P.submatrix id f = 1) :
    ∃ g : Fin r ↪ ι, regularPencil ((P * E).submatrix id g) ((P * M).submatrix id g) := by
  let c := algebraMap K (RatFunc K)
  let t := algebraMap (Polynomial K) (RatFunc K)
  let S := (descriptorPencil E M).map t
  let A := P.map c * S
  have hS : S.det ≠ 0 := regularPencil_ratFunc_det hreg
  have hrank : A.rank = r := by
    rw [show A = P.map c * S from rfl, Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hS]
    exact descriptor_projection_map_rank c P f hf
  have hspan : Submodule.span (RatFunc K) (Set.range A.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_cols, hrank, Module.finrank_fin_fun]
  have hdim : Module.finrank (RatFunc K) (Fin r → RatFunc K) = r :=
    Module.finrank_fin_fun (RatFunc K)
  have hex := spanning_family_pivots A.col hspan
  rw [hdim] at hex
  obtain ⟨g, hg⟩ := hex
  have hg' : LinearIndependent (RatFunc K) (A.submatrix id g).col := hg
  have hdet : (A.submatrix id g).det ≠ 0 := by
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_cols_iff_isUnit.mp hg'))
  have hA : A = t Polynomial.X • (P * E).map c - (P * M).map c := by
    dsimp [A, S]
    rw [descriptorPencil_map_ratFunc, Matrix.mul_sub, Matrix.mul_smul,
      ← Matrix.map_mul, ← Matrix.map_mul]
  have hmap : (descriptorPencil ((P * E).submatrix id g) ((P * M).submatrix id g)).map t =
      A.submatrix id g := by
    rw [descriptorPencil_map_ratFunc, hA]
    simp only [Matrix.submatrix_sub, Matrix.submatrix_smul]
    rfl
  refine ⟨g, ?_⟩
  intro hz
  apply hdet
  rw [← hmap]
  have heq := t.map_det (descriptorPencil ((P * E).submatrix id g) ((P * M).submatrix id g))
  exact heq.symm.trans (by rw [hz, map_zero])


/-- The projection identities prove the state bound from the actual dynamic rank.
The argument is polynomial/rational-function algebra, without assuming E invertible. -/
theorem regular_descriptor_projected_rank_le {K ν ι : Type*} [Field K]
    [Fintype ν] [Fintype ι] [DecidableEq ι] {r : ℕ}
    (C : Matrix ν ν K) (U : Matrix ν ι K) (E M : Matrix ι ι K)
    (P : Matrix (Fin r) ι K) (Q : Matrix (Fin r) ν K)
    (f : Fin r ↪ ι) (hf : P.submatrix id f = 1) (hreg : regularPencil E M)
    (hE : Q * U = P * E) (hM : Q * C * U = P * M) : r ≤ U.rank := by
  let c := algebraMap K (RatFunc K)
  let t := algebraMap (Polynomial K) (RatFunc K)
  let S := (descriptorPencil E M).map t
  have hS : S.det ≠ 0 := regularPencil_ratFunc_det hreg
  have hr : (P.map c * S).rank = r := by
    rw [Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hS]
    exact descriptor_projection_map_rank c P f hf
  have hfactor : P.map c * S =
      (t Polynomial.X • Q.map c - Q.map c * C.map c) * U.map c := by
    calc
      _ = t Polynomial.X • (P * E).map c - (P * M).map c := by
        dsimp [S]
        rw [descriptorPencil_map_ratFunc, Matrix.mul_sub, Matrix.mul_smul,
          ← Matrix.map_mul, ← Matrix.map_mul]
      _ = t Polynomial.X • (Q * U).map c - (Q * C * U).map c := by rw [hE, hM]
      _ = _ := by rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
        Matrix.sub_mul, Matrix.smul_mul]
  calc
    r = (P.map c * S).rank := hr.symm
    _ = ((t Polynomial.X • Q.map c - Q.map c * C.map c) * U.map c).rank := congrArg Matrix.rank hfactor
    _ ≤ (U.map c).rank := Matrix.rank_mul_le_right _ _
    _ ≤ U.rank := descriptor_rank_map_le c U

/-- Restrict actual equation columns of a matrix product. -/
theorem descriptor_mul_restrict_columns {K ν ι κ τ : Type*} [Semiring K] [Fintype ι]
    (A : Matrix ν ι K) (B : Matrix ι κ K) (f : τ → κ) :
    (A * B).submatrix id f = A * B.submatrix id f := by
  simpa only [Matrix.submatrix_id_id] using
    Matrix.submatrix_mul A B id id f Function.bijective_id

/-- Joint-output reduction in a fixed ambient row space with an independent
input family. State and equation selectors are genuine original column injections. -/
theorem regular_descriptor_reduce_core {K ν ι π ο : Type*} [Field K]
    [Fintype ν] [Fintype ι] [Fintype π] [DecidableEq ν] [DecidableEq ι] [DecidableEq π]
    (C : Matrix ν ν K) (X : Matrix ν ι K) (V : Matrix ν π K)
    (E M : Matrix ι ι K) (F B : Matrix π ι K) (L : Matrix ι ο K) (G : Matrix π ο K)
    (hV : LinearIndependent K V.col) (hreg : regularPencil E M)
    (hact : C * (X * E + V * F) = X * M + V * B) :
    ∃ (r : ℕ) (f g : Fin r ↪ ι) (P : Matrix (Fin r) ι K) (H : Matrix π ι K),
      r ≤ (X * E + V * F).rank ∧
      LinearIndependent K (Matrix.fromCols (X.submatrix id f) V).col ∧
      regularPencil ((P * E).submatrix id g) ((P * M).submatrix id g) ∧
      X.submatrix id f * (P * E).submatrix id g + V * (H * E + F).submatrix id g =
        (X * E + V * F).submatrix id g ∧
      C * (X.submatrix id f * (P * E).submatrix id g + V * (H * E + F).submatrix id g) =
        X.submatrix id f * (P * M).submatrix id g + V * (H * M + B).submatrix id g ∧
      X * L + V * G = X.submatrix id f * (P * L) + V * (H * L + G) := by
  obtain ⟨r, f, P, H, Q, hli, hX, hQXf, hQV, hQX, hPf⟩ := descriptor_state_coordinates X V hV
  have hE : Q * (X * E + V * F) = P * E := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQX, hQV,
      Matrix.zero_mul, add_zero]
  have hM : Q * C * (X * E + V * F) = P * M := by
    rw [Matrix.mul_assoc, hact, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hQX, hQV, Matrix.zero_mul, add_zero]
  have hr := regular_descriptor_projected_rank_le C (X * E + V * F) E M P Q f hPf hreg hE hM
  obtain ⟨g, hg⟩ := regularPencil_select_equation_columns E M hreg P f hPf
  have hdecomp (A : Matrix ι ι K) (D : Matrix π ι K) :
      X * A + V * D = X.submatrix id f * (P * A) + V * (H * A + D) := by
    calc
      _ = (X.submatrix id f * P + V * H) * A + V * D := congrArg (fun Y => Y * A + V * D) hX
      _ = _ := by simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, add_assoc]
  have hcols (A : Matrix ι ι K) (D : Matrix π ι K) :
      (X * A + V * D).submatrix id g =
        X.submatrix id f * (P * A).submatrix id g + V * (H * A + D).submatrix id g := by
    rw [hdecomp]
    simp only [Matrix.submatrix_add, descriptor_mul_restrict_columns]
    rfl
  refine ⟨r, f, g, P, H, hr, hli, hg, (hcols E F).symm, ?_, ?_⟩
  · rw [← hcols, ← descriptor_mul_restrict_columns, hact, hcols]
  · calc
      _ = (X.submatrix id f * P + V * H) * L + V * G := congrArg (fun Y => Y * L + V * G) hX
      _ = _ := by simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, add_assoc]


/-- Restrict original rows of a matrix product. -/
theorem descriptor_restrict_rows_mul {K ν ι κ τ : Type*} [Semiring K] [Fintype ι]
    (A : Matrix ν ι K) (B : Matrix ι κ K) (f : τ → ν) :
    (A * B).submatrix f id = A.submatrix f id * B := by
  simpa only [Matrix.submatrix_id_id] using
    Matrix.submatrix_mul A B f id id Function.bijective_id

/-- The exact principal-plus-cross-column restriction of an action equation. -/
theorem descriptor_action_row_split {K ν ι : Type*} [Semiring K]
    [Fintype ν] [DecidableEq ν] (C : Matrix ν ν K) (U : Matrix ν ι K) (H : Finset ν) :
    (C * U).submatrix (fun i : H => i.val) id =
      C.submatrix (fun i : H => i.val) (fun i : H => i.val) *
        U.submatrix (fun i : H => i.val) id +
      C.submatrix (fun i : H => i.val) (fun i : ↑Hᶜ => i.val) *
        U.submatrix (fun i : ↑Hᶜ => i.val) id := by
  apply Matrix.ext
  intro i j
  exact congrFun (coordinateRestriction_mulVec C H (U.col j)) i

/-- One-step deletion with any independent new input family containing all old
restricted input and actual newly exposed cross columns. All output columns survive.
The returned g selects actual original action-equation columns, as certified by
its equality with the selected columns of the original restricted dynamic input. -/
theorem regular_descriptor_delete_rows {K ν ι π π' ο : Type*} [Field K]
    [Fintype ν] [Fintype ι] [Fintype π] [Fintype π']
    [DecidableEq ν] [DecidableEq ι] [DecidableEq π] [DecidableEq π']
    (C : Matrix ν ν K) (X : Matrix ν ι K) (V : Matrix ν π K)
    (E M : Matrix ι ι K) (F B : Matrix π ι K) (L : Matrix ι ο K) (G : Matrix π ο K)
    (hreg : regularPencil E M) (hact : C * (X * E + V * F) = X * M + V * B)
    (H : Finset ν) (Vbar : Matrix H π' K) (hVbar : LinearIndependent K Vbar.col)
    (hV : ∀ j, (V.submatrix (fun i : H => i.val) id).col j ∈ Vbar.mulVecLin.range)
    (hcross : ∀ j : ↑Hᶜ,
      (C.submatrix (fun i : H => i.val) (fun i : ↑Hᶜ => i.val)).col j ∈ Vbar.mulVecLin.range) :
    ∃ (r : ℕ) (g : Fin r ↪ ι) (X' : Matrix H (Fin r) K)
      (E' M' : Matrix (Fin r) (Fin r) K) (F' B' : Matrix π' (Fin r) K)
      (L' : Matrix (Fin r) ο K) (G' : Matrix π' ο K),
      r ≤ ((X * E + V * F).submatrix (fun i : H => i.val) id).rank ∧
      LinearIndependent K (Matrix.fromCols X' Vbar).col ∧ regularPencil E' M' ∧
      X' * E' + Vbar * F' =
        ((X * E + V * F).submatrix (fun i : H => i.val) id).submatrix id g ∧
      C.submatrix (fun i : H => i.val) (fun i : H => i.val) * (X' * E' + Vbar * F') =
        X' * M' + Vbar * B' ∧
      (X * L + V * G).submatrix (fun i : H => i.val) id = X' * L' + Vbar * G' ∧
      ∃ P : Matrix (Fin r) ι K, E' = (P * E).submatrix id g ∧ M' = (P * M).submatrix id g := by
  let XH := X.submatrix (fun i : H => i.val) id
  let CH := C.submatrix (fun i : H => i.val) (fun i : H => i.val)
  let CT := C.submatrix (fun i : H => i.val) (fun i : ↑Hᶜ => i.val)
  let VH := V.submatrix (fun i : H => i.val) id
  let U := X * E + V * F
  let UH := U.submatrix (fun i : H => i.val) id
  let UT := U.submatrix (fun i : ↑Hᶜ => i.val) id
  obtain ⟨KV, hKV⟩ := descriptor_exists_right_factor Vbar VH hV
  obtain ⟨KC, hKC⟩ := descriptor_exists_right_factor Vbar CT hcross
  let Fb := KV * F
  let Bb := KV * B - KC * UT
  let Gb := KV * G
  have hUH : UH = XH * E + Vbar * Fb := by
    change (X * E + V * F).submatrix (fun i : H => i.val) id = _
    simp only [Matrix.submatrix_add]
    change XH * E + VH * F = _
    rw [hKV, Matrix.mul_assoc]
  have hrestricted : CH * UH = XH * M + Vbar * Bb := by
    have he := congrArg (fun W : Matrix ν ι K => W.submatrix (fun i : H => i.val) id) hact
    rw [descriptor_action_row_split] at he
    simp only [Matrix.submatrix_add] at he
    change CH * UH + CT * UT = XH * M + VH * B at he
    rw [hKV, hKC, Matrix.mul_assoc, Matrix.mul_assoc] at he
    calc
      CH * UH = (XH * M + Vbar * (KV * B)) - Vbar * (KC * UT) := eq_sub_iff_add_eq.mpr he
      _ = _ := by dsimp [Bb]; rw [Matrix.mul_sub]; abel
  have hout : (X * L + V * G).submatrix (fun i : H => i.val) id = XH * L + Vbar * Gb := by
    simp only [Matrix.submatrix_add]
    change XH * L + VH * G = _
    rw [hKV, Matrix.mul_assoc]
  obtain ⟨r, f, g, P, J, hr, hli, hregular, hselected, ha, ho⟩ :=
    regular_descriptor_reduce_core CH XH Vbar E M Fb Bb L Gb hVbar hreg (hUH ▸ hrestricted)
  refine ⟨r, g, XH.submatrix id f, (P * E).submatrix id g, (P * M).submatrix id g,
    (J * E + Fb).submatrix id g, (J * M + Bb).submatrix id g,
    P * L, J * L + Gb, ?_, hli, hregular, ?_, ha, ?_, P, rfl, rfl⟩
  · change r ≤ UH.rank
    rw [hUH]
    exact hr
  · exact hselected.trans (congrArg (fun W : Matrix H ι K => W.submatrix id g) hUH.symm)
  · exact hout.trans ho

/-- Joint-output form with the user's complete supplied output matrix Z. -/
theorem regular_descriptor_joint_output_one_step {K ν ι π π' ο : Type*} [Field K]
    [Fintype ν] [Fintype ι] [Fintype π] [Fintype π']
    [DecidableEq ν] [DecidableEq ι] [DecidableEq π] [DecidableEq π']
    (C : Matrix ν ν K) (X : Matrix ν ι K) (V : Matrix ν π K)
    (E M : Matrix ι ι K) (F B : Matrix π ι K)
    (Z : Matrix ν ο K) (L : Matrix ι ο K) (G : Matrix π ο K)
    (hreg : regularPencil E M) (hact : C * (X * E + V * F) = X * M + V * B)
    (hout : Z = X * L + V * G)
    (H : Finset ν) (Vbar : Matrix H π' K) (hVbar : LinearIndependent K Vbar.col)
    (hV : ∀ j, (V.submatrix (fun i : H => i.val) id).col j ∈ Vbar.mulVecLin.range)
    (hcross : ∀ j : ↑Hᶜ,
      (C.submatrix (fun i : H => i.val) (fun i : ↑Hᶜ => i.val)).col j ∈ Vbar.mulVecLin.range) :
    ∃ (r : ℕ) (g : Fin r ↪ ι) (X' : Matrix H (Fin r) K)
      (E' M' : Matrix (Fin r) (Fin r) K) (F' B' : Matrix π' (Fin r) K)
      (L' : Matrix (Fin r) ο K) (G' : Matrix π' ο K),
      r ≤ ((X * E + V * F).submatrix (fun i : H => i.val) id).rank ∧
      LinearIndependent K (Matrix.fromCols X' Vbar).col ∧ regularPencil E' M' ∧
      X' * E' + Vbar * F' =
        ((X * E + V * F).submatrix (fun i : H => i.val) id).submatrix id g ∧
      C.submatrix (fun i : H => i.val) (fun i : H => i.val) * (X' * E' + Vbar * F') =
        X' * M' + Vbar * B' ∧
      Z.submatrix (fun i : H => i.val) id = X' * L' + Vbar * G' ∧
      ∃ P : Matrix (Fin r) ι K, E' = (P * E).submatrix id g ∧ M' = (P * M).submatrix id g := by
  rw [hout]
  exact regular_descriptor_delete_rows C X V E M F B L G hreg hact H Vbar hVbar hV hcross

/-- The rank bound in the one-step theorem gives at least the actual lost
original state dimension. This formulation needs no subtraction side condition. -/
theorem descriptor_state_loss_of_rank_bound {K ν ι : Type*} [Field K]
    [Fintype ν] [Fintype ι] {r : ℕ} (U : Matrix ν ι K) (hr : r ≤ U.rank) :
    Fintype.card ι - U.rank ≤ Fintype.card ι - r :=
  Nat.sub_le_sub_left hr _

/-- If the restricted dynamic rank is k-j, with j in the original state range,
the selected regular descriptor loses at least j states. -/
theorem descriptor_state_loss_of_restricted_rank {K ν : Type*} [Field K]
    [Fintype ν] {k j r : ℕ} (U : Matrix ν (Fin k) K) (hj : j ≤ k)
    (hU : U.rank = k - j) (hr : r ≤ U.rank) : j ≤ k - r ∧ r + j ≤ k := by
  rw [hU] at hr
  omega

end AdaptiveOrthogonalRigidity
