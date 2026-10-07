/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Existence.FullOp
public import EllipticPdes.Form.DivForm
public import EllipticPdes.Form.GeneralForm
public import EllipticPdes.Sobolev.GraphEuclidean
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Coordinate operators as divergence-form operators

A coordinate operator `Sobolev.FullEllipticOp d` has matrix, drift and potential given by
coordinates. `FullEllipticOp.ofCoord` reads it as a `DivForm.FullEllipticOp` for the Lebesgue
measure on `EuclideanSpace ℝ (Fin d)`, and the forms correspond under `H1Graph.h01Equiv`:

* `EllipticCoeff.form_h01Equiv`: the principal forms agree.
* `FullEllipticOp.lowerForm_h01Equiv`, `FullEllipticOp.form_h01Equiv`: the lower-order and the
  full forms agree.
* `zerothForm_h01Equiv`: the `L²` pairings agree.
* `FullEllipticOp.gardingγ_ofCoord`: the Gårding constants agree.

These let every theorem about `DivForm.FullEllipticOp` apply to the coordinate operators.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes

namespace DivForm

variable {d : ℕ}

/-- The coordinate field `x ↦ (aᵢⱼ x)` as a matrix, transposed so that `(a ξ)ⱼ = ∑ᵢ aᵢⱼ ξᵢ`. -/
abbrev coordMatrix (A : Sobolev.EllipticCoeff d) (x : EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => A.a x j i

/-- A matrix with entries bounded by `Λ` acts on `ℝᵈ` with operator norm at most `d Λ`. -/
lemma norm_toEuclideanCLM_le {M : Matrix (Fin d) (Fin d) ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hM : ∀ i j, |M i j| ≤ Λ) : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖ ≤ d * Λ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ξ => ?_
  have hrow : ∀ j, (∑ i, M j i * ξ i) ^ 2 ≤ d * Λ ^ 2 * ‖ξ‖ ^ 2 := fun j => by
    refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
    rw [EuclideanSpace.real_norm_sq_eq]
    gcongr
    calc ∑ i, M j i ^ 2 ≤ ∑ _i : Fin d, Λ ^ 2 :=
          Finset.sum_le_sum fun i _ => sq_le_sq' (abs_le.1 (hM j i)).1 (abs_le.1 (hM j i)).2
      _ = d * Λ ^ 2 := by simp
  have hsq : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M ξ‖ ^ 2 ≤ (d * Λ * ‖ξ‖) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ j, (Matrix.toEuclideanCLM (𝕜 := ℝ) M ξ) j ^ 2 ≤ ∑ _j : Fin d, d * Λ ^ 2 * ‖ξ‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => by simpa [Matrix.mulVec, dotProduct] using hrow j
      _ = (d * Λ * ‖ξ‖) ^ 2 := by simp; ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq

/-- The pairing against the matrix field is the coordinate quadratic expression. -/
lemma inner_coordMatrix (A : Sobolev.EllipticCoeff d) (x ξ η : EuclideanSpace ℝ (Fin d)) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (coordMatrix A x) ξ, η⟫ =
      ∑ i, ∑ j, A.a x i j * ξ i * η j := by
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, coordMatrix, Matrix.of_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The coordinate coefficient matrix read as a field of endomorphisms of `ℝᵈ`, with
`(a ξ)ⱼ = ∑ᵢ aᵢⱼ ξᵢ`. -/
def EllipticCoeff.ofCoord (A : Sobolev.EllipticCoeff d) :
    EllipticCoeff (volume : Measure (EuclideanSpace ℝ (Fin d))) where
  a x := Matrix.toEuclideanCLM (𝕜 := ℝ) (coordMatrix A x)
  lam := A.lam
  Λ := d * A.Λ
  lam_pos := A.lam_pos
  Λ_nonneg := by have := A.Λ_nonneg; positivity
  aestronglyMeasurable := by
    have hg : Continuous
        (fun F : Fin d → Fin d → ℝ => Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.of F)) :=
      LinearMap.continuous_of_finiteDimensional
        ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).toAlgEquiv.toLinearMap ∘ₗ
          (Matrix.ofLinearEquiv ℝ).toLinearMap)
    have hF : Measurable fun x : EuclideanSpace ℝ (Fin d) => fun i j => A.a x j i :=
      Measurable.of_eval fun i => Measurable.of_eval fun j => A.measurable j i
    exact hg.comp_aestronglyMeasurable hF.aestronglyMeasurable
  norm_le := by
    filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 (A.bdd i)] with x hx
    exact norm_toEuclideanCLM_le A.Λ_nonneg fun i j => hx j i
  coercive := by
    filter_upwards [A.elliptic] with x hx ξ
    rw [EuclideanSpace.real_norm_sq_eq, inner_coordMatrix]
    simpa using hx ξ.ofLp

/-- The coordinate operator as a divergence-form operator for Lebesgue measure. -/
def FullEllipticOp.ofCoord (Op : Sobolev.FullEllipticOp d) :
    FullEllipticOp (volume : Measure (EuclideanSpace ℝ (Fin d))) where
  toEllipticCoeff := EllipticCoeff.ofCoord Op.toEllipticCoeff
  b x := WithLp.toLp 2 (Op.b x)
  c := Op.c
  Bsup := Real.sqrt d * Op.Bsup
  Csup := Op.Csup
  Bsup_nonneg := by have := Op.Bsup_nonneg; positivity
  Csup_nonneg := Op.Csup_nonneg
  b_aestronglyMeasurable :=
    ((WithLp.measurable_toLp 2 (Fin d → ℝ)).comp
      (Measurable.of_eval Op.b_meas)).aestronglyMeasurable
  c_aestronglyMeasurable := Op.c_meas.aestronglyMeasurable
  norm_b_le := by
    filter_upwards [ae_all_iff.2 Op.b_bdd] with x hx
    have h : ‖(WithLp.toLp 2 (Op.b x) : EuclideanSpace ℝ (Fin d))‖ ^ 2 ≤
        (Real.sqrt d * Op.Bsup) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
      calc ∑ i, Op.b x i ^ 2 ≤ ∑ _i : Fin d, Op.Bsup ^ 2 :=
            Finset.sum_le_sum fun i _ => sq_le_sq' (abs_le.1 (hx i)).1 (abs_le.1 (hx i)).2
        _ = d * Op.Bsup ^ 2 := by simp
    exact (sq_le_sq₀ (norm_nonneg _) (by have := Op.Bsup_nonneg; positivity)).1 h
  abs_c_le := Op.c_bdd

/-- The coefficient of `EllipticCoeff.ofCoord` is the matrix field. -/
@[simp] lemma EllipticCoeff.ofCoord_a (A : Sobolev.EllipticCoeff d)
    (x : EuclideanSpace ℝ (Fin d)) :
    (EllipticCoeff.ofCoord A).a x = Matrix.toEuclideanCLM (𝕜 := ℝ) (coordMatrix A x) := rfl

/-- The principal part of `FullEllipticOp.ofCoord` is `EllipticCoeff.ofCoord`. -/
lemma FullEllipticOp.ofCoord_toEllipticCoeff (Op : Sobolev.FullEllipticOp d) :
    (FullEllipticOp.ofCoord Op).toEllipticCoeff = EllipticCoeff.ofCoord Op.toEllipticCoeff := rfl

/-- The pairing against `ofCoord` is the coordinate quadratic expression. -/
lemma EllipticCoeff.inner_ofCoord_a (A : Sobolev.EllipticCoeff d)
    (x ξ η : EuclideanSpace ℝ (Fin d)) :
    ⟪(EllipticCoeff.ofCoord A).a x ξ, η⟫ = ∑ i, ∑ j, A.a x i j * ξ i * η j :=
  inner_coordMatrix A x ξ η

/-- The pairing of the drift of `ofCoord` is the coordinate sum. -/
lemma FullEllipticOp.inner_ofCoord_b (Op : Sobolev.FullEllipticOp d)
    (x g : EuclideanSpace ℝ (Fin d)) :
    ⟪(FullEllipticOp.ofCoord Op).b x, g⟫ = ∑ i, Op.b x i * g i := by
  simp [FullEllipticOp.ofCoord, PiLp.inner_apply, mul_comm]

/-! ### Transport of the forms along `h01Equiv` -/

/-- The gradient of `h01Equiv U` has the coordinate partial derivatives of `U` as components. -/
lemma ae_gradL_h01Equiv (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : Sobolev.H01 Ω) :
    ∀ᵐ x ∂(volume.restrict Ω), ∀ i : Fin d,
      H1Graph.gradL (H1Graph.h01Equiv Ω U : H1Graph volume Ω) x i =
        (U : Sobolev.H1amb Ω) i.succ x := by
  refine ae_all_iff.2 fun i => ?_
  have h := H1Graph.h1Equiv_apply_succ Ω (H1Graph.h01Equiv Ω U : H1Graph volume Ω) i
  rw [H1Graph.h1Equiv_h01Equiv] at h
  filter_upwards [ContinuousLinearMap.coeFn_compLp
    (EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (H1Graph.gradL (H1Graph.h01Equiv Ω U : H1Graph volume Ω))] with x hx
  rw [h, hx]
  rfl

/-- The function part of `h01Equiv U` has the coordinate `0` of `U` as representative. -/
lemma ae_fnL_h01Equiv (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : Sobolev.H01 Ω) :
    H1Graph.fnL (H1Graph.h01Equiv Ω U : H1Graph volume Ω) =ᵐ[volume.restrict Ω]
      (U : Sobolev.H1amb Ω) 0 := by
  rw [H1Graph.fnL_h01Equiv]

/-- The principal forms correspond under `h01Equiv`. -/
theorem EllipticCoeff.form_h01Equiv (A : Sobolev.EllipticCoeff d)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : Sobolev.H01 Ω) :
    (EllipticCoeff.ofCoord A).form Ω (H1Graph.h01Equiv Ω U : H1Graph volume Ω)
        (H1Graph.h01Equiv Ω V : H1Graph volume Ω) = A.bilin Ω U V := by
  rw [EllipticCoeff.form_eq_integral, Sobolev.EllipticCoeff.bilin_apply]
  have key : ∫ x in Ω, (⟪(EllipticCoeff.ofCoord A).a x
        (H1Graph.gradL (H1Graph.h01Equiv Ω U : H1Graph volume Ω) x),
        H1Graph.gradL (H1Graph.h01Equiv Ω V : H1Graph volume Ω) x⟫) =
      ∫ x in Ω, (∑ i : Fin d, ∑ j : Fin d,
        A.a x i j * ((U : Sobolev.H1amb Ω) i.succ x : ℝ) *
          ((V : Sobolev.H1amb Ω) j.succ x : ℝ)) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_gradL_h01Equiv Ω U, ae_gradL_h01Equiv Ω V] with x hU hV
    rw [EllipticCoeff.inner_ofCoord_a]
    simp only [hU, hV]
  rw [key, integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => A.integrable_triple i j _ _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => A.integrable_triple i j _ _)]
  exact Finset.sum_congr rfl fun j _ => (A.inner_actL_eq i j _ _).symm

/-- The product of a bounded coefficient with two `L²` classes is integrable. -/
lemma integrable_mulCoeff {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume.restrict Ω), |f x| ≤ M) (g h : Sobolev.L2D Ω) :
    Integrable (fun x => f x * (g x : ℝ) * (h x : ℝ)) (volume.restrict Ω) :=
  (L2.integrable_mul (Sobolev.mulCoeffL hf hM g) h).congr (by
    filter_upwards [Sobolev.mulCoeffL_coeFn hf hM g] with x hx
    rw [hx])

/-- The lower-order forms correspond under `h01Equiv`. -/
theorem FullEllipticOp.lowerForm_h01Equiv (Op : Sobolev.FullEllipticOp d)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : Sobolev.H01 Ω) :
    (FullEllipticOp.ofCoord Op).lowerForm Ω (H1Graph.h01Equiv Ω U : H1Graph volume Ω)
        (H1Graph.h01Equiv Ω V : H1Graph volume Ω) = Op.lowerBilin Ω U V := by
  have hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), |Op.b x i| ≤ Op.Bsup :=
    fun i => ae_restrict_of_ae (Op.b_bdd i)
  have hc : ∀ᵐ x ∂(volume.restrict Ω), |Op.c x| ≤ Op.Csup := ae_restrict_of_ae Op.c_bdd
  rw [FullEllipticOp.lowerForm_eq_integral, Sobolev.FullEllipticOp.lowerBilin_apply]
  simp only [Sobolev.FullEllipticOp.bAct, Sobolev.FullEllipticOp.cAct,
    Sobolev.inner_mulCoeffL_eq]
  have key : ∫ x in Ω, (⟪(FullEllipticOp.ofCoord Op).b x,
        H1Graph.gradL (H1Graph.h01Equiv Ω U : H1Graph volume Ω) x⟫ *
        H1Graph.fnL (H1Graph.h01Equiv Ω V : H1Graph volume Ω) x +
      (FullEllipticOp.ofCoord Op).c x *
        H1Graph.fnL (H1Graph.h01Equiv Ω U : H1Graph volume Ω) x *
        H1Graph.fnL (H1Graph.h01Equiv Ω V : H1Graph volume Ω) x) =
      ∫ x in Ω, (∑ i : Fin d, Op.b x i * ((U : Sobolev.H1amb Ω) i.succ x : ℝ) *
          ((V : Sobolev.H1amb Ω) 0 x : ℝ) +
        Op.c x * ((U : Sobolev.H1amb Ω) 0 x : ℝ) * ((V : Sobolev.H1amb Ω) 0 x : ℝ)) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_gradL_h01Equiv Ω U, ae_fnL_h01Equiv Ω U, ae_fnL_h01Equiv Ω V]
      with x hU hfU hfV
    beta_reduce
    rw [FullEllipticOp.inner_ofCoord_b Op x]
    simp only [hU, hfU, hfV, Finset.sum_mul]
    rfl
  rw [key, integral_add (integrable_finsetSum _ fun i _ => integrable_mulCoeff (Op.b_meas i)
      (hb i) _ _) (integrable_mulCoeff Op.c_meas hc _ _),
    integral_finsetSum _ fun i _ => integrable_mulCoeff (Op.b_meas i) (hb i) _ _]

/-- The full forms correspond under `h01Equiv`. -/
theorem FullEllipticOp.form_h01Equiv (Op : Sobolev.FullEllipticOp d)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : Sobolev.H01 Ω) :
    (FullEllipticOp.ofCoord Op).formOn Ω (H1Graph.H01 volume Ω)
        (H1Graph.h01Equiv Ω U) (H1Graph.h01Equiv Ω V) = Op.fullBilin Ω U V := by
  rw [FullEllipticOp.formOn_apply, FullEllipticOp.form_apply,
    FullEllipticOp.ofCoord_toEllipticCoeff, EllipticCoeff.form_h01Equiv,
    FullEllipticOp.lowerForm_h01Equiv, Sobolev.FullEllipticOp.fullBilin_apply]

/-- The `L²` pairing of function parts corresponds to the zeroth-order form. -/
theorem zerothForm_h01Equiv (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : Sobolev.H01 Ω) :
    ⟪H1Graph.embL2 volume Ω (H1Graph.h01Equiv Ω U),
        H1Graph.embL2 volume Ω (H1Graph.h01Equiv Ω V)⟫ =
      Sobolev.FullEllipticOp.zerothForm Ω U V := by
  rw [H1Graph.embL2_h01Equiv, H1Graph.embL2_h01Equiv, Sobolev.FullEllipticOp.zerothForm_apply]

/-- The Gårding constants of a coordinate operator and its divergence-form reading agree. -/
theorem FullEllipticOp.gardingγ_ofCoord (Op : Sobolev.FullEllipticOp d) :
    (FullEllipticOp.ofCoord Op).gardingγ = Op.gardingγ := by
  simp only [FullEllipticOp.gardingγ, Sobolev.FullEllipticOp.gardingγ, FullEllipticOp.ofCoord,
    EllipticCoeff.ofCoord]
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]

end DivForm
end EllipticPdes
