/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Form.DivForm
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import EllipticPdes.SobolevP.RieszBridge
public import EllipticPdes.SobolevP.Transfer

/-!
# Divergence-form operators on a normed space

On a finite-dimensional real normed space `E` with a Haar measure `μ` there is no gradient vector,
so the coefficient `a x` is a linear map `StrongDual ℝ E →L[ℝ] E` and the principal form is
`∇v (a ∇u)`. The transfer along `L = toEuclidean : E ≃L[ℝ] F`, with
`F = EuclideanSpace ℝ (Fin (finrank ℝ E))`, sends such an operator to a `DivForm.FullEllipticOp`
on `F` for the pushforward measure, with coefficient `a' y w = L (a (L⁻¹ y) (⟪w, ·⟫ ∘ L))`.

## Main declarations

* `EllipticPdes.NormedDivForm.EllipticCoeff`, `EllipticPdes.NormedDivForm.FullEllipticOp`: the
  coefficients.
* `EllipticPdes.NormedDivForm.FullEllipticOp.transfer`: the transferred operator on `F`.
* `EllipticPdes.NormedDivForm.FullEllipticOp.transferEquiv`: `W1p0 2 μ Ω ≃L H01 (μ.map L) (L '' Ω)`.
* `EllipticPdes.NormedDivForm.FullEllipticOp.formOn`: the bilinear form on `W1p0 2 μ Ω`.
* `EllipticPdes.NormedDivForm.FullEllipticOp.formOn_eq_integral`: its integral formula.
* `EllipticPdes.NormedDivForm.FullEllipticOp.formOn_transfer`: `B_E[u, v] = B_F[T u, T v]`.
* `EllipticPdes.NormedDivForm.FullEllipticOp.transfer_adjoint`: symmetry of `a` transfers.
-/

@[expose] public section

open MeasureTheory Module
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace EllipticPdes

namespace NormedDivForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

/-- A bounded measurable uniformly elliptic coefficient field `a`, with ellipticity constant
`lam` and bound `Λ`, on a normed space. -/
structure EllipticCoeff (μ : Measure E) where
  /-- The coefficient field. -/
  a : E → StrongDual ℝ E →L[ℝ] E
  /-- The ellipticity constant. -/
  lam : ℝ
  /-- The bound on the operator norm. -/
  Λ : ℝ
  /-- The ellipticity constant is positive. -/
  lam_pos : 0 < lam
  /-- The norm bound is nonnegative. -/
  Λ_nonneg : 0 ≤ Λ
  /-- The coefficient field is almost everywhere strongly measurable. -/
  aestronglyMeasurable : AEStronglyMeasurable a μ
  /-- The operator norm of the coefficient is at most `Λ` almost everywhere. -/
  norm_le : ∀ᵐ x ∂μ, ‖a x‖ ≤ Λ
  /-- Uniform ellipticity: `ξ (a x ξ) ≥ lam ‖ξ‖²` almost everywhere. -/
  coercive : ∀ᵐ x ∂μ, ∀ ξ : StrongDual ℝ E, lam * ‖ξ‖ ^ 2 ≤ ξ (a x ξ)

/-- A divergence-form operator `-div (a ∇u) + ∇u (b) + c u` with bounded measurable
coefficients on a normed space. -/
structure FullEllipticOp (μ : Measure E) : Type _ extends EllipticCoeff μ where
  /-- The drift. -/
  b : E → E
  /-- The zeroth-order coefficient. -/
  c : E → ℝ
  /-- The bound on the drift. -/
  Bsup : ℝ
  /-- The bound on the zeroth-order coefficient. -/
  Csup : ℝ
  /-- The drift bound is nonnegative. -/
  Bsup_nonneg : 0 ≤ Bsup
  /-- The bound on the zeroth-order coefficient is nonnegative. -/
  Csup_nonneg : 0 ≤ Csup
  /-- The drift is almost everywhere strongly measurable. -/
  b_aestronglyMeasurable : AEStronglyMeasurable b μ
  /-- The zeroth-order coefficient is almost everywhere strongly measurable. -/
  c_aestronglyMeasurable : AEStronglyMeasurable c μ
  /-- The drift has norm at most `Bsup` almost everywhere. -/
  norm_b_le : ∀ᵐ x ∂μ, ‖b x‖ ≤ Bsup
  /-- The zeroth-order coefficient is at most `Csup` in absolute value almost everywhere. -/
  abs_c_le : ∀ᵐ x ∂μ, |c x| ≤ Csup

section Transfer

variable [FiniteDimensional ℝ E]

local notation "𝔽" => EuclideanSpace ℝ (Fin (finrank ℝ E))
local notation "𝓛" => (toEuclidean (E := E))
local notation "𝓛'" => ContinuousLinearEquiv.symm (toEuclidean (E := E))

/-- The pullback of a vector of `F = EuclideanSpace ℝ (Fin (finrank ℝ E))`, read as a covector
through the Riesz map, to a covector on `E` along `toEuclidean`. -/
def pullback : 𝔽 →L[ℝ] StrongDual ℝ E :=
  ((ContinuousLinearMap.compL ℝ E 𝔽 ℝ).flip (𝓛 : E →L[ℝ] 𝔽)).comp rieszC'

omit [MeasurableSpace E] in
lemma pullback_apply (w : 𝔽) (z : E) : pullback w z = inner ℝ w (𝓛 z) := rfl

/-- The matrix `L ∘ A ∘ pullback` on `F` that a coefficient value `A` transfers to. -/
def transferMat (A : StrongDual ℝ E →L[ℝ] E) : 𝔽 →L[ℝ] 𝔽 :=
  (𝓛 : E →L[ℝ] 𝔽).comp (A.comp pullback)

omit [MeasurableSpace E] in
lemma transferMat_apply (A : StrongDual ℝ E →L[ℝ] E) (w : 𝔽) :
    transferMat A w = 𝓛 (A (pullback w)) := rfl

omit [MeasurableSpace E] in
lemma pullback_toDual_symm (ξ : StrongDual ℝ E) :
    pullback ((InnerProductSpace.toDual ℝ 𝔽).symm (ξ.comp (𝓛' : 𝔽 →L[ℝ] E))) = ξ := by
  ext z
  rw [pullback_apply, InnerProductSpace.toDual_symm_apply]
  simp

omit [MeasurableSpace E] in
lemma norm_pullback_le (w : 𝔽) : ‖pullback w‖ ≤ ‖(𝓛 : E →L[ℝ] 𝔽)‖ * ‖w‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
  rw [pullback_apply]
  calc ‖inner ℝ w (𝓛 z)‖ ≤ ‖w‖ * ‖𝓛 z‖ := norm_inner_le_norm _ _
    _ ≤ ‖w‖ * (‖(𝓛 : E →L[ℝ] 𝔽)‖ * ‖z‖) := by
        gcongr
        exact (𝓛 : E →L[ℝ] 𝔽).le_opNorm z
    _ = _ := by ring

omit [MeasurableSpace E] in
lemma norm_transferMat_le (A : StrongDual ℝ E →L[ℝ] E) :
    ‖transferMat A‖ ≤ ‖(𝓛 : E →L[ℝ] 𝔽)‖ * ‖A‖ * ‖(𝓛 : E →L[ℝ] 𝔽)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [transferMat_apply]
  calc ‖𝓛 (A (pullback w))‖ ≤ ‖(𝓛 : E →L[ℝ] 𝔽)‖ * ‖A (pullback w)‖ :=
        (𝓛 : E →L[ℝ] 𝔽).le_opNorm _
    _ ≤ ‖(𝓛 : E →L[ℝ] 𝔽)‖ * (‖A‖ * ‖pullback w‖) := by gcongr; exact A.le_opNorm _
    _ ≤ ‖(𝓛 : E →L[ℝ] 𝔽)‖ * (‖A‖ * (‖(𝓛 : E →L[ℝ] 𝔽)‖ * ‖w‖)) := by
        gcongr; exact norm_pullback_le w
    _ = _ := by ring

omit [MeasurableSpace E] in
lemma inner_transferMat_self (A : StrongDual ℝ E →L[ℝ] E) (w : 𝔽) :
    inner ℝ (transferMat A w) w = pullback w (A (pullback w)) := by
  rw [transferMat_apply, real_inner_comm, pullback_apply]

omit [MeasurableSpace E] in
lemma norm_le_pullback (w : 𝔽) :
    ‖w‖ ≤ max ‖(𝓛' : 𝔽 →L[ℝ] E)‖ 1 * ‖pullback w‖ := by
  rcases eq_or_lt_of_le (norm_nonneg w) with h | h
  · rw [← h]; positivity
  · have h1 : ‖w‖ * ‖w‖ ≤ (max ‖(𝓛' : 𝔽 →L[ℝ] E)‖ 1 * ‖pullback w‖) * ‖w‖ := by
      calc ‖w‖ * ‖w‖ = inner ℝ w w := (real_inner_self_eq_norm_mul_norm w).symm
        _ = pullback w (𝓛' w) := by rw [pullback_apply]; simp
        _ ≤ ‖pullback w‖ * ‖𝓛' w‖ := (le_abs_self _).trans ((pullback w).le_opNorm _)
        _ ≤ ‖pullback w‖ * (‖(𝓛' : 𝔽 →L[ℝ] E)‖ * ‖w‖) := by
            gcongr; exact (𝓛' : 𝔽 →L[ℝ] E).le_opNorm w
        _ ≤ ‖pullback w‖ * (max ‖(𝓛' : 𝔽 →L[ℝ] E)‖ 1 * ‖w‖) := by
            gcongr; exact le_max_left _ _
        _ = _ := by ring
    exact le_of_mul_le_mul_right h1 h

omit [MeasurableSpace E] in
lemma coercive_transferMat (A : StrongDual ℝ E →L[ℝ] E) {lam : ℝ} (hlam : 0 < lam)
    (h : ∀ ξ : StrongDual ℝ E, lam * ‖ξ‖ ^ 2 ≤ ξ (A ξ)) (w : 𝔽) :
    lam / (max ‖(𝓛' : 𝔽 →L[ℝ] E)‖ 1) ^ 2 * ‖w‖ ^ 2 ≤ inner ℝ (transferMat A w) w := by
  have hM : 0 < max ‖(𝓛' : 𝔽 →L[ℝ] E)‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  rw [inner_transferMat_self]
  refine le_trans ?_ (h (pullback w))
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h2 : ‖w‖ ^ 2 ≤ (max ‖(𝓛' : 𝔽 →L[ℝ] E)‖ 1 * ‖pullback w‖) ^ 2 := by
    gcongr; exact norm_le_pullback w
  nlinarith

omit [MeasurableSpace E] in
lemma inner_transferMat (A : StrongDual ℝ E →L[ℝ] E) (ξ η : StrongDual ℝ E) :
    inner ℝ (transferMat A ((InnerProductSpace.toDual ℝ 𝔽).symm (ξ.comp (𝓛' : 𝔽 →L[ℝ] E))))
      ((InnerProductSpace.toDual ℝ 𝔽).symm (η.comp (𝓛' : 𝔽 →L[ℝ] E))) = η (A ξ) := by
  rw [transferMat_apply, pullback_toDual_symm, real_inner_comm,
    InnerProductSpace.toDual_symm_apply]
  simp

omit [MeasurableSpace E] in
lemma inner_transferVec (x : E) (ξ : StrongDual ℝ E) :
    inner ℝ (𝓛 x) ((InnerProductSpace.toDual ℝ 𝔽).symm (ξ.comp (𝓛' : 𝔽 →L[ℝ] E))) = ξ x := by
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  simp

omit [MeasurableSpace E] in
lemma inner_transferMat_comm (A : StrongDual ℝ E →L[ℝ] E)
    (hA : ∀ ξ η : StrongDual ℝ E, η (A ξ) = ξ (A η)) (v w : 𝔽) :
    inner ℝ (transferMat A v) w = inner ℝ v (transferMat A w) := by
  rw [transferMat_apply, transferMat_apply, real_inner_comm, ← pullback_apply, ← pullback_apply,
    hA]

end Transfer

section Operator

variable [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

local notation "𝔽" => EuclideanSpace ℝ (Fin (finrank ℝ E))
local notation "𝓛" => (toEuclidean (E := E))
local notation "𝓛'" => ContinuousLinearEquiv.symm (toEuclidean (E := E))

omit [μ.IsAddHaarMeasure] in
/-- `L.symm` is measure-preserving from the pushforward back to `μ`. -/
lemma measurePreserving_symm_map : MeasurePreserving 𝓛' (μ.map 𝓛) μ :=
  (show MeasurePreserving (toEuclidean (E := E)).toHomeomorph.toMeasurableEquiv μ (μ.map 𝓛) from
    ⟨(toEuclidean (E := E)).continuous.measurable, rfl⟩).symm
    (toEuclidean (E := E)).toHomeomorph.toMeasurableEquiv

variable (μ) in
/-- The change of variables `W₀^{1,2}(Ω) ≃L H₀¹(L '' Ω)`: the transfer along `toEuclidean`
followed by the Riesz bridge. -/
def transferEquiv (Ω : Set E) : W1p0 2 μ Ω ≃L[ℝ] H1Graph.H01 (μ.map 𝓛) (𝓛 '' Ω) :=
  (W1p0.mapEquiv 𝓛).trans W1p0.toH01

namespace FullEllipticOp

/-- **Transferred operator.** The coefficient is `a' y w = L (a (L⁻¹ y) (⟪w, ·⟫ ∘ L))`, the
drift is `b' y = L (b (L⁻¹ y))` and the zeroth-order term is `c' y = c (L⁻¹ y)`. The constants are
`lam' = lam / (max ‖L⁻¹‖ 1) ^ 2`, `Λ' = ‖L‖ Λ ‖L‖` and `Bsup' = ‖L‖ Bsup`. -/
def transfer (Op : FullEllipticOp μ) : DivForm.FullEllipticOp (μ.map 𝓛) where
  a y := transferMat (Op.a (𝓛' y))
  lam := Op.lam / (max ‖(𝓛' : 𝔽 →L[ℝ] E)‖ 1) ^ 2
  Λ := ‖(𝓛 : E →L[ℝ] 𝔽)‖ * Op.Λ * ‖(𝓛 : E →L[ℝ] 𝔽)‖
  lam_pos := by
    have : 0 < max ‖(𝓛' : 𝔽 →L[ℝ] E)‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have := Op.lam_pos
    positivity
  Λ_nonneg := mul_nonneg (mul_nonneg (norm_nonneg _) Op.Λ_nonneg) (norm_nonneg _)
  aestronglyMeasurable :=
    (continuous_const.clm_comp (continuous_id.clm_comp continuous_const) :
      Continuous fun g : StrongDual ℝ E →L[ℝ] E => (𝓛 : E →L[ℝ] 𝔽).comp (g.comp pullback)
      ).comp_aestronglyMeasurable
      (Op.aestronglyMeasurable.comp_measurePreserving measurePreserving_symm_map)
  norm_le := by
    filter_upwards [measurePreserving_symm_map.quasiMeasurePreserving.ae Op.norm_le] with y hy
    refine (norm_transferMat_le _).trans ?_
    gcongr
  coercive := by
    filter_upwards [measurePreserving_symm_map.quasiMeasurePreserving.ae Op.coercive] with y hy w
    exact coercive_transferMat _ Op.lam_pos hy w
  b y := 𝓛 (Op.b (𝓛' y))
  c y := Op.c (𝓛' y)
  Bsup := ‖(𝓛 : E →L[ℝ] 𝔽)‖ * Op.Bsup
  Csup := Op.Csup
  Bsup_nonneg := mul_nonneg (norm_nonneg _) Op.Bsup_nonneg
  Csup_nonneg := Op.Csup_nonneg
  b_aestronglyMeasurable :=
    (toEuclidean (E := E)).continuous.comp_aestronglyMeasurable
      (Op.b_aestronglyMeasurable.comp_measurePreserving measurePreserving_symm_map)
  c_aestronglyMeasurable :=
    Op.c_aestronglyMeasurable.comp_measurePreserving measurePreserving_symm_map
  norm_b_le := by
    filter_upwards [measurePreserving_symm_map.quasiMeasurePreserving.ae Op.norm_b_le] with y hy
    exact ((𝓛 : E →L[ℝ] 𝔽).le_opNorm _).trans (by gcongr)
  abs_c_le := measurePreserving_symm_map.quasiMeasurePreserving.ae Op.abs_c_le

variable (Op : FullEllipticOp μ) (Ω : Set E)

/-- The bilinear form on `W₀^{1,2}(Ω)`, the form of the transferred operator on `H₀¹(L '' Ω)`
pulled back along `transferEquiv`. -/
def formOn : W1p0 2 μ Ω →L[ℝ] W1p0 2 μ Ω →L[ℝ] ℝ :=
  (Op.transfer.formOn (𝓛 '' Ω) (H1Graph.H01 (μ.map 𝓛) (𝓛 '' Ω))).bilinearComp
    (transferEquiv μ Ω : W1p0 2 μ Ω →L[ℝ] _) (transferEquiv μ Ω : W1p0 2 μ Ω →L[ℝ] _)

/-- **Form identity.** The form on `E` is the form of the transferred operator on the
transferred functions. -/
theorem formOn_transfer (u v : W1p0 2 μ Ω) :
    Op.formOn Ω u v =
      Op.transfer.formOn (𝓛 '' Ω) (H1Graph.H01 (μ.map 𝓛) (𝓛 '' Ω))
        (transferEquiv μ Ω u) (transferEquiv μ Ω v) := rfl

omit [μ.IsAddHaarMeasure] in
/-- The full form of the transferred operator, as one integral over the image. -/
lemma transfer_form_eq_integral (U V : H1Graph (μ.map 𝓛) (𝓛 '' Ω)) :
    Op.transfer.form (𝓛 '' Ω) U V = ∫ y in 𝓛 '' Ω,
      (inner ℝ (Op.transfer.a y (H1Graph.gradL U y)) (H1Graph.gradL V y) +
        (inner ℝ (Op.transfer.b y) (H1Graph.gradL U y) * H1Graph.fnL V y +
          Op.transfer.c y * H1Graph.fnL U y * H1Graph.fnL V y)) ∂(μ.map 𝓛) := by
  have hP : Integrable (fun y => inner ℝ (Op.transfer.a y (H1Graph.gradL U y))
      (H1Graph.gradL V y)) ((μ.map 𝓛).restrict (𝓛 '' Ω)) :=
    (L2.integrable_inner (Op.transfer.toEllipticCoeff.act (𝓛 '' Ω) (H1Graph.gradL U))
      (H1Graph.gradL V)).congr (by
        filter_upwards [Op.transfer.toEllipticCoeff.coeFn_act (𝓛 '' Ω) (H1Graph.gradL U)]
          with y hy
        rw [hy])
  have hR : Integrable (fun y => inner ℝ (Op.transfer.b y) (H1Graph.gradL U y) *
      H1Graph.fnL V y + Op.transfer.c y * H1Graph.fnL U y * H1Graph.fnL V y)
      ((μ.map 𝓛).restrict (𝓛 '' Ω)) := by
    refine ((L2.integrable_inner (Op.transfer.bAct (𝓛 '' Ω) (H1Graph.gradL U))
      (H1Graph.fnL V)).add (L2.integrable_inner (Op.transfer.cAct (𝓛 '' Ω) (H1Graph.fnL U))
        (H1Graph.fnL V))).congr ?_
    filter_upwards [Op.transfer.coeFn_bAct (𝓛 '' Ω) (H1Graph.gradL U),
      Op.transfer.coeFn_cAct (𝓛 '' Ω) (H1Graph.fnL U)] with y h1 h2
    simp only [Pi.add_apply, h1, h2, RCLike.inner_apply, conj_trivial]
    ring
  have h1 := DivForm.EllipticCoeff.form_eq_integral Op.transfer.toEllipticCoeff (𝓛 '' Ω) U V
  have h2 := DivForm.FullEllipticOp.lowerForm_eq_integral Op.transfer U V
  have h3 := DivForm.FullEllipticOp.form_apply Op.transfer U V
  exact (h3.trans (congrArg₂ (· + ·) h1 h2)).trans (integral_add hP hR).symm

lemma fnL_transferEquiv_ae (w : W1p0 2 μ Ω) :
    (⇑(H1Graph.fnL (transferEquiv μ Ω w : H1Graph (μ.map 𝓛) (𝓛 '' Ω))) ∘ 𝓛) =ᵐ[μ.restrict Ω]
      ⇑(W1p0.fnL w) := by
  have hmp := measurePreserving_restrict_image 𝓛 μ Ω
  filter_upwards [hmp.quasiMeasurePreserving.ae_eq_comp (W1p0.fnL_mapEquiv 𝓛 w)] with x hx
  exact hx.trans (by simp)

lemma gradL_transferEquiv_ae (w : W1p0 2 μ Ω) :
    (fun x => H1Graph.gradL (transferEquiv μ Ω w : H1Graph (μ.map 𝓛) (𝓛 '' Ω)) (𝓛 x))
      =ᵐ[μ.restrict Ω] fun x => (InnerProductSpace.toDual ℝ 𝔽).symm
        ((W1p0.gradL w x).comp (𝓛' : 𝔽 →L[ℝ] E)) := by
  have hmp := measurePreserving_restrict_image 𝓛 μ Ω
  have h : ⇑(H1Graph.gradL (transferEquiv μ Ω w : H1Graph (μ.map 𝓛) (𝓛 '' Ω)))
      =ᵐ[(μ.map 𝓛).restrict (𝓛 '' Ω)] fun y => (InnerProductSpace.toDual ℝ 𝔽).symm
        ((W1p0.gradL w (𝓛' y)).comp (𝓛' : 𝔽 →L[ℝ] E)) := by
    filter_upwards [W1p0.gradL_toH01 (W1p0.mapEquiv 𝓛 w), W1p0.gradL_mapEquiv 𝓛 w]
      with y h1 h2
    exact h1.trans (by rw [h2])
  filter_upwards [hmp.quasiMeasurePreserving.ae_eq_comp h] with x hx
  simpa using hx

omit [μ.IsAddHaarMeasure] in
lemma transfer_integrand (x : E) (ξ η : StrongDual ℝ E) (s t : ℝ) :
    inner ℝ (Op.transfer.a (𝓛 x) ((InnerProductSpace.toDual ℝ 𝔽).symm
        (ξ.comp (𝓛' : 𝔽 →L[ℝ] E)))) ((InnerProductSpace.toDual ℝ 𝔽).symm
        (η.comp (𝓛' : 𝔽 →L[ℝ] E))) +
      (inner ℝ (Op.transfer.b (𝓛 x)) ((InnerProductSpace.toDual ℝ 𝔽).symm
        (ξ.comp (𝓛' : 𝔽 →L[ℝ] E))) * t + Op.transfer.c (𝓛 x) * s * t) =
    η (Op.a x ξ) + ξ (Op.b x) * t + Op.c x * s * t := by
  have e1 : Op.transfer.a (𝓛 x) = transferMat (Op.a x) := by
    simp [transfer]
  have e2 : Op.transfer.b (𝓛 x) = 𝓛 (Op.b x) := by simp [transfer]
  have e3 : Op.transfer.c (𝓛 x) = Op.c x := by simp [transfer]
  rw [e1, e2, e3, inner_transferMat, inner_transferVec]
  ring

/-- **Integral formula.** `B[u, v] = ∫_Ω ∇v (a ∇u) + ∇u (b) v + c u v`. -/
theorem formOn_eq_integral (u v : W1p0 2 μ Ω) :
    Op.formOn Ω u v = ∫ x in Ω, ((W1p0.gradL v x) (Op.a x (W1p0.gradL u x)) +
      (W1p0.gradL u x) (Op.b x) * W1p0.fnL v x + Op.c x * W1p0.fnL u x * W1p0.fnL v x) ∂μ := by
  rw [formOn_transfer, DivForm.FullEllipticOp.formOn_apply, transfer_form_eq_integral]
  rw [← (measurePreserving_restrict_image 𝓛 μ Ω).integral_comp
    (toEuclidean (E := E)).toHomeomorph.toMeasurableEquiv.measurableEmbedding]
  refine integral_congr_ae ?_
  filter_upwards [fnL_transferEquiv_ae Ω u, fnL_transferEquiv_ae Ω v,
    gradL_transferEquiv_ae Ω u, gradL_transferEquiv_ae Ω v] with x h1 h2 h3 h4
  have h1' : H1Graph.fnL (transferEquiv μ Ω u : H1Graph (μ.map 𝓛) (𝓛 '' Ω)) (𝓛 x) =
    W1p0.fnL u x := h1
  have h2' : H1Graph.fnL (transferEquiv μ Ω v : H1Graph (μ.map 𝓛) (𝓛 '' Ω)) (𝓛 x) =
    W1p0.fnL v x := h2
  simp only [h1', h2', h3, h4]
  exact transfer_integrand Op x _ _ _ _

omit [μ.IsAddHaarMeasure] in
/-- If the coefficient is almost everywhere symmetric, the transferred coefficient is almost
everywhere self-adjoint. -/
theorem transfer_adjoint (h : ∀ᵐ x ∂μ, ∀ ξ η : StrongDual ℝ E, η (Op.a x ξ) = ξ (Op.a x η)) :
    ∀ᵐ y ∂(μ.map 𝓛), (Op.transfer.a y).adjoint = Op.transfer.a y := by
  filter_upwards [measurePreserving_symm_map.quasiMeasurePreserving.ae h] with y hy
  refine ContinuousLinearMap.ext fun w => ext_inner_right ℝ fun v => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (inner_transferMat_comm _ hy w v).symm

end FullEllipticOp

end Operator

end NormedDivForm

end EllipticPdes
