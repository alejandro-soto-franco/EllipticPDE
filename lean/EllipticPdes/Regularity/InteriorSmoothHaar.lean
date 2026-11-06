/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.InteriorSmoothGeneral
public import EllipticPdes.Spectrum.RellichHaar

/-!
# Interior smoothness for any additive Haar measure

`DivForm.FullEllipticOp.interior_smooth` is stated for the canonical volume of a finite-dimensional
real inner product space. An additive Haar measure is `c • volume` for some `c > 0`
(`H1Graph.exists_eq_smul_volume`). An operator given for `c • ν` is the same operator for `ν`
(`FullEllipticOp.ofSmul`), its form scales by `c` (`form_ofSmul`), and so does the `L²` pairing
(`H1Graph.inner_eq_smul_inner_lpSmulL`). Weak solutions therefore correspond under the identity on
representatives, and the volume theorem applies.

## Main declarations

* `EllipticPdes.DivForm.FullEllipticOp.ofSmul`, `form_ofSmul`, `weak_ofSmul`
* `EllipticPdes.DivForm.FullEllipticOp.interior_smooth_haar`
-/

@[expose] public section

open MeasureTheory Module
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace EllipticPdes

namespace H1Graph

section LpRescale

variable {α : Type*} [MeasurableSpace α] {ρ ρ' : Measure α} {c : ℝ≥0}

/-- An integral against `c • ρ` is `c` times the integral against `ρ`. -/
lemma Internal.integral_smul_measure_eq (F : α → ℝ) (h : ρ' = c • ρ) :
    ∫ x, F x ∂ρ' = c * ∫ x, F x ∂ρ := by
  rw [h, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]

/-- **Rescaling the measure rescales the `L²` inner product.** -/
lemma inner_eq_smul_inner_lpSmulL (hc : c ≠ 0) (h : ρ' = c • ρ) (f g : Lp ℝ 2 ρ') :
    ⟪f, g⟫ = c * ⟪lpSmulL hc h f, lpSmulL hc h g⟫ := by
  rw [L2.inner_def, L2.inner_def, Internal.integral_smul_measure_eq _ h]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [coeFn_lpSmulL hc h f, coeFn_lpSmulL hc h g] with x h1 h2
  rw [h1, h2]

/-- A statement true almost everywhere for `ρ` on `s` is true almost everywhere for `c • ρ`
on `s`. -/
lemma Internal.ae_restrict_smul {p : α → Prop} {s : Set α} (h : ∀ᵐ x ∂ρ.restrict s, p x) :
    ∀ᵐ x ∂(c • ρ).restrict s, p x :=
  Measure.restrict_smul c ρ s ▸ Measure.smul_absolutelyContinuous.ae_le h

/-- The rescaled datum is still the restriction of `g`. -/
lemma Internal.lpSmulL_ae_eq (hc : c ≠ 0) {Ω : Set α} {f : Lp ℝ 2 ((c • ρ).restrict Ω)} {g : α → ℝ}
    (hfg : f =ᵐ[(c • ρ).restrict Ω] g) :
    ⇑(lpSmulL hc (Measure.restrict_smul c ρ Ω) f) =ᵐ[ρ.restrict Ω] g :=
  (coeFn_lpSmulL hc (Measure.restrict_smul c ρ Ω) f).trans
    ((absolutelyContinuous_of_smul hc (Measure.restrict_smul c ρ Ω)).ae_eq hfg)

end LpRescale

section Graph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ν : Measure E} {Ω : Set E} (c : ℝ≥0) (hc : c ≠ 0)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma fnL_smulMeasureL (U : H1Graph (c • ν) Ω) :
    fnL (smulMeasureL ν Ω c hc U) = lpSmulL hc (Measure.restrict_smul c ν Ω) (fnL U) := rfl

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma gradL_smulMeasureL (U : H1Graph (c • ν) Ω) :
    gradL (smulMeasureL ν Ω c hc U) = lpSmulL hc (Measure.restrict_smul c ν Ω) (gradL U) := rfl

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma smulMeasureL_smulMeasureInvL (U : H1Graph ν Ω) :
    smulMeasureL ν Ω c hc (smulMeasureInvL ν Ω c U) = U :=
  (smulMeasureEquiv ν Ω c hc).apply_symm_apply U

variable [IsFiniteMeasureOnCompacts ν]

include hc in
/-- The inverse rescaling sends the graph of a test function to the graph of the same test
function. -/
lemma smulMeasureInvL_testGraphₗ (φ : testFunctions Ω) :
    smulMeasureInvL ν Ω c (testGraphₗ ν Ω φ) = testGraphₗ (c • ν) Ω φ :=
  ((smulMeasureEquiv ν Ω c hc).symm_apply_eq).2 (smulMeasureL_testGraphₗ c hc φ).symm

include hc in
/-- The inverse rescaling maps `H₀¹(ν, Ω)` into `H₀¹(c • ν, Ω)`. -/
lemma smulMeasureInvL_mem_H01 {U : H1Graph ν Ω} (hU : U ∈ H01 ν Ω) :
    smulMeasureInvL ν Ω c U ∈ H01 (c • ν) Ω :=
  mem_H01_of_map_testGraphₗ _ (smulMeasureInvL_testGraphₗ c hc) hU

/-- The inverse rescaling restricted to `H₀¹`. -/
def smulMeasureInvH01 (hc : c ≠ 0) : H01 ν Ω →L[ℝ] H01 (c • ν) Ω :=
  ((smulMeasureInvL ν Ω c).comp (H01 ν Ω).subtypeL).codRestrict _ fun U =>
    smulMeasureInvL_mem_H01 c hc U.2

lemma smulMeasureH01_smulMeasureInvH01 (U : H01 ν Ω) :
    smulMeasureH01 c hc (smulMeasureInvH01 c hc U) = U :=
  Subtype.ext (smulMeasureL_smulMeasureInvL c hc (U : H1Graph ν Ω))

end Graph

end H1Graph

namespace DivForm.FullEllipticOp

open H1Graph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  {ν : Measure E} {c : ℝ≥0}

/-- **Operator for a rescaled measure.** An operator given for `c • ν` with `c ≠ 0` is an
operator for `ν` with the same coefficients and constants. -/
def ofSmul (hc : c ≠ 0) (Op : FullEllipticOp (c • ν)) : FullEllipticOp ν where
  a := Op.a
  lam := Op.lam
  Λ := Op.Λ
  lam_pos := Op.lam_pos
  Λ_nonneg := Op.Λ_nonneg
  aestronglyMeasurable :=
    Op.aestronglyMeasurable.mono_ac (absolutelyContinuous_of_smul hc rfl)
  norm_le := (absolutelyContinuous_of_smul hc rfl).ae_le Op.norm_le
  coercive := (absolutelyContinuous_of_smul hc rfl).ae_le Op.coercive
  b := Op.b
  c := Op.c
  Bsup := Op.Bsup
  Csup := Op.Csup
  Bsup_nonneg := Op.Bsup_nonneg
  Csup_nonneg := Op.Csup_nonneg
  b_aestronglyMeasurable :=
    Op.b_aestronglyMeasurable.mono_ac (absolutelyContinuous_of_smul hc rfl)
  c_aestronglyMeasurable :=
    Op.c_aestronglyMeasurable.mono_ac (absolutelyContinuous_of_smul hc rfl)
  norm_b_le := (absolutelyContinuous_of_smul hc rfl).ae_le Op.norm_b_le
  abs_c_le := (absolutelyContinuous_of_smul hc rfl).ae_le Op.abs_c_le

/-- The principal integrand is integrable on `Ω`. -/
lemma Internal.integrable_principal (Op : FullEllipticOp ν) (Ω : Set E) (U V : H1Graph ν Ω) :
    Integrable (fun x => ⟪Op.a x (gradL U x), gradL V x⟫) (ν.restrict Ω) :=
  (L2.integrable_inner (Op.toEllipticCoeff.act Ω (gradL U)) (gradL V)).congr (by
    filter_upwards [Op.toEllipticCoeff.coeFn_act Ω (gradL U)] with y hy
    rw [hy])

/-- The lower-order integrand is integrable on `Ω`. -/
lemma Internal.integrable_lower (Op : FullEllipticOp ν) (Ω : Set E) (U V : H1Graph ν Ω) :
    Integrable (fun x => ⟪Op.b x, gradL U x⟫ * fnL V x + Op.c x * fnL U x * fnL V x)
      (ν.restrict Ω) := by
  refine ((L2.integrable_inner (Op.bAct Ω (gradL U)) (fnL V)).add
    (L2.integrable_inner (Op.cAct Ω (fnL U)) (fnL V))).congr ?_
  filter_upwards [Op.coeFn_bAct Ω (gradL U), Op.coeFn_cAct Ω (fnL U)] with y h1 h2
  simp only [Pi.add_apply, h1, h2, RCLike.inner_apply, conj_trivial]
  ring

/-- **Full form as one integral.** -/
lemma form_eq_integral_full (Op : FullEllipticOp ν) (Ω : Set E) (U V : H1Graph ν Ω) :
    Op.form Ω U V = ∫ x in Ω, (⟪Op.a x (gradL U x), gradL V x⟫ +
      (⟪Op.b x, gradL U x⟫ * fnL V x + Op.c x * fnL U x * fnL V x)) ∂ν := by
  rw [form_apply, EllipticCoeff.form_eq_integral, lowerForm_eq_integral,
    integral_add (Internal.integrable_principal Op Ω U V) (Internal.integrable_lower Op Ω U V)]

variable [FiniteDimensional ℝ E] [BorelSpace E] {Ω : Set E}

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **Scaling of the form with the measure.** -/
theorem form_ofSmul (hc : c ≠ 0) (Op : FullEllipticOp (c • ν)) (U V : H1Graph (c • ν) Ω) :
    Op.form Ω U V =
      c * (Op.ofSmul hc).form Ω (smulMeasureL ν Ω c hc U) (smulMeasureL ν Ω c hc V) := by
  rw [form_eq_integral_full, form_eq_integral_full,
    H1Graph.Internal.integral_smul_measure_eq _ (Measure.restrict_smul c ν Ω)]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [coeFn_lpSmulL hc (Measure.restrict_smul c ν Ω) (fnL U),
    coeFn_lpSmulL hc (Measure.restrict_smul c ν Ω) (fnL V),
    coeFn_lpSmulL hc (Measure.restrict_smul c ν Ω) (gradL U),
    coeFn_lpSmulL hc (Measure.restrict_smul c ν Ω) (gradL V)] with x h1 h2 h3 h4
  rw [fnL_smulMeasureL, fnL_smulMeasureL, gradL_smulMeasureL, gradL_smulMeasureL, h1, h2, h3, h4]
  rfl

/-- **Weak solutions correspond under rescaling.** Under the identity on representatives a weak
solution for `c • ν` with datum `f` is a weak solution for `ν` with the same datum. -/
theorem weak_ofSmul [IsFiniteMeasureOnCompacts ν] (hc : c ≠ 0) (Op : FullEllipticOp (c • ν))
    (u : H01 (c • ν) Ω) (f : Lp ℝ 2 ((c • ν).restrict Ω))
    (hweak : ∀ v : H01 (c • ν) Ω, Op.formOn Ω (H01 (c • ν) Ω) u v = ⟪f, embL2 (c • ν) Ω v⟫)
    (v : H01 ν Ω) :
    (Op.ofSmul hc).formOn Ω (H01 ν Ω) (smulMeasureH01 c hc u) v =
      ⟪lpSmulL hc (Measure.restrict_smul c ν Ω) f, embL2 ν Ω v⟫ := by
  refine mul_left_cancel₀ (NNReal.coe_ne_zero.2 hc) ?_
  rw [← smulMeasureH01_smulMeasureInvH01 c hc v]
  exact (form_ofSmul hc Op _ _).symm.trans ((hweak _).trans
    (inner_eq_smul_inner_lpSmulL hc (Measure.restrict_smul c ν Ω) _ _))

/-- The function part of the rescaled solution agrees with that of the solution on the interior of
a subset of `Ω`. -/
lemma Internal.embL2_smulMeasureH01_ae [IsFiniteMeasureOnCompacts ν] (hc : c ≠ 0)
    (u : H01 (c • ν) Ω) {V : Set E} (hVΩ : V ⊆ Ω) :
    ⇑(embL2 ν Ω (smulMeasureH01 c hc u)) =ᵐ[ν.restrict (interior V)] ⇑(embL2 (c • ν) Ω u) :=
  ae_restrict_of_ae_restrict_of_subset (interior_subset.trans hVΩ)
    (coeFn_lpSmulL hc (Measure.restrict_smul c ν Ω) _)

/-- **Infinite differentiability in the interior for any additive Haar measure** (Evans, *Partial
Differential Equations* (2nd ed.), §6.3.1, Theorem 3, p. 334). The statement of `interior_smooth`
with the canonical volume replaced by any additive Haar measure `μ`. -/
theorem interior_smooth_haar {n : ℕ} (hd : finrank ℝ E = n + 1) (μ : Measure E)
    [μ.IsAddHaarMeasure] (Op : FullEllipticOp μ) (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA : Regularity.IsSmoothBdd Op.a) (hB : Regularity.IsSmoothBdd Op.b)
    (hC : Regularity.IsSmoothBdd Op.c) (u : H01 μ Ω) (f : Lp ℝ 2 (μ.restrict Ω)) {g : E → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (hfg : f =ᵐ[μ.restrict Ω] g)
    (hweak : ∀ v : H01 μ Ω, Op.formOn Ω (H01 μ Ω) u v = ⟪f, embL2 μ Ω v⟫)
    {V : Set E} (hVc : IsCompact V) (hVΩ : V ⊆ Ω) :
    ∃ u' : E → ℝ, u' =ᵐ[μ.restrict (interior V)] ⇑(embL2 μ Ω u) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) u' (interior V) := by
  obtain ⟨c, hc, rfl⟩ := exists_eq_smul_volume μ
  obtain ⟨u', hae, hsm⟩ := interior_smooth hd (Op.ofSmul hc) hΩm hΩo hA hB hC
    (smulMeasureH01 c hc u) _ hg hgc (H1Graph.Internal.lpSmulL_ae_eq hc hfg)
    (weak_ofSmul hc Op u f hweak) hVc hVΩ
  exact ⟨u', H1Graph.Internal.ae_restrict_smul
    (hae.trans (Internal.embL2_smulMeasureH01_ae hc u hVΩ)), hsm⟩

end DivForm.FullEllipticOp

end EllipticPdes
