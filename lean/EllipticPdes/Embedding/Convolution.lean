/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Analysis.Mollifier
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Young's `Lᵖ` inequality for a probability kernel

On a finite-dimensional real normed space `E` with an additive Haar measure `μ`, convolving an
`Lᵖ` function `h : E → F` (with `1 ≤ p < ∞`) against a non-negative kernel of unit mass does not
increase its `Lᵖ` seminorm (`eLpNorm_convolution_le_of_integral_eq_one`). The proof derives the
pointwise bound from Hölder's inequality in `ℝ≥0∞` and closes with Tonelli, so no Minkowski
integral inequality is required.

The mollifications `ρₙ ⋆ h` of an `Lᵖ` function by normed bumps converge to `h` in `Lᵖ` as the
outer radii tend to `0` (`tendsto_eLpNorm_normed_convolution_sub`). The argument is a density
`3ε` argument: approximate `h` by a smooth compactly supported `w`
(`MeasureTheory.MemLp.exist_eLpNorm_sub_le`), control the tail `ρ ⋆ (h - w)` by the Young bound,
and drive `ρ ⋆ w - w` to zero with the uniform convergence of
`ContDiffBump.dist_normed_convolution_le` on a fixed compact set. It holds along an arbitrary
filter.

The real-valued statements with the kernel on the right (`eLpNorm_convolution_le`,
`contDiff_convolution_normed`, `tendsto_eLpNorm_convolution_sub`) are the forms the coordinate
files use; they are instances of the general statements through the commutativity of
convolution against scalar multiplication. The file also contains the elementary `Lᵖ`
bookkeeping shared by the Sobolev ladders and the continuous linear maps into `Lp` built from
almost everywhere linear families.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal Convolution Topology Pointwise

noncomputable section

namespace EllipticPdes.Embedding

section Young

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Pointwise Young bound.** For `1 ≤ p` and a kernel `ρ` of unit `ℝ≥0∞`-mass,
`‖(ρ ⋆ h)(x)‖ₑ ^ p ≤ ∫⁻ t, ‖ρ t‖ₑ ‖h (x - t)‖ₑ ^ p`. -/
private theorem enorm_convolution_rpow_le {p : ℝ} (hp : 1 ≤ p) {ρ : E → ℝ} {h : E → F}
    (hρen : AEMeasurable (fun z => ‖ρ z‖ₑ) μ) (hhen : AEMeasurable (fun z => ‖h z‖ₑ) μ)
    (hmass : ∫⁻ z, ‖ρ z‖ₑ ∂μ = 1) (x : E) :
    ‖(ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) x‖ₑ ^ p
      ≤ ∫⁻ t, ‖ρ t‖ₑ * ‖h (x - t)‖ₑ ^ p ∂μ := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hhxen : AEMeasurable (fun t => ‖h (x - t)‖ₑ) μ :=
    hhen.comp_quasiMeasurePreserving
      (Measure.measurePreserving_sub_left μ x).quasiMeasurePreserving
  have hbound : ‖(ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) x‖ₑ
      ≤ ∫⁻ t, ‖ρ t‖ₑ * ‖h (x - t)‖ₑ ∂μ := by
    rw [convolution_def]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun t => ?_))
    simp [enorm_smul]
  refine (ENNReal.rpow_le_rpow hbound hp0.le).trans ?_
  rcases eq_or_lt_of_le hp with hp1 | hp1
  · subst hp1
    simp only [ENNReal.rpow_one]
    exact le_rfl
  · have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp1
    set q := Real.conjExponent p
    have hsum : 1 / p + 1 / q = 1 := by simpa using hpq.one_div_add_one_div
    have e1 : ∀ t, ‖ρ t‖ₑ ^ (1 / q) * (‖ρ t‖ₑ ^ (1 / p) * ‖h (x - t)‖ₑ)
        = ‖ρ t‖ₑ * ‖h (x - t)‖ₑ := fun t => by
      rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ hpq.symm.one_div_nonneg
        hpq.one_div_nonneg, add_comm, hsum, ENNReal.rpow_one]
    have e2 : ∀ t, (‖ρ t‖ₑ ^ (1 / p) * ‖h (x - t)‖ₑ) ^ p = ‖ρ t‖ₑ * ‖h (x - t)‖ₑ ^ p :=
      fun t => by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_div,
        inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
    have e3 : ∀ t, (‖ρ t‖ₑ ^ (1 / q)) ^ q = ‖ρ t‖ₑ := fun t => by
      rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hpq.symm.pos.ne', ENNReal.rpow_one]
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq.symm (hρen.pow_const (1 / q))
      ((hρen.pow_const (1 / p)).mul hhxen)
    simp only [Pi.mul_apply] at hH
    rw [lintegral_congr e1, lintegral_congr e2, lintegral_congr e3, hmass, ENNReal.one_rpow,
      one_mul] at hH
    calc (∫⁻ t, ‖ρ t‖ₑ * ‖h (x - t)‖ₑ ∂μ) ^ p
        ≤ ((∫⁻ t, ‖ρ t‖ₑ * ‖h (x - t)‖ₑ ^ p ∂μ) ^ (1 / p)) ^ p :=
          ENNReal.rpow_le_rpow hH hp0.le
      _ = _ := by rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [μ.IsAddHaarMeasure] in
/-- A non-negative function of unit integral has unit `ℝ≥0∞`-mass. -/
private theorem lintegral_enorm_eq_one {ρ : E → ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ∫ y, ρ y ∂μ = 1) :
    ∫⁻ z, ‖ρ z‖ₑ ∂μ = 1 := by
  have hρint : Integrable ρ μ := by
    by_contra hcon
    rw [integral_undef hcon] at hρ1
    exact one_ne_zero hρ1.symm
  rw [lintegral_congr fun z => Real.enorm_of_nonneg (hρ0 z),
    ← ofReal_integral_eq_lintegral_ofReal hρint (ae_of_all _ fun z => hρ0 z), hρ1,
    ENNReal.ofReal_one]

/-- **Young's `Lᵖ` inequality for a probability kernel.** For `1 ≤ p < ∞`, a non-negative
kernel `ρ` with unit mass `∫ ρ = 1` and a measurable `h : E → F`, convolution against `ρ` does
not increase the `Lᵖ` seminorm: `‖ρ ⋆ h‖_{Lᵖ} ≤ ‖h‖_{Lᵖ}`. -/
theorem eLpNorm_convolution_le_of_integral_eq_one {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {ρ : E → ℝ} (hρ0 : 0 ≤ ρ)
    (hρm : AEStronglyMeasurable ρ μ) (hρ1 : ∫ y, ρ y ∂μ = 1) {h : E → F}
    (hh : AEStronglyMeasurable h μ) :
    eLpNorm (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) p μ ≤ eLpNorm h p μ := by
  have hP0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hp0 : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hpt hp
  have hhen : AEMeasurable (fun z => ‖h z‖ₑ) μ := hh.enorm
  have hρen : AEMeasurable (fun z => ‖ρ z‖ₑ) μ := hρm.enorm
  have hmass := lintegral_enorm_eq_one hρ0 hρ1
  have hconvm : AEStronglyMeasurable (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) μ :=
    hρm.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hh
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hpt hconvm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hpt hh]
  refine ENNReal.rpow_le_rpow ?_ (one_div_nonneg.mpr (zero_le_one.trans hp0))
  calc ∫⁻ x, ‖(ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) x‖ₑ ^ p.toReal ∂μ
      ≤ ∫⁻ x, ∫⁻ t, ‖ρ t‖ₑ * ‖h (x - t)‖ₑ ^ p.toReal ∂μ ∂μ :=
        lintegral_mono (enorm_convolution_rpow_le hp0 hρen hhen hmass)
    _ = ∫⁻ t, ∫⁻ x, ‖ρ t‖ₑ * ‖h (x - t)‖ₑ ^ p.toReal ∂μ ∂μ :=
        lintegral_lintegral_swap (hρen.comp_snd.mul
          ((hhen.pow_const _).comp_quasiMeasurePreserving
            (quasiMeasurePreserving_sub_of_right_invariant μ μ)))
    _ = ∫⁻ t, ‖ρ t‖ₑ * ∫⁻ x, ‖h x‖ₑ ^ p.toReal ∂μ ∂μ := by
        refine lintegral_congr fun t => ?_
        have hm : AEMeasurable (fun x => ‖h (x - t)‖ₑ ^ p.toReal) μ :=
          (hhen.pow_const _).comp_quasiMeasurePreserving
            (measurePreserving_sub_right μ t).quasiMeasurePreserving
        rw [lintegral_const_mul'' _ hm,
          lintegral_sub_right_eq_self (fun z => ‖h z‖ₑ ^ p.toReal) t]
    _ = ∫⁻ x, ‖h x‖ₑ ^ p.toReal ∂μ := by rw [lintegral_mul_const'' _ hρen, hmass, one_mul]

/-- Young's inequality restricted to a set `s` on the left, bounded by the full `Lᵖ` norm. -/
theorem eLpNorm_convolution_restrict_le_of_integral_eq_one {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hpt : p ≠ ∞) {ρ : E → ℝ}
    (hρ0 : 0 ≤ ρ) (hρm : AEStronglyMeasurable ρ μ) (hρ1 : ∫ y, ρ y ∂μ = 1) {h : E → F}
    (hh : AEStronglyMeasurable h μ) (s : Set E) :
    eLpNorm (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) p (μ.restrict s) ≤ eLpNorm h p μ :=
  le_trans (eLpNorm_mono_measure _ Measure.restrict_le_self)
    (eLpNorm_convolution_le_of_integral_eq_one hp hpt hρ0 hρm hρ1 hh)

/-- A finite quantity times a small enough number is below any positive finite bound. -/
private theorem exists_pos_mul_ofReal_le {A η : ℝ≥0∞} (hA : A ≠ ∞) (hη : 0 < η)
    (hηtop : η ≠ ∞) : ∃ ε : ℝ, 0 < ε ∧ A * ENNReal.ofReal ε ≤ η := by
  have hA1top : A + 1 ≠ ∞ := by simp [hA]
  have hA1pos : A + 1 ≠ 0 := by positivity
  refine ⟨(η / (A + 1)).toReal, ENNReal.toReal_pos (ENNReal.div_pos hη.ne' hA1top).ne'
    (ENNReal.div_ne_top hηtop hA1pos), ?_⟩
  rw [ENNReal.ofReal_toReal (ENNReal.div_ne_top hηtop hA1pos)]
  calc A * (η / (A + 1)) ≤ (A + 1) * (η / (A + 1)) := by gcongr; exact le_self_add
    _ ≤ η := ENNReal.mul_div_le

/-- **Middle `3ε` term.** For a continuous compactly supported `w`, the mollifications
`ρᵢ ⋆ w` converge to `w` in `Lᵖ` as the outer bump radii shrink. The convolutions are
uniformly close to `w` on the fixed compact `closedBall 0 1 + tsupport w` (uniform continuity
of `w` plus `ContDiffBump.dist_normed_convolution_le`), and the `Lᵖ` seminorm of a uniformly
small function on a fixed finite-measure set is small. This needs only `rOut → 0`, not a bound
on the ratio of the radii. -/
private theorem tendsto_eLpNorm_normed_convolution_sub_of_continuous [CompleteSpace F]
    {p : ℝ≥0∞} {w : E → F} (hwc : Continuous w) (hwcs : HasCompactSupport w) {ι : Type*}
    {l : Filter ι}
    {φ : ι → ContDiffBump (0 : E)} (hφ : Filter.Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    Filter.Tendsto (fun i => eLpNorm
      ((φ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] w - w) p μ) l (𝓝 0) := by
  have hunif : UniformContinuous w := hwcs.uniformContinuous_of_continuous hwc
  set S1 := closedBall (0 : E) 1 + tsupport w with hS1def
  have hS1cpt : IsCompact S1 := (isCompact_closedBall _ _).add hwcs
  have hAtop : μ S1 ^ p.toReal⁻¹ ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hS1cpt.measure_lt_top.ne
  have htsuppS1 : tsupport w ⊆ S1 := fun y hy => by
    simpa using Set.add_mem_add (mem_closedBall_self (x := (0 : E)) zero_le_one) hy
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ∞ with rfl | hηtop
  · exact Filter.Eventually.of_forall fun _ => le_top
  obtain ⟨ε, hε0, hAε⟩ := exists_pos_mul_ofReal_le hAtop hη hηtop
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.mp hunif ε hε0
  filter_upwards [Metric.tendsto_nhds.mp hφ δ hδ0, Metric.tendsto_nhds.mp hφ 1 one_pos]
    with i hiδ hi1
  have hrδ : (φ i).rOut < δ := by
    rwa [Real.dist_0_eq_abs, abs_of_pos (φ i).rOut_pos] at hiδ
  have hr1 : (φ i).rOut < 1 := by
    rwa [Real.dist_0_eq_abs, abs_of_pos (φ i).rOut_pos] at hi1
  have hpt' : ∀ x₀, dist (((φ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] w) x₀) (w x₀)
      ≤ ε := fun x₀ =>
    (φ i).dist_normed_convolution_le hwc.aestronglyMeasurable fun x hx =>
      (hδ (lt_trans (mem_ball.1 hx) hrδ)).le
  have hsuppconv : Function.support ((φ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] w)
      ⊆ S1 := by
    refine (support_convolution_subset _).trans (Set.add_subset_add ?_ (subset_tsupport w))
    rw [(φ i).support_normed_eq]
    exact ball_subset_closedBall.trans (closedBall_subset_closedBall hr1.le)
  have hsupp : Function.support ((φ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] w - w)
      ⊆ S1 := fun x hx => by
    by_contra hxS1
    refine Function.mem_support.mp hx ?_
    rw [Pi.sub_apply, image_eq_zero_of_notMem_tsupport fun hxt => hxS1 (htsuppS1 hxt),
      Function.notMem_support.mp fun hxs => hxS1 (hsuppconv hxs), sub_zero]
  have hdm : AEStronglyMeasurable
      ((φ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] w - w) μ :=
    ((contDiff_normed_convolution (φ i) hwc.locallyIntegrable).continuous.sub
      hwc).aestronglyMeasurable
  calc eLpNorm ((φ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] w - w) p μ
      = eLpNorm ((φ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] w - w) p (μ.restrict S1) :=
        (eLpNorm_restrict_eq_of_support_subset hdm hsupp).symm
    _ ≤ (μ.restrict S1) Set.univ ^ p.toReal⁻¹ * ENNReal.ofReal ε :=
        eLpNorm_le_of_ae_bound hdm.restrict (Filter.Eventually.of_forall fun x => by
          rw [Pi.sub_apply, ← dist_eq_norm]; exact hpt' x)
    _ = μ S1 ^ p.toReal⁻¹ * ENNReal.ofReal ε := by rw [Measure.restrict_apply_univ]
    _ ≤ η := hAε

/-- **The `3ε` decomposition.** For `w` and `h` in `Lᵖ`, a continuous unit-mass kernel `ρ` of
compact support satisfies `‖ρ ⋆ h - h‖_p ≤ ‖ρ ⋆ w - w‖_p + 2 ‖h - w‖_p`, by Young's inequality
for `ρ ⋆ (h - w)`. -/
private theorem eLpNorm_convolution_sub_le {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {ρ : E → ℝ}
    {h w : E → F} (hρ0 : 0 ≤ ρ) (hρcont : Continuous ρ) (hρcs : HasCompactSupport ρ)
    (hρ1 : ∫ y, ρ y ∂μ = 1) (hh : MemLp h p μ) (hw : MemLp w p μ) :
    eLpNorm (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h - h) p μ
      ≤ eLpNorm (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] w - w) p μ
        + 2 * eLpNorm (h - w) p μ := by
  have hCE : ∀ f : E → F, LocallyIntegrable f μ →
      ConvolutionExists ρ f (ContinuousLinearMap.lsmul ℝ ℝ) μ := fun f hf =>
    hρcs.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hρcont hf
  have hadd : ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h
      = ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (h - w)
        + ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] w := by
    have := (hCE _ ((hh.sub hw).locallyIntegrable hp)).distrib_add
      (hCE _ (hw.locallyIntegrable hp))
    rwa [show (h - w) + w = h from sub_add_cancel h w] at this
  have hfun : ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h - h
      = ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (h - w)
        + ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] w - w) + (w - h)) := by
    rw [hadd]; abel
  rw [hfun]
  calc _ ≤ eLpNorm (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (h - w)) p μ
        + (eLpNorm (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] w - w) p μ
          + eLpNorm (w - h) p μ) :=
        (eLpNorm_add_le hp).trans (add_le_add le_rfl (eLpNorm_add_le hp))
    _ ≤ eLpNorm (h - w) p μ
        + (eLpNorm (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] w - w) p μ
          + eLpNorm (h - w) p μ) := by
        rw [eLpNorm_sub_comm w h]
        exact add_le_add (eLpNorm_convolution_le_of_integral_eq_one hp hpt hρ0
          hρcont.aestronglyMeasurable hρ1 (hh.sub hw).aestronglyMeasurable) le_rfl
    _ = _ := by ring

/-- **`Lᵖ` convergence of mollifications.** For `1 ≤ p < ∞`, an `Lᵖ` function `h` and a family
of normed bumps whose outer radii tend to `0` along a filter, the mollifications `ρᵢ ⋆ h`
converge to `h` in `Lᵖ`. -/
theorem tendsto_eLpNorm_normed_convolution_sub [CompleteSpace F] {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hpt : p ≠ ∞)
    {h : E → F} (hh : MemLp h p μ) {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : E)}
    (hφ : Filter.Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    Filter.Tendsto (fun i => eLpNorm
      ((φ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h - h) p μ) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ∞ with rfl | hηtop
  · exact Filter.Eventually.of_forall fun _ => le_top
  set δ : ℝ := η.toReal / 3 with hδdef
  have hδ0 : 0 < δ := by have := ENNReal.toReal_pos hη.ne' hηtop; positivity
  obtain ⟨w, hwcs, hwsmooth, hwle⟩ := hh.exist_eLpNorm_sub_le hpt hp hδ0
  have hwc : Continuous w := hwsmooth.continuous
  have hwml : MemLp w p μ := hwc.memLp_of_hasCompactSupport hwcs
  filter_upwards [ENNReal.tendsto_nhds_zero.mp
    (tendsto_eLpNorm_normed_convolution_sub_of_continuous (μ := μ) hwc hwcs hφ) (ENNReal.ofReal δ)
    (ENNReal.ofReal_pos.mpr hδ0)] with i hi
  refine (eLpNorm_convolution_sub_le hp hpt (fun x => (φ i).nonneg_normed x)
    ((φ i).contDiff_normed (n := 1)).continuous (φ i).hasCompactSupport_normed
    (φ i).integral_normed (μ := μ) hh hwml).trans ?_
  calc _ ≤ ENNReal.ofReal δ + 2 * ENNReal.ofReal δ :=
        add_le_add hi (mul_le_mul' le_rfl hwle)
    _ = η := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add hδ0.le (by positivity),
          show δ + 2 * δ = η.toReal from by rw [hδdef]; ring, ENNReal.ofReal_toReal hηtop]

end Young

/-! ### Real-valued statements with the kernel on the right -/

section RealKernelRight

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Convolution against scalar multiplication is commutative. -/
theorem convolution_lsmul_comm {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd G] [MeasurableNeg G] {μ : Measure G} [μ.IsAddLeftInvariant]
    [μ.IsNegInvariant] (f g : G → ℝ) :
    f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g = g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f := by
  rw [← convolution_flip]
  congr 1
  exact ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => mul_comm b a

/-- **Young's `Lᵖ` inequality for a probability kernel**, with the kernel on the right:
`‖h ⋆ ρ‖_{Lᵖ} ≤ ‖h‖_{Lᵖ}` for `1 ≤ p`, `ρ ≥ 0` and `∫ ρ = 1`. -/
theorem eLpNorm_convolution_le {p : ℝ} (hp : 1 ≤ p) {ρ : E → ℝ} (hρ0 : 0 ≤ ρ)
    (hρm : AEStronglyMeasurable ρ μ) (hρ1 : ∫ y, ρ y ∂μ = 1) {h : E → ℝ}
    (hh : MemLp h (ENNReal.ofReal p) μ) :
    eLpNorm (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] ρ) (ENNReal.ofReal p) μ
      ≤ eLpNorm h (ENNReal.ofReal p) μ := by
  rw [convolution_lsmul_comm]
  exact eLpNorm_convolution_le_of_integral_eq_one
    (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp) ENNReal.ofReal_ne_top
    hρ0 hρm hρ1 hh.aestronglyMeasurable

/-- The mollification of a locally integrable function is smooth, with the kernel on the
right. -/
theorem contDiff_convolution_normed (ρ : ContDiffBump (0 : E)) {h : E → ℝ}
    (hh : LocallyIntegrable h μ) :
    ContDiff ℝ (⊤ : ℕ∞) (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] ρ.normed μ) := by
  rw [convolution_lsmul_comm]
  exact contDiff_normed_convolution ρ hh

/-- The mollification of a compactly supported function has compact support, with the kernel
on the right. -/
theorem hasCompactSupport_convolution_normed (ρ : ContDiffBump (0 : E)) {h : E → ℝ}
    (hh : HasCompactSupport h) :
    HasCompactSupport (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] ρ.normed μ) := by
  rw [convolution_lsmul_comm]
  exact hasCompactSupport_normed_convolution ρ hh

/-- **Mollifications converge in `L¹`.** The standard mollifications of an integrable function
converge to it in `L¹`. -/
theorem tendsto_eLpNorm_one_mollifier_convolution_sub {δ : ℝ} (hδ : 0 < δ) {h : E → ℝ}
    (hh : Integrable h μ) :
    Filter.Tendsto (fun n => eLpNorm (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
      (mollifier hδ n : ContDiffBump (0 : E)).normed μ - h) 1 μ) Filter.atTop (𝓝 0) := by
  simp only [convolution_lsmul_comm h]
  exact tendsto_eLpNorm_normed_convolution_sub le_rfl ENNReal.one_ne_top
    (memLp_one_iff_integrable.2 hh) (tendsto_rOut_mollifier hδ)

end RealKernelRight

variable {d : ℕ}

/-- **`Lᵖ` convergence of mollifications** (the form the extension files use). For `1 ≤ p`, an
`Lᵖ` function `h`, and a family of normalised bumps whose outer radii tend to `0` (with a
bounded inner/outer ratio), the mollifications `h ⋆ ρ_ε` converge to `h` in `Lᵖ`. -/
theorem tendsto_eLpNorm_convolution_sub {p : ℝ} (hp : 1 ≤ p)
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hh : MemLp h (ENNReal.ofReal p) volume)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin d))} {K : ℝ}
    (hφ : Filter.Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (_hK : ∀ᶠ i in l, (φ i).rOut ≤ K * (φ i).rIn) :
    Filter.Tendsto
      (fun i => eLpNorm
          (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume) - h)
          (ENNReal.ofReal p) volume) l (𝓝 0) := by
  simp only [convolution_lsmul_comm h]
  exact tendsto_eLpNorm_normed_convolution_sub
    (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp) ENNReal.ofReal_ne_top hh hφ

/-- **Lowering an exponent on a finite measure space costs a constant.** For `0 < p ≤ q` there
is `A` with `‖f‖_{Lᵖ} ≤ A ‖f‖_{Lq}`, namely `μ(univ)^{1/p - 1/q}`. -/
theorem exists_const_eLpNorm_le_of_le {α E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ] [NormedAddCommGroup E] {p q : ℝ≥0∞} (hp : p ≠ 0) (hpq : p ≤ q) :
    ∃ A : ℝ≥0, ∀ f : α → E, AEStronglyMeasurable f μ → eLpNorm f p μ ≤ A * eLpNorm f q μ := by
  have he : 0 ≤ 1 / p.toReal - 1 / q.toReal := by
    rcases eq_or_ne q ⊤ with rfl | hq
    · simp
    · rw [sub_nonneg]
      exact one_div_le_one_div_of_le (ENNReal.toReal_pos hp (ne_top_of_le_ne_top hq hpq))
        (ENNReal.toReal_mono hq hpq)
  refine ⟨(μ univ ^ (1 / p.toReal - 1 / q.toReal)).toNNReal, fun f hf => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.rpow_ne_top_of_nonneg he (measure_ne_top μ _)), mul_comm]
  exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hf

/-- A function bounded by `B` together with its `d` partial derivatives, each bounded by `B`,
has total `a + ∑ k, b k` at most `(d + 1) B`. -/
theorem add_sum_le_of_le {d : ℕ} {a B : ℝ≥0∞} {b : Fin d → ℝ≥0∞} (ha : a ≤ B)
    (hb : ∀ k, b k ≤ B) : a + ∑ k, b k ≤ (d + 1) * B := by
  calc a + ∑ k, b k ≤ B + ∑ _k : Fin d, B := add_le_add ha (Finset.sum_le_sum fun k _ => hb k)
    _ = (d + 1) * B := by simp [add_mul, add_comm]

/-- The sum of `d` seminorms, each at most `B`, is at most `d * B`, read in `ℝ≥0`. -/
theorem sum_toNNReal_eLpNorm_le {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {g : Fin d → α → ℝ} {p : ℝ≥0∞} {B : ℝ≥0} (h : ∀ k, eLpNorm (g k) p μ ≤ B) :
    ∑ k, (eLpNorm (g k) p μ).toNNReal ≤ d * B := by
  calc ∑ k, (eLpNorm (g k) p μ).toNNReal ≤ ∑ _k : Fin d, B :=
        Finset.sum_le_sum fun k _ =>
          (ENNReal.toNNReal_mono ENNReal.coe_ne_top (h k)).trans_eq (ENNReal.toNNReal_coe B)
    _ = d * B := by simp

/-- **A continuous linear map into `Lp` from an almost everywhere linear family of functions.**
The family `T` sends a point of a normed space to a function in `Lp`, linearly up to null sets,
with `‖T x‖_p ≤ C ‖x‖`. -/
def lpCLM {X α F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : X → α → F) (hT : ∀ x, MemLp (T x) p μ)
    (hadd : ∀ x y, T (x + y) =ᵐ[μ] T x + T y) (hsmul : ∀ (c : ℝ) x, T (c • x) =ᵐ[μ] c • T x)
    (C : ℝ≥0) (hC : ∀ x, eLpNorm (T x) p μ ≤ C * ‖x‖ₑ) : X →L[ℝ] Lp F p μ :=
  LinearMap.mkContinuous
    { toFun := fun x => (hT x).toLp (T x)
      map_add' := fun x y => by
        rw [MemLp.toLp_congr _ ((hT x).add (hT y)) (hadd x y), MemLp.toLp_add]
      map_smul' := fun c x => by
        rw [MemLp.toLp_congr _ ((hT x).const_smul c) (hsmul c x), MemLp.toLp_const_smul]
        rfl }
    C (fun x => by
      change ‖(hT x).toLp (T x)‖ ≤ C * ‖x‖
      rw [Lp.norm_toLp]
      refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg C.coe_nonneg (norm_nonneg x))
        ((hC x).trans_eq ?_)
      rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal, ofReal_norm])

/-- `lpCLM T` agrees almost everywhere with the family it is built from. -/
theorem coeFn_lpCLM {X α F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {T : X → α → F}
    {hT : ∀ x, MemLp (T x) p μ} {hadd : ∀ x y, T (x + y) =ᵐ[μ] T x + T y}
    {hsmul : ∀ (c : ℝ) x, T (c • x) =ᵐ[μ] c • T x} {C : ℝ≥0}
    {hC : ∀ x, eLpNorm (T x) p μ ≤ C * ‖x‖ₑ} (x : X) :
    ⇑(lpCLM T hT hadd hsmul C hC x) =ᵐ[μ] T x :=
  MemLp.coeFn_toLp (hT x)

/-- **Inclusion of `Lq` into `Lp` on a finite measure space**, for `p ≤ q`. -/
def lpInclusion {α F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {m : MeasurableSpace α}
    (μ : Measure α) [IsFiniteMeasure μ]
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q) : Lp F q μ →L[ℝ] Lp F p μ :=
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos (Fact.out : 1 ≤ p)).ne'
  lpCLM (fun f : Lp F q μ => ⇑f) (fun f => (Lp.memLp f).mono_exponent hpq)
    (fun f g => Lp.coeFn_add f g) (fun c f => Lp.coeFn_smul c f)
    (exists_const_eLpNorm_le_of_le (μ := μ) (E := F) hp0 hpq).choose fun f =>
    ((exists_const_eLpNorm_le_of_le (μ := μ) (E := F) hp0 hpq).choose_spec f
      (Lp.aestronglyMeasurable f)).trans_eq (by rw [Lp.enorm_def])

/-- The inclusion of `Lq` into `Lp` is the identity on representatives. -/
theorem coeFn_lpInclusion {α F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ]
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q) (f : Lp F q μ) :
    ⇑(lpInclusion μ hpq f) =ᵐ[μ] ⇑f :=
  MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent hpq)

/-- The inclusion of `Lq` into `Lp` is injective. -/
theorem lpInclusion_injective {α F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ] {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] (hpq : p ≤ q) :
    Function.Injective (lpInclusion (F := F) μ hpq) := fun f g h =>
  Lp.ext ((coeFn_lpInclusion μ hpq f).symm.trans
    ((Lp.ext_iff.mp h).trans (coeFn_lpInclusion μ hpq g)))

end EllipticPdes.Embedding
