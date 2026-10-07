/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Analysis.Mollifier
public import EllipticPdes.Sobolev.WeakDeriv
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# A continuous weak derivative is a classical derivative

On an open set `Ω` of a finite-dimensional real normed space, a function `u` that is continuous
on `Ω`, with a weak Fréchet derivative `G` continuous on `Ω`, is Fréchet differentiable at every
point of `Ω`, with derivative `G`.

The proof mollifies. Near a point `x`, `u` and `G` are cut to a compact ball `K ⊆ Ω` around `x`
and convolved with normed bumps `ρₙ` of radius tending to zero. Each `ρₙ ⋆ u` is differentiable
with derivative `ρₙ ⋆ G` on a smaller ball, because the derivative of a convolution falls on the
bump and the weak derivative moves it back onto `u`. Both mollifications converge uniformly on
the smaller ball, since `u` and `G` are uniformly continuous on `K`, and
`hasFDerivAt_of_tendstoUniformlyOn` identifies the derivative of the limit.

## Main declarations

* `EllipticPdes.tendstoUniformlyOn_normed_convolution`: mollifications of a function continuous
  on a compact set converge uniformly on any set whose closed thickening stays in it.
* `EllipticPdes.HasWeakFDerivOn.hasFDerivAt_convolution`: the derivative of a mollification is
  the mollification of the weak derivative.
* `EllipticPdes.HasWeakFDerivOn.hasFDerivAt`: a continuous weak derivative is a Fréchet
  derivative.
-/

@[expose] public section

open MeasureTheory Set Metric Filter TopologicalSpace ContinuousLinearMap
open scoped Convolution Topology

noncomputable section

namespace EllipticPdes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Uniform convergence of mollifications.** Let `h` be continuous on a compact set `K`, and
`s` a set whose closed `σ`-thickening lies in `K`. Mollifications of `h` by normed bumps of
outer radius at most `σ` and tending to zero converge to `h` uniformly on `s`. -/
theorem tendstoUniformlyOn_normed_convolution {ι : Type*} {l : Filter ι} {K s : Set E}
    (hK : IsCompact K) {h : E → F} (hh : ContinuousOn h K) (hm : AEStronglyMeasurable h μ)
    {σ : ℝ} (hs : cthickening σ s ⊆ K) {φ : ι → ContDiffBump (0 : E)} (hφσ : ∀ i, (φ i).rOut ≤ σ)
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    TendstoUniformlyOn (fun i => (φ i).normed μ ⋆[lsmul ℝ ℝ, μ] h) h l s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hh) (ε / 2) (half_pos hε)
  filter_upwards [hφ.eventually (gt_mem_nhds hδ)] with i hi y hy
  have hyK : y ∈ K := hs (self_subset_cthickening s hy)
  have hnear : ∀ z ∈ ball y (φ i).rOut, dist (h z) (h y) ≤ ε / 2 := fun z hz =>
    (hδε z (hs (mem_cthickening_of_dist_le z y σ s hy ((mem_ball.1 hz).le.trans (hφσ i)))) y hyK
      ((mem_ball.1 hz).trans hi)).le
  rw [dist_comm]
  exact ((φ i).dist_normed_convolution_le hm hnear).trans_lt (half_lt_self hε)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace F] in
/-- A smooth function times the extension by zero of `f` outside `K` is the smooth function
times `f`, when the smooth function vanishes off `K`. -/
theorem smul_indicator_eq_of_tsupport_subset {K : Set E} {ψ : E → ℝ} (hψ : tsupport ψ ⊆ K)
    (f : E → F) (t : E) : ψ t • K.indicator f t = ψ t • f t := by
  by_cases ht : t ∈ K
  · rw [indicator_of_mem ht]
  · rw [image_eq_zero_of_notMem_tsupport fun h => ht (hψ h), zero_smul, zero_smul]

omit [CompleteSpace F] in
/-- The normed bump reflected through `y` is supported in the closed ball of radius `rOut`
around `y`. -/
theorem tsupport_normed_sub_subset (ρ : ContDiffBump (0 : E)) (y : E) :
    tsupport (fun t => ρ.normed μ (y - t)) ⊆ closedBall y ρ.rOut := by
  refine closure_minimal (fun t ht => ?_) isClosed_closedBall
  have : y - t ∈ ball (0 : E) ρ.rOut := ρ.support_normed_eq (μ := μ) ▸ ht
  simpa [dist_comm, dist_eq_norm] using (mem_ball_zero_iff.1 this).le

variable {Ω : Opens E} {u : E → F} {G : E → E →L[ℝ] F}

omit [CompleteSpace F] in
/-- **The derivative of a mollification is the mollification of the derivative.** Let the
extensions by zero of `u` and `G` outside a set `K` be locally integrable, and suppose the
integration by parts identity `∫ ∂ᵥψ • u = -∫ ψ • G v` holds against every `C^∞` function `ψ`
with compact support in `K`.
If the closed ball of radius `ρ.rOut` around `y` lies in `K`, then the mollification of the
extension of `u` by zero outside `K` has derivative at `y` the mollification of the extension of
`G`. -/
theorem hasFDerivAt_convolution_of_forall_integral_eq {K : Set E}
    (hu : LocallyIntegrable (K.indicator u) μ) (hG : LocallyIntegrable (K.indicator G) μ)
    (hw : ∀ (v : E) (ψ : E → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ K →
      ∫ t, fderiv ℝ ψ t v • u t ∂μ = -∫ t, ψ t • G t v ∂μ)
    (ρ : ContDiffBump (0 : E)) {y : E} (hy : closedBall y ρ.rOut ⊆ K) :
    HasFDerivAt (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] K.indicator u)
      ((ρ.normed μ ⋆[lsmul ℝ ℝ, μ] K.indicator G) y) y := by
  have hρd : ∀ n : ℕ∞, ContDiff ℝ n (ρ.normed μ) := fun n => ρ.contDiff_normed
  -- The bump reflected through `y`, a test function on `Ω`.
  set ψ : E → ℝ := fun t => ρ.normed μ (y - t) with hψ_def
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := (hρd ⊤).comp (contDiff_const.sub contDiff_id)
  have hψs : tsupport ψ ⊆ K := (tsupport_normed_sub_subset ρ y).trans hy
  have hψc : HasCompactSupport ψ :=
    (isCompact_closedBall y ρ.rOut).of_isClosed_subset (isClosed_tsupport ψ)
      (tsupport_normed_sub_subset ρ y)
  have hψd : ∀ t v, fderiv ℝ ψ t v = -fderiv ℝ (ρ.normed μ) (y - t) v := fun t v => by
    have h : HasFDerivAt ψ ((fderiv ℝ (ρ.normed μ) (y - t)).comp (-ContinuousLinearMap.id ℝ E))
        t := ((hρd 1).differentiable one_ne_zero (y - t)).hasFDerivAt.comp t
      ((hasFDerivAt_id t).const_sub y)
    rw [h.fderiv]
    simp
  have hL : ∀ v, (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] K.indicator G) y v = ∫ t, ψ t • G t v ∂μ := by
    intro v
    rw [← convolution_flip, convolution_def, integral_apply
      ((ρ.hasCompactSupport_normed (μ := μ)).convolutionExists_right
        (lsmul ℝ ℝ : ℝ →L[ℝ] (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F).flip hG (hρd 0).continuous y)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simpa using congrArg (fun A : E →L[ℝ] F => A v)
      (smul_indicator_eq_of_tsupport_subset hψs G t)
  have hR : ∀ v, ((K.indicator u) ⋆[(lsmul ℝ ℝ).flip, μ] fun a => fderiv ℝ (ρ.normed μ) a v) y =
      -∫ t, fderiv ℝ ψ t v • u t ∂μ := by
    intro v
    rw [convolution_def, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have hs' : tsupport (fun t => fderiv ℝ ψ t v) ⊆ K :=
      (tsupport_fderiv_apply_subset ℝ v).trans hψs
    have h := smul_indicator_eq_of_tsupport_subset hs' u t
    simp only [hψd, neg_smul, neg_inj] at h
    simp [hψd, h]
  rw [← convolution_flip]
  convert (ρ.hasCompactSupport_normed (μ := μ)).hasFDerivAt_convolution_right
    (lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip hu (hρd 1) y using 1
  ext v
  rw [hL, convolution_precompR_apply _ hu (ρ.hasCompactSupport_normed.fderiv ℝ)
    ((hρd 1).continuous_fderiv one_ne_zero), hR, hw v ψ hψ hψc hψs,
    neg_neg]

omit [CompleteSpace F] in
/-- **The derivative of a mollification is the mollification of the weak derivative.** Let `G`
be the weak Fréchet derivative of `u` on `Ω`, and `K ⊆ Ω` a measurable set on which `u` and `G`
are integrable. If the closed ball of radius `ρ.rOut` around `y` lies in `K`, then the
mollification of the extension of `u` by zero outside `K` has derivative at `y` the
mollification of the extension of `G`. -/
theorem HasWeakFDerivOn.hasFDerivAt_convolution (hw : HasWeakFDerivOn Ω u G μ)
    {K : Set E} (hKm : MeasurableSet K) (hKΩ : K ⊆ Ω) (hu : IntegrableOn u K μ)
    (hG : IntegrableOn G K μ) (ρ : ContDiffBump (0 : E)) {y : E} (hy : closedBall y ρ.rOut ⊆ K) :
    HasFDerivAt (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] K.indicator u)
      ((ρ.normed μ ⋆[lsmul ℝ ℝ, μ] K.indicator G) y) y :=
  hasFDerivAt_convolution_of_forall_integral_eq (hu.integrable_indicator hKm).locallyIntegrable
    (IntegrableOn.integrable_indicator (ε' := E →L[ℝ] F) hG hKm).locallyIntegrable
    (fun v _ hψ hψc hψs => (hw v).integral_eq hψ hψc (hψs.trans hKΩ)) ρ hy

omit [CompleteSpace F] [μ.IsAddHaarMeasure] in
/-- **A weak Fréchet derivative is locally integrable as an operator-valued function.** If
every directional component `x ↦ G x v` is locally integrable on `Ω`, so is `G`, since on a
finite-dimensional space `G x` is the sum of its values on a basis against the coordinate
functionals. -/
theorem HasWeakFDerivOn.locallyIntegrableOn (hw : HasWeakFDerivOn Ω u G μ) :
    LocallyIntegrableOn G Ω μ := by
  classical
  set b := Module.finBasis ℝ E
  set c : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ := fun i =>
    LinearMap.toContinuousLinearMap (b.coord i)
  have hG : G = fun x => ∑ i, (c i).smulRight (G x (b i)) := by
    funext x
    ext v
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply]
    conv_lhs => rw [← b.sum_repr v, map_sum]
    simp [c]
  have key : LocallyIntegrableOn (fun x => ∑ i, (c i).smulRight (G x (b i))) Ω μ := by
    refine (locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed).2 fun K hK hKc => ?_
    have hint : ∀ i ∈ Finset.univ, Integrable (fun x => (c i).smulRight (G x (b i)))
        (μ.restrict K) := fun i _ => by
      have hi := (hw (b i)).locallyIntegrableOn.integrableOn_compact_subset hK hKc
      refine Integrable.mono' (hi.norm.const_mul ‖c i‖)
        ((smulRightL ℝ E F (c i)).continuous.comp_aestronglyMeasurable hi.aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      simp
    exact integrable_finsetSum (μ := μ.restrict K)
      (f := fun i x => (c i).smulRight (G x (b i))) Finset.univ hint
  rwa [← hG] at key

/-- **A continuous weak derivative is a Fréchet derivative.** If `u` is continuous on the open
set `Ω` and has a weak Fréchet derivative `G` continuous on `Ω`, then `u` is differentiable at
every point `x` of `Ω`, with derivative `G x`. -/
theorem HasWeakFDerivOn.hasFDerivAt (hw : HasWeakFDerivOn Ω u G μ) (hu : ContinuousOn u Ω)
    (hG : ContinuousOn G Ω) {x : E} (hx : x ∈ Ω) : HasFDerivAt u (G x) x := by
  obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx
  have hr : 0 < R / 4 := by positivity
  set K := closedBall x (R / 4 + R / 4)
  have hK : IsCompact K := isCompact_closedBall x _
  have hKΩ : K ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hRΩ
  have hthick : cthickening (R / 4) (ball x (R / 4)) ⊆ K :=
    (cthickening_subset_of_subset _ ball_subset_closedBall).trans
      (cthickening_closedBall hr.le hr.le x).le
  have hsub : ∀ n, ∀ y ∈ ball x (R / 4), closedBall y (mollifier (E := E) hr n).rOut ⊆ K :=
    fun n y hy => closedBall_subset_closedBall' (by
      linarith [rOut_mollifier_le (E := E) hr n, (mem_ball.1 hy).le])
  have hKm := hK.measurableSet
  have huK : IntegrableOn u K μ := (hu.mono hKΩ).integrableOn_compact hK
  have hGK : IntegrableOn G K μ := (hG.mono hKΩ).integrableOn_compact hK
  have hGi : Integrable (K.indicator G) μ :=
    IntegrableOn.integrable_indicator (ε' := E →L[ℝ] F) hGK hKm
  have hvals := (tendstoUniformlyOn_normed_convolution (μ := μ) hK
    ((hu.mono hKΩ).congr fun y hy => indicator_of_mem hy u)
    (huK.integrable_indicator hKm).aestronglyMeasurable hthick (rOut_mollifier_le hr)
    (tendsto_rOut_mollifier hr)).congr_right fun y hy => indicator_of_mem (hthick
      (self_subset_cthickening _ hy)) u
  have hders := (tendstoUniformlyOn_normed_convolution (μ := μ) hK
    ((hG.mono hKΩ).congr fun y hy => indicator_of_mem hy G)
    hGi.aestronglyMeasurable hthick (rOut_mollifier_le hr)
    (tendsto_rOut_mollifier hr)).congr_right fun y hy => indicator_of_mem (hthick
      (self_subset_cthickening _ hy)) G
  exact hasFDerivAt_of_tendstoUniformlyOn isOpen_ball hders
    (fun n y hy => hw.hasFDerivAt_convolution hKm hKΩ huK hGK _ (hsub n y hy))
    (fun y hy => hvals.tendsto_at hy) (mem_ball_self hr)

end EllipticPdes
