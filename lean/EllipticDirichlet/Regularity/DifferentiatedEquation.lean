/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticDirichlet.Regularity.Interior
import EllipticDirichlet.Regularity.CoeffC2
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The differentiated-equation integral identity

For `u ∈ H₀¹(Ω)` weakly solving `Lu = f` with `C²` principal coefficients, this file builds
towards the **differentiated-equation integral identity** of Evans, *Partial Differential
Equations* (2nd ed.), §6.3.2, Theorem 4: for a fixed direction `ℓ` and every smooth
compactly-supported test `φ` with `tsupport φ ⊆ V`,

```
∑_{i,j} ∫_V a_{ij} (∂ₖ∂ᵢu) ∂ⱼφ  +  ∑_{i,j} ∫_V (∂_ℓ a_{ij})(∂ᵢu) ∂ⱼφ  =  ∫_V f_ℓ · φ
```

with `f_ℓ` an explicit lower-order datum. The identity is stated in `HasWeakDerivOn`-style
integration by parts on plain `Lp ℝ 2 (volume.restrict V)` classes.

This file starts with the small calculus facts used repeatedly throughout the milestone: the
partial derivative of a smooth (resp. compactly supported) test function is again smooth
(resp. compactly supported), so `∂ⱼφ` is again an admissible `HasWeakDerivOn` test function,
and the pointwise Leibniz rule for `partialD` against a product.
-/

open MeasureTheory
open scoped RealInnerProductSpace Topology ENNReal Convolution

noncomputable section

namespace EllipticDirichlet.Regularity

open EllipticDirichlet.Sobolev

variable {d : ℕ}

/-! ### Test-function calculus -/

/-- The partial derivative of a `C^∞` function is `C^∞`. -/
theorem contDiff_partialD {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (partialD j φ) := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := (contDiff_infty_iff_fderiv.mp hφ).2
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => (fderiv ℝ φ x) (EuclideanSpace.single j 1))
  exact hf.clm_apply (contDiff_const (c := EuclideanSpace.single j (1 : ℝ)))

/-- The partial derivative of a compactly-supported function has compact support. -/
theorem hasCompactSupport_partialD {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : HasCompactSupport φ) (j : Fin d) : HasCompactSupport (partialD j φ) :=
  hφ.mono' ((subset_tsupport (partialD j φ)).trans (tsupport_partialD_subset j φ))

/-- `∂ⱼφ` is again an admissible `HasWeakDerivOn` test function on `V` when `φ` is. -/
theorem isTest_partialD {V : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ)
    (hV : tsupport φ ⊆ V) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (partialD j φ) ∧ HasCompactSupport (partialD j φ)
      ∧ tsupport (partialD j φ) ⊆ V :=
  ⟨contDiff_partialD hc j, hasCompactSupport_partialD hcs j,
    (tsupport_partialD_subset j φ).trans hV⟩

/- The pointwise Leibniz rule for `partialD` against a product already exists as
`partialD_mul` (`Regularity/Caccioppoli.lean`, transitively imported via `Interior`):
`partialD i (fun x => η x * φ x) = fun x => η x * partialD i φ x + partialD i η x * φ x`
for `η, φ` differentiable. It is mathematically the same identity with the two summands
commuted (`add_comm`), so it is reused here rather than redeclared under the same name. -/

/-! ### Coefficient mollification -/

/-- **Sup bound for a mollification.** If a continuous function `h` is bounded by `M` almost
everywhere and `ρ` is a non-negative continuous compactly supported kernel of unit mass, then the
convolution `h ⋆ ρ` is bounded by `M` at every point: the Lebesgue-null exceptional set for the
almost-everywhere bound is also null for the convolution integral. -/
private lemma abs_convolution_le
    {ρ : EuclideanSpace ℝ (Fin d) → ℝ} (hρ0 : 0 ≤ ρ) (hρc : Continuous ρ)
    (hρcs : HasCompactSupport ρ)
    (hρ1 : ∫ y, ρ y ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) = 1)
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hhc : Continuous h) {M : ℝ}
    (hM : ∀ᵐ t ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |h t| ≤ M)
    (x : EuclideanSpace ℝ (Fin d)) :
    |(h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x| ≤ M := by
  have hshift_c : Continuous (fun t => ρ (x - t)) :=
    hρc.comp (continuous_const.sub continuous_id)
  have hshift_cs : HasCompactSupport (fun t => ρ (x - t)) :=
    hρcs.comp_homeomorph (Homeomorph.subLeft x)
  have hval : (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x
      = ∫ t, h t * ρ (x - t) ∂volume := by
    rw [convolution_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have habs : Integrable (fun t => |h t| * ρ (x - t)) volume :=
    (hhc.abs.mul hshift_c).integrable_of_hasCompactSupport hshift_cs.mul_left
  have hintM : Integrable (fun t => M * ρ (x - t)) volume :=
    (continuous_const.mul hshift_c).integrable_of_hasCompactSupport hshift_cs.mul_left
  rw [hval]
  calc |∫ t, h t * ρ (x - t) ∂volume|
      ≤ ∫ t, |h t * ρ (x - t)| ∂volume := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun t => h t * ρ (x - t))
    _ = ∫ t, |h t| * ρ (x - t) ∂volume := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [abs_mul, abs_of_nonneg (hρ0 (x - t))]
    _ ≤ ∫ t, M * ρ (x - t) ∂volume := by
        refine integral_mono_ae habs hintM ?_
        filter_upwards [hM] with t ht
        exact mul_le_mul_of_nonneg_right ht (hρ0 (x - t))
    _ = M * ∫ t, ρ (x - t) ∂volume := integral_const_mul M _
    _ = M * 1 := by rw [integral_sub_left_eq_self ρ volume x, hρ1]
    _ = M := mul_one M

/-- **The derivative of a mollified `C¹` function is the mollification of its derivative.** For
`a ∈ C¹` and a smooth compactly supported kernel `ρ`, `∂_ℓ (a ⋆ ρ) = (∂_ℓ a) ⋆ ρ`. The derivative
first passes to the kernel (`∂_ℓ (a ⋆ ρ) = a ⋆ ∂_ℓ ρ`), and integration by parts in the
convolution variable moves it back onto `a`. -/
private lemma partialD_convolution_eq
    {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : ContDiff ℝ 1 a)
    {ρ : EuclideanSpace ℝ (Fin d) → ℝ} (hρcd : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρcs : HasCompactSupport ρ) (ℓ : Fin d) :
    partialD ℓ (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ)
      = (partialD ℓ a) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ := by
  have hρcd1 : ContDiff ℝ 1 ρ := hρcd.of_le (by exact_mod_cast le_top)
  have hρdiff : Differentiable ℝ ρ := hρcd.differentiable (by simp)
  have haLI : LocallyIntegrable a volume := ha.continuous.locallyIntegrable
  have hadiff : Differentiable ℝ a := ha.differentiable one_ne_zero
  have hdacont : Continuous (fun t => fderiv ℝ a t (EuclideanSpace.single ℓ 1)) :=
    (ha.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdρcont : Continuous (partialD ℓ ρ) := (contDiff_partialD hρcd ℓ).continuous
  funext x
  -- Step 1: the derivative passes to the kernel.
  have hderiv := hρcs.hasFDerivAt_convolution_right
    (L := ContinuousLinearMap.lsmul ℝ ℝ) haLI hρcd1 x
  have step2 : partialD ℓ (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x
      = (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] partialD ℓ ρ) x := by
    have hpd : partialD ℓ (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x
        = (fderiv ℝ (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x)
            (EuclideanSpace.single ℓ 1) := rfl
    have hprec := convolution_precompR_apply (𝕜 := ℝ)
      (L := ContinuousLinearMap.lsmul ℝ ℝ) haLI (hρcs.fderiv ℝ)
      (hρcd.continuous_fderiv (by simp)) x (EuclideanSpace.single ℓ 1)
    rw [hpd, hderiv.fderiv, hprec]
    rfl
  rw [step2]
  -- Step 2: integration by parts moves the derivative onto `a`.
  set G : EuclideanSpace ℝ (Fin d) → ℝ := fun t => ρ (x - t) with hG
  have hGdiff : Differentiable ℝ G :=
    hρdiff.comp (differentiable_id.const_sub x)
  have hGcont : Continuous G := hρcd.continuous.comp (continuous_const.sub continuous_id)
  have hshift_cs : HasCompactSupport G := hρcs.comp_homeomorph (Homeomorph.subLeft x)
  have hdρ_shift_cs : HasCompactSupport (fun t => (partialD ℓ ρ) (x - t)) :=
    (hasCompactSupport_partialD hρcs ℓ).comp_homeomorph (Homeomorph.subLeft x)
  have hGfd : ∀ t, fderiv ℝ G t (EuclideanSpace.single ℓ 1) = -(partialD ℓ ρ) (x - t) := by
    intro t
    have hfd : HasFDerivAt G ((fderiv ℝ ρ (x - t)).comp
        (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)))) t :=
      (hρdiff (x - t)).hasFDerivAt.comp t ((hasFDerivAt_id t).const_sub x)
    rw [hfd.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply, map_neg, partialD]
  -- integrability of the three integrands feeding the by-parts identity
  have hint_f'g : Integrable (fun t => fderiv ℝ a t (EuclideanSpace.single ℓ 1) * G t) volume :=
    (hdacont.mul hGcont).integrable_of_hasCompactSupport hshift_cs.mul_left
  have hint_fg : Integrable (fun t => a t * G t) volume :=
    (ha.continuous.mul hGcont).integrable_of_hasCompactSupport hshift_cs.mul_left
  have hfg'_eq : (fun t => a t * fderiv ℝ G t (EuclideanSpace.single ℓ 1))
      = fun t => a t * -(partialD ℓ ρ) (x - t) := funext fun t => by rw [hGfd t]
  have hint_fg' : Integrable (fun t => a t * fderiv ℝ G t (EuclideanSpace.single ℓ 1)) volume := by
    rw [hfg'_eq]
    exact (ha.continuous.mul ((hdρcont.comp (continuous_const.sub continuous_id)).neg))
      |>.integrable_of_hasCompactSupport hdρ_shift_cs.neg.mul_left
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := a) (g := G) (v := EuclideanSpace.single ℓ 1)
    hint_f'g hint_fg' hint_fg (fun t _ => hadiff t) (fun t _ => hGdiff t)
  -- rewrite both convolutions as integrals
  have hL : (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] partialD ℓ ρ) x
      = ∫ t, a t * partialD ℓ ρ (x - t) ∂volume := by
    rw [convolution_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hR : ((partialD ℓ a) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x
      = ∫ t, partialD ℓ a t * ρ (x - t) ∂volume := by
    rw [convolution_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [hL, hR]
  have h1 : ∫ t, a t * fderiv ℝ G t (EuclideanSpace.single ℓ 1) ∂volume
      = -∫ t, fderiv ℝ a t (EuclideanSpace.single ℓ 1) * G t ∂volume := hibp
  simp only [hGfd, mul_neg] at h1
  rw [integral_neg] at h1
  have h2 := neg_inj.mp h1
  simpa only [hG, partialD] using h2

/-- **Dominated-convergence engine for a mollified factor.** For a continuous factor `h` bounded
by `Mh` almost everywhere, an `L²` class `w`, and a continuous compactly supported `χ`, the set
integrals `∫_V w · (h ⋆ ρ_n) · χ` converge to `∫_V w · h · χ` as the bump radii shrink. The
mollification `h ⋆ ρ_n` is dominated by `Mh` everywhere and converges pointwise to `h`, so the
integrand is dominated by the `L¹(V)` function `|w · (Mh · χ)|` (Cauchy-Schwarz on the two `L²`
factors `w` and `Mh · χ`) and dominated convergence applies. -/
private lemma tendsto_setIntegral_mul_convolution
    {V : Set (EuclideanSpace ℝ (Fin d))} (_hVm : MeasurableSet V)
    (φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (hφrOut : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (𝓝 0))
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hhc : Continuous h) {Mh : ℝ}
    (hMh : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |h x| ≤ Mh)
    (w : Lp ℝ 2 (volume.restrict V))
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχc : Continuous χ) (hχcs : HasCompactSupport χ) :
    Filter.Tendsto
      (fun n => ∫ x in V, (w x : ℝ)
          * ((h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (φ n).normed volume) x * χ x))
      Filter.atTop
      (𝓝 (∫ x in V, (w x : ℝ) * (h x * χ x))) := by
  classical
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  have hLflip : (ContinuousLinearMap.lsmul ℝ ℝ).flip = ContinuousLinearMap.lsmul ℝ ℝ := by
    refine ContinuousLinearMap.ext fun p => ContinuousLinearMap.ext fun q => ?_
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    exact mul_comm q p
  have hhLI : LocallyIntegrable h volume := hhc.locallyIntegrable
  have hρ0 : ∀ n, (0 : EuclideanSpace ℝ (Fin d) → ℝ) ≤ (φ n).normed volume :=
    fun n x => (φ n).nonneg_normed x
  have hρc : ∀ n, Continuous ((φ n).normed volume) :=
    fun n => ((φ n).contDiff_normed : ContDiff ℝ 1 ((φ n).normed volume)).continuous
  have hρcs : ∀ n, HasCompactSupport ((φ n).normed volume) :=
    fun n => (φ n).hasCompactSupport_normed
  have hρ1 : ∀ n, ∫ y, (φ n).normed volume y ∂volume = 1 := fun n => (φ n).integral_normed
  have hbnd : ∀ n x,
      |(h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (φ n).normed volume) x| ≤ Mh :=
    fun n x => abs_convolution_le (hρ0 n) (hρc n) (hρcs n) (hρ1 n) hhc hMh x
  have hMh0 : 0 ≤ Mh := le_trans (abs_nonneg _) (hbnd 0 0)
  have hconv : ∀ x, Filter.Tendsto
      (fun n => (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (φ n).normed volume) x)
      Filter.atTop (𝓝 (h x)) := by
    intro x
    have hbase := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume)
      (g := h) hφrOut hhc x
    exact hbase.congr fun n => by rw [← convolution_flip, hLflip]
  have hconvc : ∀ n,
      Continuous (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (φ n).normed volume) :=
    fun n => (hρcs n).continuous_convolution_right
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hhLI (hρc n)
  have hχL2 : MemLp (fun x => Mh * χ x) 2 (volume.restrict V) :=
    ((hχc.memLp_of_hasCompactSupport (p := 2) (μ := volume) hχcs :
      MemLp χ 2 volume).const_mul Mh).restrict V
  set bound : EuclideanSpace ℝ (Fin d) → ℝ := fun x => |(w x : ℝ) * (Mh * χ x)| with hbound
  have hbound_int : Integrable bound (volume.restrict V) :=
    ((Lp.memLp w).integrable_mul hχL2).abs
  refine tendsto_integral_of_dominated_convergence bound ?_ hbound_int ?_ ?_
  · intro n
    exact ((Lp.memLp w).aestronglyMeasurable).mul
      (((hconvc n).mul hχc).aestronglyMeasurable)
  · intro n
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs]
    calc |(w x : ℝ)
            * ((h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (φ n).normed volume) x * χ x)|
        = |(w x : ℝ)|
            * |(h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (φ n).normed volume) x| * |χ x| := by
          rw [abs_mul, abs_mul]; ring
      _ ≤ |(w x : ℝ)| * Mh * |χ x| := by gcongr; exact hbnd n x
      _ = bound x := by simp only [hbound, abs_mul, abs_of_nonneg hMh0]; ring
  · refine Filter.Eventually.of_forall fun x => ?_
    exact ((hconv x).mul_const (χ x)).const_mul (w x : ℝ)

/-! ### The weighted weak-derivative product rule -/

/-- **Weak-derivative Leibniz with a `C¹` weight.** If `g` has weak `ℓ`-derivative `g'` on `V`,
and `a` is `C¹` with `a`, `∂_ℓ a` bounded almost everywhere (so the products below are `L²(V)`
classes), then `a·g` has weak `ℓ`-derivative `(∂_ℓ a)·g + a·g'` on `V`. Proved by mollifying the
globally defined coefficient `a`, which keeps the test function `C^∞` and needs no support margin
at `∂V`. -/
theorem HasWeakDerivOn.mul_contDiff_left {V : Set (EuclideanSpace ℝ (Fin d))}
    (hVm : MeasurableSet V) (ℓ : Fin d)
    {g g' : Lp ℝ 2 (volume.restrict V)} (hg : HasWeakDerivOn V ℓ g g')
    {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : ContDiff ℝ 1 a)
    {Ma Mda : ℝ}
    (haM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |a x| ≤ Ma)
    (hdaM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |partialD ℓ a x| ≤ Mda)
    (ag : Lp ℝ 2 (volume.restrict V))
    (hag : ag =ᵐ[volume.restrict V] fun x => a x * (g x : ℝ))
    (dag : Lp ℝ 2 (volume.restrict V))
    (hdag : dag =ᵐ[volume.restrict V]
              fun x => partialD ℓ a x * (g x : ℝ) + a x * (g' x : ℝ)) :
    HasWeakDerivOn V ℓ ag dag := by
  classical
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  have hdacont : Continuous (partialD ℓ a) := by
    have hcf : Continuous (fun x => fderiv ℝ a x) := ha.continuous_fderiv one_ne_zero
    exact hcf.clm_apply continuous_const
  -- shrinking bump sequence
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := fun n =>
    { rIn := 1 / (n + 2 : ℝ) / 2
      rOut := 1 / (n + 2 : ℝ)
      rIn_pos := by positivity
      rIn_lt_rOut := half_lt_self (by positivity) }
  have hrOut : ∀ n, (φ n).rOut = 1 / (n + 2 : ℝ) := fun _ => rfl
  have hφrOut : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (𝓝 0) := by
    simp only [hrOut]
    exact tendsto_const_nhds.div_atTop
      (Filter.tendsto_atTop_add_const_right Filter.atTop 2 tendsto_natCast_atTop_atTop)
  intro ψ hψc hψcs hψV
  -- reduce the goal through the a.e. representatives of `ag`, `dag`
  have hagInt : ∫ x in V, (ag x : ℝ) * partialD ℓ ψ x
      = ∫ x in V, (a x * (g x : ℝ)) * partialD ℓ ψ x :=
    integral_congr_ae (by filter_upwards [hag] with x hx; rw [hx])
  have hdagInt : ∫ x in V, (dag x : ℝ) * ψ x
      = ∫ x in V, (partialD ℓ a x * (g x : ℝ) + a x * (g' x : ℝ)) * ψ x :=
    integral_congr_ae (by filter_upwards [hdag] with x hx; rw [hx])
  rw [hagInt, hdagInt]
  -- the three dominated-convergence limits
  have hA := tendsto_setIntegral_mul_convolution hVm φ hφrOut ha.continuous haM g
    (contDiff_partialD hψc ℓ).continuous (hasCompactSupport_partialD hψcs ℓ)
  have hB := tendsto_setIntegral_mul_convolution hVm φ hφrOut hdacont hdaM g
    hψc.continuous hψcs
  have hC := tendsto_setIntegral_mul_convolution hVm φ hφrOut ha.continuous haM g'
    hψc.continuous hψcs
  -- the `ε`-approximant identity
  have hPn : ∀ n,
      (∫ x in V, (g x : ℝ)
          * ((a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (φ n).normed volume) x
              * partialD ℓ ψ x))
      + (∫ x in V, (g x : ℝ)
          * (((partialD ℓ a) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (φ n).normed volume) x
              * ψ x))
      = -(∫ x in V, (g' x : ℝ)
          * ((a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (φ n).normed volume) x * ψ x)) := by
    intro n
    set ρ := (φ n).normed volume with hρ
    have hρcd : ContDiff ℝ (⊤ : ℕ∞) ρ := (φ n).contDiff_normed
    have hρcs : HasCompactSupport ρ := (φ n).hasCompactSupport_normed
    have haN_cd : ContDiff ℝ (⊤ : ℕ∞) (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) :=
      hρcs.contDiff_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
        ha.continuous.locallyIntegrable hρcd
    have haN_diff : Differentiable ℝ (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) :=
      haN_cd.differentiable (by simp)
    have hdaN_c : Continuous ((partialD ℓ a) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) :=
      hρcs.continuous_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
        hdacont.locallyIntegrable hρcd.continuous
    have hexp : ∀ x, partialD ℓ (fun y =>
          (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) y * ψ y) x
        = (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x * partialD ℓ ψ x
          + ((partialD ℓ a) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x * ψ x := by
      intro x
      have h1 := congrFun (partialD_mul haN_diff (hψc.differentiable (by simp)) ℓ) x
      rw [h1, show partialD ℓ (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ)
            = (partialD ℓ a) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ from
          partialD_convolution_eq ha hρcd hρcs ℓ]
    have hχc : ContDiff ℝ (⊤ : ℕ∞) (fun y =>
        (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) y * ψ y) := haN_cd.mul hψc
    have hχcs : HasCompactSupport (fun y =>
        (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) y * ψ y) := hψcs.mul_left
    have hχV : tsupport (fun y =>
        (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) y * ψ y) ⊆ V :=
      (closure_mono (Function.support_mul_subset_right _ ψ)).trans hψV
    have hgχ := hg (fun y => (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) y * ψ y)
      hχc hχcs hχV
    simp only [hexp] at hgχ
    have hi1 : Integrable (fun x => (g x : ℝ)
        * ((a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x * partialD ℓ ψ x))
        (volume.restrict V) :=
      (Lp.memLp g).integrable_mul
        (((haN_cd.continuous.mul (contDiff_partialD hψc ℓ).continuous).memLp_of_hasCompactSupport
          (p := 2) (μ := volume) (hasCompactSupport_partialD hψcs ℓ).mul_left).restrict V)
    have hi2 : Integrable (fun x => (g x : ℝ)
        * (((partialD ℓ a) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x * ψ x))
        (volume.restrict V) :=
      (Lp.memLp g).integrable_mul
        (((hdaN_c.mul hψc.continuous).memLp_of_hasCompactSupport (p := 2)
          (μ := volume) hψcs.mul_left).restrict V)
    rw [← hgχ, ← integral_add hi1 hi2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  -- pass to the limit
  have hAB := hA.add hB
  have hnegC : Filter.Tendsto
      (fun n => (∫ x in V, (g x : ℝ)
          * ((a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (φ n).normed volume) x
              * partialD ℓ ψ x))
        + (∫ x in V, (g x : ℝ)
          * (((partialD ℓ a) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (φ n).normed volume) x
              * ψ x)))
      Filter.atTop
      (𝓝 (-(∫ x in V, (g' x : ℝ) * (a x * ψ x)))) :=
    Filter.Tendsto.congr (fun n => (hPn n).symm) hC.neg
  have hkey : (∫ x in V, (g x : ℝ) * (a x * partialD ℓ ψ x))
        + (∫ x in V, (g x : ℝ) * (partialD ℓ a x * ψ x))
      = -(∫ x in V, (g' x : ℝ) * (a x * ψ x)) :=
    tendsto_nhds_unique hAB hnegC
  -- reorganise both sides of the goal
  have hLHS : (∫ x in V, (a x * (g x : ℝ)) * partialD ℓ ψ x)
      = ∫ x in V, (g x : ℝ) * (a x * partialD ℓ ψ x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hib : Integrable (fun x => (g x : ℝ) * (partialD ℓ a x * ψ x)) (volume.restrict V) :=
    (Lp.memLp g).integrable_mul
      (((hdacont.mul hψc.continuous).memLp_of_hasCompactSupport (p := 2)
        (μ := volume) hψcs.mul_left).restrict V)
  have hic : Integrable (fun x => (g' x : ℝ) * (a x * ψ x)) (volume.restrict V) :=
    (Lp.memLp g').integrable_mul
      (((ha.continuous.mul hψc.continuous).memLp_of_hasCompactSupport (p := 2)
        (μ := volume) hψcs.mul_left).restrict V)
  have hRHS : (∫ x in V, (partialD ℓ a x * (g x : ℝ) + a x * (g' x : ℝ)) * ψ x)
      = (∫ x in V, (g x : ℝ) * (partialD ℓ a x * ψ x))
        + (∫ x in V, (g' x : ℝ) * (a x * ψ x)) := by
    rw [← integral_add hib hic]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hLHS, hRHS]
  linarith [hkey]

/-! ### Principal term: moving `∂_ℓ` onto `u` -/

/-- Moving `∂_ℓ` from the test function onto `u` in the principal term. For every direction
pair the coefficient-weighted first derivative `a_{ij}·∂ᵢu` has weak `ℓ`-derivative
`(∂_ℓ a_{ij})·∂ᵢu + a_{ij}·∂ₖ∂ᵢu`; testing against `∂ⱼφ` yields, summed over `i,j`,
`∑ ∫_V a_{ij}(∂ᵢu) ∂_ℓ∂ⱼφ = -∑ ∫_V [(∂_ℓ a_{ij})(∂ᵢu) + a_{ij}(∂ₗ∂ᵢu)] ∂ⱼφ`. -/
theorem principal_move {V : Set (EuclideanSpace ℝ (Fin d))} (hVm : MeasurableSet V)
    (A : EllipticCoeff d) (hA : IsC2Coeff A) (ℓ : Fin d)
    (Du : Fin d → Lp ℝ 2 (volume.restrict V))
    (D2 : Fin d → Fin d → Lp ℝ 2 (volume.restrict V))
    (hD2 : ∀ i, HasWeakDerivOn V ℓ (Du i) (D2 ℓ i))
    (aDu : Fin d → Fin d → Lp ℝ 2 (volume.restrict V))
    (haDu : ∀ i j, aDu i j =ᵐ[volume.restrict V] fun x => A.a x i j * (Du i x : ℝ))
    (comm : Fin d → Fin d → Lp ℝ 2 (volume.restrict V))
    (hcomm : ∀ i j, comm i j =ᵐ[volume.restrict V] fun x =>
      partialD ℓ (fun y => A.a y i j) x * (Du i x : ℝ) + A.a x i j * (D2 ℓ i x : ℝ))
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    ∑ i, ∑ j, ∫ x in V, (aDu i j x : ℝ) * partialD ℓ (partialD j φ) x
      = - ∑ i, ∑ j, ∫ x in V, (comm i j x : ℝ) * partialD j φ x := by
  -- the pointwise gradient bound, restated for `partialD` via the operator-norm inequality
  have hbound : ∀ (i j : Fin d) (x : EuclideanSpace ℝ (Fin d)),
      |partialD ℓ (fun y => A.a y i j) x| ≤ hA.A1 := by
    intro i j x
    have heq : partialD ℓ (fun y => A.a y i j) x
        = fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single ℓ 1) := rfl
    rw [heq, ← Real.norm_eq_abs]
    calc ‖fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single ℓ 1)‖
        ≤ ‖fderiv ℝ (fun y => A.a y i j) x‖ * ‖EuclideanSpace.single ℓ (1 : ℝ)‖ :=
          (fderiv ℝ (fun y => A.a y i j) x).le_opNorm _
      _ = ‖fderiv ℝ (fun y => A.a y i j) x‖ := by simp
      _ ≤ hA.A1 := hA.grad_bdd i j x
  -- the crux, specialised to the `(i, j)` coefficient and tested against `∂ⱼφ`
  have hstep : ∀ i j : Fin d,
      ∫ x in V, (aDu i j x : ℝ) * partialD ℓ (partialD j φ) x
        = - ∫ x in V, (comm i j x : ℝ) * partialD j φ x := by
    intro i j
    have hmove := HasWeakDerivOn.mul_contDiff_left hVm ℓ (hD2 i)
      (hA.toIsC1Coeff.contDiff i j) (A.bdd i j) (Filter.Eventually.of_forall (hbound i j))
      (aDu i j) (haDu i j) (comm i j) (hcomm i j)
    obtain ⟨hψc, hψcs, hψV⟩ := isTest_partialD hφc hφcs hφV j
    exact hmove (partialD j φ) hψc hψcs hψV
  -- sum the per-`(i, j)` identity and push the sign out of the double sum
  calc ∑ i, ∑ j, ∫ x in V, (aDu i j x : ℝ) * partialD ℓ (partialD j φ) x
      = ∑ i : Fin d, ∑ j : Fin d, - ∫ x in V, (comm i j x : ℝ) * partialD j φ x :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hstep i j))
    _ = - ∑ i, ∑ j, ∫ x in V, (comm i j x : ℝ) * partialD j φ x := by
        simp only [Finset.sum_neg_distrib]

end EllipticDirichlet.Regularity
