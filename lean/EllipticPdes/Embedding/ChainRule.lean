/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.Morrey
public import EllipticPdes.Embedding.GagliardoNirenberg
public import EllipticPdes.Embedding.WeakDerivChain
public import EllipticPdes.Embedding.WeakGradUnique

/-!
# Chain rule for weak gradients

A `C¹` function of a class with a weak gradient has a weak gradient, the derivative of the
function at the class times the gradient, once the derivative is bounded. The proof mollifies
the class inside the domain: on the support of a test function, the partials of the
mollifications are the mollified gradient, the classical chain rule and integration by parts
apply to each mollification, and both sides pass to the limit. The function side uses the
Lipschitz bound on `f`; the gradient side uses a subsequence converging almost everywhere and
dominated convergence for the continuous, bounded derivative.

The positive part follows from the chain rule applied to the `C¹` functions
`t ↦ √((t⁺)² + ε²) - ε`, which increase to `t⁺` as `ε` decreases to `0` with derivatives
bounded by one, and from dominated convergence once more. The weak gradient of `u⁺` is the
gradient of `u` where `u > 0` and zero elsewhere. Splitting `u - c` into positive and negative
parts and using uniqueness of the weak gradient, the gradient vanishes almost everywhere on
every level set.

Integrability is asked for locally on the domain throughout, which is the class the sources
state the results for, and the domain is open.

## Main declarations

* `EllipticPdes.Embedding.hasWeakGradOn_comp`: the chain rule for a `C¹` function with bounded
  derivative.
* `EllipticPdes.Embedding.hasWeakGradOn_posPart`: the weak gradient of the positive part.
* `EllipticPdes.Embedding.hasWeakGradOn_posPart_sub_const`: the weak gradient of `(u - c)⁺`.
* `EllipticPdes.Embedding.ae_eq_zero_of_eq_const_of_hasWeakGradOn`: the weak gradient vanishes
  almost everywhere on a level set.

## References

D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§7.4 Lemma 7.5 (p. 151), Lemma 7.6 and Lemma 7.7 (p. 152);
L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.10 Problems 17 and 18 (p. 308).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal Convolution

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD tsupport_partialD_subset)

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### Elementary closure properties with local integrability -/

/-- **Negation of a weak gradient.** -/
theorem HasWeakGradOn.neg {B : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (h : HasWeakGradOn B u g) : HasWeakGradOn B (fun x => -u x) (fun k x => -g k x) := by
  intro φ hφc hφcs hφB k
  have key := h φ hφc hφcs hφB k
  simp only [neg_mul, integral_neg, key, neg_neg]

/-- **Additivity of a weak gradient**, with local integrability on an open set. -/
theorem HasWeakGradOn.add_of_locallyIntegrableOn
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} {g h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : LocallyIntegrableOn u Ω volume) (hv : LocallyIntegrableOn v Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hh : ∀ k, LocallyIntegrableOn (h k) Ω volume)
    (hU : HasWeakGradOn Ω u g) (hV : HasWeakGradOn Ω v h) :
    HasWeakGradOn Ω (fun x => u x + v x) (fun k x => g k x + h k x) := by
  intro φ hφc hφcs hφs k
  have hφcont : Continuous φ := hφc.continuous
  have hφpc : Continuous (partialD k φ) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφpcs : HasCompactSupport (partialD k φ) :=
    hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  have hps : tsupport (partialD k φ) ⊆ Ω := (tsupport_partialD_subset k φ).trans hφs
  have hL : ∫ x in Ω, (u x + v x) * partialD k φ x
      = (∫ x in Ω, u x * partialD k φ x) + ∫ x in Ω, v x * partialD k φ x := by
    rw [← integral_add (integrable_mul_of_locallyIntegrableOn hu hφpc hφpcs hps).integrableOn
      (integrable_mul_of_locallyIntegrableOn hv hφpc hφpcs hps).integrableOn]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hR : ∫ x in Ω, (g k x + h k x) * φ x
      = (∫ x in Ω, g k x * φ x) + ∫ x in Ω, h k x * φ x := by
    rw [← integral_add (integrable_mul_of_locallyIntegrableOn (hg k) hφcont hφcs hφs).integrableOn
      (integrable_mul_of_locallyIntegrableOn (hh k) hφcont hφcs hφs).integrableOn]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [hL, hR, hU φ hφc hφcs hφs k, hV φ hφc hφcs hφs k]
  ring

/-- **Subtracting a constant** leaves the weak gradient unchanged. -/
theorem hasWeakGradOn_sub_const {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hwg : HasWeakGradOn Ω u g) (c : ℝ) : HasWeakGradOn Ω (fun x => u x - c) g := by
  intro φ hφc hφcs hφs k
  have hφpc : Continuous (partialD k φ) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφpcs : HasCompactSupport (partialD k φ) :=
    hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  have hps : tsupport (partialD k φ) ⊆ Ω := (tsupport_partialD_subset k φ).trans hφs
  -- the integral of a partial of a test function vanishes
  have hzero : ∫ x, partialD k φ x = 0 := by
    have h0 : ∀ x : EuclideanSpace ℝ (Fin d), fderiv ℝ (fun _ => (1 : ℝ)) x = 0 := fun x =>
      by simp
    have hI1 : Integrable (fun x => fderiv ℝ φ x (EuclideanSpace.single k (1 : ℝ))) volume :=
      hφpc.integrable_of_hasCompactSupport hφpcs
    have hI2 : Integrable φ volume := hφc.continuous.integrable_of_hasCompactSupport hφcs
    have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun _ => (1 : ℝ)) (g := φ) (v := EuclideanSpace.single k (1 : ℝ))
      (by simp only [h0, _root_.zero_apply, zero_mul]; exact integrable_zero _ _ _)
      (by simpa using hI1) (by simpa using hI2)
      (fun x _ => differentiableAt_const _) (fun x _ => (hφc.differentiable (by simp)) x)
    simp only [one_mul, h0, _root_.zero_apply, zero_mul, integral_zero,
      neg_zero] at key
    simpa [partialD] using key
  have hzeroΩ : ∫ x in Ω, partialD k φ x = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      image_eq_zero_of_notMem_tsupport fun hc => hx (hps hc)]
    exact hzero
  have hsplit : ∫ x in Ω, (u x - c) * partialD k φ x
      = (∫ x in Ω, u x * partialD k φ x) - c * ∫ x in Ω, partialD k φ x := by
    rw [← integral_const_mul, ← integral_sub
      (integrable_mul_of_locallyIntegrableOn hu hφpc hφpcs hps).integrableOn
      ((hφpc.integrable_of_hasCompactSupport hφpcs).integrableOn.const_mul c)]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [hsplit, hzeroΩ, mul_zero, sub_zero, hwg φ hφc hφcs hφs k]

/-! ### The chain rule -/

/-- **Chain rule for weak gradients** (Gilbarg and Trudinger Lemma 7.5, Evans §5.10 Problem
17). A `C¹` function with bounded derivative, composed with a class with a locally integrable
weak gradient on an open set, has the weak gradient `f'(u) ∇u` there. This is the coordinate
form of `HasWeakFDerivOn.comp_contDiff`. -/
theorem hasWeakGradOn_comp (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hwg : HasWeakGradOn Ω u g)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ≥0} (hM : ∀ t, ‖deriv f t‖₊ ≤ M) :
    HasWeakGradOn Ω (fun x => f (u x)) (fun k x => deriv f (u x) * g k x) := by
  have h := ((hasWeakGradOn_iff_hasWeakFDerivOn hΩ hu hg).1 hwg).comp_contDiff hf hM
  have hk : ∀ k, LocallyIntegrableOn (fun x => deriv f (u x) * g k x) Ω volume := fun k => by
    simpa using (h (EuclideanSpace.single k 1)).locallyIntegrableOn
  refine (hasWeakGradOn_iff_hasWeakFDerivOn hΩ (h 0).locallyIntegrableOn_fun hk).2 ?_
  convert h using 1
  funext x
  ext v
  simp only [gradCLM, sum_apply, smul_apply,
    smul_eq_mul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => by simp; ring

/-! ### The positive part -/

/-- The `C¹` approximation of the positive part, `√((t⁺)² + ε²) - ε`. -/
private def posPartApprox (ε t : ℝ) : ℝ := Real.sqrt ((max t 0) ^ 2 + ε ^ 2) - ε

/-- The square of the positive part is differentiable, with derivative `2 t⁺`. -/
private theorem hasDerivAt_max_sq (t : ℝ) :
    HasDerivAt (fun s : ℝ => (max s 0) ^ 2) (2 * max t 0) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h0 : (fun s : ℝ => (max s 0) ^ 2) =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
      (gt_mem_nhds ht).mono fun s hs => by simp [max_eq_right hs.le]
    rw [max_eq_right ht.le, mul_zero]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq h0
  · rw [hasDerivAt_iff_tendsto_slope_zero]
    simp only [zero_add, max_self, zero_pow two_ne_zero, sub_zero, mul_zero, smul_eq_mul]
    have hcont : Tendsto (fun s : ℝ => max s 0) (𝓝[≠] 0) (𝓝 0) := by
      have hc0 : Continuous fun s : ℝ => max s 0 := continuous_id.max continuous_const
      have := hc0.tendsto (0 : ℝ)
      simp only [max_self] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    refine hcont.congr' (eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun s hs => ?_))
    rcases lt_or_gt_of_ne hs with hs' | hs'
    · simp [max_eq_right hs'.le]
    · simp only [max_eq_left hs'.le]
      field_simp
  · have h0 : (fun s : ℝ => (max s 0) ^ 2) =ᶠ[𝓝 t] fun s => s ^ 2 :=
      (lt_mem_nhds ht).mono fun s hs => by simp [max_eq_left hs.le]
    rw [max_eq_left ht.le]
    have := hasDerivAt_pow 2 t
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at this
    exact this.congr_of_eventuallyEq h0

/-- The square of the positive part is `C¹`. -/
private theorem contDiff_max_sq : ContDiff ℝ 1 fun s : ℝ => (max s 0) ^ 2 := by
  refine contDiff_one_iff_deriv.mpr ⟨fun t => (hasDerivAt_max_sq t).differentiableAt, ?_⟩
  rw [funext fun t => (hasDerivAt_max_sq t).deriv]
  exact continuous_const.mul (continuous_id.max continuous_const)

/-- The argument of the square root in `posPartApprox` is positive. -/
private theorem posPartApprox_arg_pos {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) : 0 < (max t 0) ^ 2 + ε ^ 2 := by
  have := pow_pos (abs_pos.mpr hε) 2
  rw [sq_abs] at this
  nlinarith [sq_nonneg (max t 0)]

/-- The derivative of the approximation. -/
private theorem hasDerivAt_posPartApprox {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    HasDerivAt (posPartApprox ε)
      (2 * max t 0 / (2 * Real.sqrt ((max t 0) ^ 2 + ε ^ 2))) t :=
  (((hasDerivAt_max_sq t).add_const (ε ^ 2)).sqrt (posPartApprox_arg_pos hε t).ne').sub_const ε

/-- The approximation is `C¹`. -/
private theorem contDiff_posPartApprox {ε : ℝ} (hε : ε ≠ 0) : ContDiff ℝ 1 (posPartApprox ε) :=
  ((contDiff_max_sq.add contDiff_const).sqrt fun t => (posPartApprox_arg_pos hε t).ne').sub
    contDiff_const

/-- The derivative of the approximation, in closed form. -/
private theorem deriv_posPartApprox {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    deriv (posPartApprox ε) t = max t 0 / Real.sqrt ((max t 0) ^ 2 + ε ^ 2) := by
  rw [(hasDerivAt_posPartApprox hε t).deriv, mul_div_mul_left _ _ two_ne_zero]

/-- The derivative of the approximation lies in `[0, 1]`. -/
private theorem deriv_posPartApprox_mem {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    0 ≤ deriv (posPartApprox ε) t ∧ deriv (posPartApprox ε) t ≤ 1 := by
  rw [deriv_posPartApprox hε]
  have hm : 0 ≤ max t 0 := le_max_right _ _
  have hs : 0 < Real.sqrt ((max t 0) ^ 2 + ε ^ 2) :=
    Real.sqrt_pos.mpr (posPartApprox_arg_pos hε t)
  refine ⟨div_nonneg hm hs.le, (div_le_one hs).mpr ?_⟩
  exact (Real.le_sqrt hm (posPartApprox_arg_pos hε t).le).mpr (by nlinarith [sq_nonneg ε])

/-- The derivative of the approximation has nonnegative norm at most one. -/
private theorem nnnorm_deriv_posPartApprox_le {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    ‖deriv (posPartApprox ε) t‖₊ ≤ 1 := by
  obtain ⟨h0, h1⟩ := deriv_posPartApprox_mem hε t
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg h0, NNReal.coe_one]
  exact h1

/-- The approximation lies between `0` and the positive part. -/
private theorem posPartApprox_mem {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    0 ≤ posPartApprox ε t ∧ posPartApprox ε t ≤ max t 0 := by
  have hm : 0 ≤ max t 0 := le_max_right _ _
  unfold posPartApprox
  constructor
  · rw [sub_nonneg]
    calc ε = Real.sqrt (ε ^ 2) := (Real.sqrt_sq hε).symm
      _ ≤ Real.sqrt ((max t 0) ^ 2 + ε ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (max t 0)])
  · rw [sub_le_iff_le_add]
    exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩

/-- The approximation tends to the positive part as `ε → 0`. -/
private theorem tendsto_posPartApprox (t : ℝ) :
    Tendsto (fun ε => posPartApprox ε t) (𝓝 0) (𝓝 (max t 0)) := by
  have hc : Continuous fun ε : ℝ => posPartApprox ε t := by
    unfold posPartApprox
    fun_prop
  have := hc.tendsto 0
  simp only [posPartApprox, zero_pow two_ne_zero, add_zero, sub_zero,
    Real.sqrt_sq (le_max_right t 0)] at this
  exact this

/-- The derivative of the approximation tends to the indicator of `{t > 0}` as `ε → 0`
along positive values. -/
private theorem tendsto_deriv_posPartApprox (t : ℝ) :
    Tendsto (fun n : ℕ => deriv (posPartApprox (1 / (n + 1 : ℝ))) t) atTop
      (𝓝 (if 0 < t then 1 else 0)) := by
  have hεne : ∀ n : ℕ, (1 / (n + 1 : ℝ)) ≠ 0 := fun n => by positivity
  simp only [fun n => deriv_posPartApprox (hεne n) t]
  split_ifs with ht
  · rw [max_eq_left ht.le]
    have hc : Continuous fun ε : ℝ => t / Real.sqrt (t ^ 2 + ε ^ 2) := by
      refine continuous_const.div (continuous_const.add (continuous_id.pow 2)).sqrt fun ε => ?_
      exact (Real.sqrt_pos.mpr (by positivity)).ne'
    have := (hc.tendsto 0).comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simp only [Function.comp_def, zero_pow two_ne_zero, add_zero, Real.sqrt_sq ht.le,
      div_self ht.ne'] at this
    exact this
  · rw [max_eq_right (not_lt.mp ht)]
    simp only [zero_div]
    exact tendsto_const_nhds

/-- **Weak gradient of the positive part** (Gilbarg and Trudinger Lemma 7.6, Evans §5.10
Problem 18). On an open set, `u⁺ = max u 0` has the weak gradient `∇u` where `u > 0` and `0`
elsewhere. -/
theorem hasWeakGradOn_posPart (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hwg : HasWeakGradOn Ω u g) :
    HasWeakGradOn Ω (fun x => max (u x) 0) (fun k x => if 0 < u x then g k x else 0) := by
  intro φ hφc hφcs hφΩ k
  have hφcont : Continuous φ := hφc.continuous
  have hpc : Continuous (partialD k φ) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpcs : HasCompactSupport (partialD k φ) :=
    hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  have hps : tsupport (partialD k φ) ⊆ Ω := (tsupport_partialD_subset k φ).trans hφΩ
  set ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ) with hεdef
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hum : AEStronglyMeasurable u (volume.restrict Ω) := hu.aestronglyMeasurable
  -- the identity for every approximation
  have hn : ∀ n, ∫ x in Ω, posPartApprox (ε n) (u x) * partialD k φ x
      = -∫ x in Ω, deriv (posPartApprox (ε n)) (u x) * g k x * φ x := fun n =>
    hasWeakGradOn_comp hΩ hu hg hwg (contDiff_posPartApprox (hεpos n).ne') (M := 1)
      (nnnorm_deriv_posPartApprox_le (hεpos n).ne') φ hφc hφcs hφΩ k
  -- the function side
  have hL : Tendsto (fun n => ∫ x in Ω, posPartApprox (ε n) (u x) * partialD k φ x) atTop
      (𝓝 (∫ x in Ω, max (u x) 0 * partialD k φ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖u x * partialD k φ x‖)
      (fun n => ((contDiff_posPartApprox (hεpos n).ne').continuous.comp_aestronglyMeasurable
        hum).mul hpc.aestronglyMeasurable)
      (integrable_mul_of_locallyIntegrableOn hu hpc hpcs hps).norm.integrableOn
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · obtain ⟨h0, h1⟩ := posPartApprox_mem (hεpos n).le (u x)
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0]
      gcongr
      refine h1.trans ?_
      rw [Real.norm_eq_abs]
      exact max_le (le_abs_self _) (abs_nonneg _)
    · exact ((tendsto_posPartApprox (u x)).comp hε0).mul_const _
  -- the gradient side
  have hR : Tendsto (fun n => ∫ x in Ω, deriv (posPartApprox (ε n)) (u x) * g k x * φ x) atTop
      (𝓝 (∫ x in Ω, (if 0 < u x then 1 else 0) * g k x * φ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖g k x * φ x‖)
      (fun n => (((contDiff_posPartApprox (hεpos n).ne').continuous_deriv_one
        |>.comp_aestronglyMeasurable hum).mul (hg k).aestronglyMeasurable).mul
        hφcont.aestronglyMeasurable)
      (integrable_mul_of_locallyIntegrableOn (hg k) hφcont hφcs hφΩ).norm.integrableOn
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · obtain ⟨h0, h1⟩ := deriv_posPartApprox_mem (hεpos n).ne' (u x)
      rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg h0]
      calc deriv (posPartApprox (ε n)) (u x) * ‖g k x‖ * ‖φ x‖
          ≤ 1 * ‖g k x‖ * ‖φ x‖ := by gcongr
        _ = ‖g k x‖ * ‖φ x‖ := by ring
    · exact ((tendsto_deriv_posPartApprox (u x)).mul_const _).mul_const _
  have hlim := tendsto_nhds_unique hL (by simp only [hn]; exact hR.neg)
  rw [hlim]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  split_ifs <;> simp

/-- **Weak gradient of `(u - c)⁺`.** -/
theorem hasWeakGradOn_posPart_sub_const (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hwg : HasWeakGradOn Ω u g) (c : ℝ) :
    HasWeakGradOn Ω (fun x => max (u x - c) 0) (fun k x => if c < u x then g k x else 0) := by
  have huc : LocallyIntegrableOn (fun x => u x - c) Ω volume :=
    hu.sub (locallyIntegrableOn_const c)
  have := hasWeakGradOn_posPart hΩ huc hg (hasWeakGradOn_sub_const hu hwg c)
  simpa only [sub_pos] using this

/-- **Local integrability by domination.** -/
theorem locallyIntegrableOn_of_norm_le (hΩ : IsOpen Ω) {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : LocallyIntegrableOn g Ω volume) (hf : AEStronglyMeasurable f (volume.restrict Ω))
    (h : ∀ x, ‖f x‖ ≤ ‖g x‖) : LocallyIntegrableOn f Ω volume :=
  (locallyIntegrableOn_iff hΩ.isLocallyClosed).mpr fun _ hK hKc =>
    (hg.integrableOn_compact_subset hK hKc).norm.mono'
      (hf.mono_measure (Measure.restrict_mono hK le_rfl)) (Eventually.of_forall h)

/-- **Measurability of a truncation.** -/
theorem aestronglyMeasurable_ite_lt {μ : Measure (EuclideanSpace ℝ (Fin d))}
    {u w : EuclideanSpace ℝ (Fin d) → ℝ} (hu : AEStronglyMeasurable u μ)
    (hw : AEStronglyMeasurable w μ) (c : ℝ) :
    AEStronglyMeasurable (fun x => if c < u x then w x else 0) μ := by
  refine ⟨fun x => if c < hu.mk u x then hw.mk w x else 0, ?_, ?_⟩
  · exact StronglyMeasurable.ite
      (measurableSet_lt measurable_const hu.stronglyMeasurable_mk.measurable)
      hw.stronglyMeasurable_mk stronglyMeasurable_const
  · filter_upwards [hu.ae_eq_mk, hw.ae_eq_mk] with x h1 h2
    simp only [h1, h2]

/-- **Local integrability of a truncated gradient.** -/
theorem locallyIntegrableOn_ite_lt (hΩ : IsOpen Ω) {u w : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict Ω)) (hw : LocallyIntegrableOn w Ω volume)
    (c : ℝ) : LocallyIntegrableOn (fun x => if c < u x then w x else 0) Ω volume :=
  locallyIntegrableOn_of_norm_le hΩ hw (aestronglyMeasurable_ite_lt hu hw.aestronglyMeasurable c)
    fun x => by split_ifs <;> simp

/-- **Local integrability of the positive part of `u - c`.** -/
theorem locallyIntegrableOn_posPart_sub_const (hΩ : IsOpen Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume) (c : ℝ) :
    LocallyIntegrableOn (fun x => max (u x - c) 0) Ω volume := by
  refine locallyIntegrableOn_of_norm_le hΩ (hu.sub (locallyIntegrableOn_const c))
    (((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable
      hu.aestronglyMeasurable) fun x => ?_
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le (le_abs_self _) (abs_nonneg _)

/-- **Vanishing of the weak gradient on level sets** (Gilbarg and Trudinger Lemma 7.7). On an
open set, the weak gradient of `u` is zero almost everywhere on `{u = c}`. -/
theorem ae_eq_zero_of_eq_const_of_hasWeakGradOn (hΩ : IsOpen Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : LocallyIntegrableOn u Ω volume) (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume)
    (hwg : HasWeakGradOn Ω u g) (c : ℝ) (k : Fin d) :
    ∀ᵐ x ∂(volume.restrict Ω), u x = c → g k x = 0 := by
  have hum : AEStronglyMeasurable u (volume.restrict Ω) := hu.aestronglyMeasurable
  -- the positive parts of `u - c` and of `-u - (-c)`
  have hpos := hasWeakGradOn_posPart_sub_const hΩ hu hg hwg c
  have hneg := hasWeakGradOn_posPart_sub_const hΩ hu.neg (fun j => (hg j).neg) hwg.neg (-c)
  have hind : ∀ j, LocallyIntegrableOn (fun x => if c < u x then g j x else 0) Ω volume :=
    fun j => locallyIntegrableOn_ite_lt hΩ hum (hg j) c
  have hind' : ∀ j, LocallyIntegrableOn (fun x => if -c < -u x then -g j x else 0) Ω volume :=
    fun j => locallyIntegrableOn_ite_lt hΩ hum.neg (hg j).neg (-c)
  have hsum := hpos.add_of_locallyIntegrableOn (locallyIntegrableOn_posPart_sub_const hΩ hu c)
    (locallyIntegrableOn_posPart_sub_const hΩ hu.neg (-c)).neg hind (fun j => (hind' j).neg)
    hneg.neg
  -- the sum is `u - c`, whose weak gradient is `g`
  have heq : (fun x => max (u x - c) 0 + -max (-u x - -c) 0) = fun x => u x - c := by
    funext x
    rw [neg_sub_neg, ← neg_sub (u x) c, ← sub_eq_add_neg, max_zero_sub_max_neg_zero_eq_self]
  simp only [Pi.neg_apply] at hsum
  rw [heq] at hsum
  have hsumint : ∀ j, LocallyIntegrableOn
      (fun x => (if c < u x then g j x else 0) + -(if -c < -u x then -g j x else 0)) Ω volume :=
    fun j => (hind j).add (hind' j).neg
  have huniq := hasWeakGradOn_unique_ae_of_locallyIntegrableOn hΩ hg hsumint
    (hasWeakGradOn_sub_const hu hwg c) hsum k
  filter_upwards [huniq] with x hx hxc
  rw [hx]
  simp [hxc]

/-- **Weak gradient of the negative part** (Gilbarg and Trudinger Lemma 7.6, second clause).
`u⁻ = min u 0` has the weak gradient `∇u` where `u < 0` and `0` elsewhere. -/
theorem hasWeakGradOn_negPart (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hwg : HasWeakGradOn Ω u g) :
    HasWeakGradOn Ω (fun x => min (u x) 0) (fun k x => if u x < 0 then g k x else 0) := by
  have h := (hasWeakGradOn_posPart hΩ hu.neg (fun k => (hg k).neg) hwg.neg).neg
  refine h.congr_ae (Eventually.of_forall fun x => ?_) fun k => Eventually.of_forall fun x => ?_
  · simp only [Pi.neg_apply]
    by_cases hx : u x ≤ 0
    · rw [min_eq_left hx, max_eq_left (by linarith), neg_neg]
    · have hx' : 0 < u x := not_le.mp hx
      rw [min_eq_right hx'.le, max_eq_right (by linarith), neg_zero]
  · simp only [Pi.neg_apply, neg_pos]
    split_ifs <;> simp

/-- Local integrability of the positive part. -/
theorem locallyIntegrableOn_posPart (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : LocallyIntegrableOn u Ω volume) :
    LocallyIntegrableOn (fun x => max (u x) 0) Ω volume := by
  have := locallyIntegrableOn_posPart_sub_const hΩ hu 0
  simpa only [sub_zero] using this

/-- **Weak gradient of the absolute value** (Gilbarg and Trudinger Lemma 7.6, third clause).
`|u|` has the weak gradient `∇u` where `u > 0`, `-∇u` where `u < 0`, and `0` elsewhere. -/
theorem hasWeakGradOn_abs (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hwg : HasWeakGradOn Ω u g) :
    HasWeakGradOn Ω (fun x => |u x|)
      fun k x => if 0 < u x then g k x else if u x < 0 then -g k x else 0 := by
  have hpos := hasWeakGradOn_posPart hΩ hu hg hwg
  have hneg := hasWeakGradOn_posPart hΩ hu.neg (fun k => (hg k).neg) hwg.neg
  have hsum := hpos.add_of_locallyIntegrableOn (locallyIntegrableOn_posPart hΩ hu)
    (locallyIntegrableOn_posPart hΩ hu.neg)
    (fun k => locallyIntegrableOn_ite_lt hΩ hu.aestronglyMeasurable (hg k) 0)
    (fun k => locallyIntegrableOn_ite_lt hΩ hu.neg.aestronglyMeasurable (hg k).neg 0) hneg
  refine hsum.congr_ae (Eventually.of_forall fun x => ?_)
    fun k => Eventually.of_forall fun x => ?_
  · simp only [Pi.neg_apply]
    exact max_zero_add_max_neg_zero_eq_abs_self (u x)
  · simp only [Pi.neg_apply, neg_pos]
    rcases lt_trichotomy (u x) 0 with h | h | h
    · have h' : ¬ 0 < u x := not_lt.mpr h.le
      simp [h, h']
    · simp [h]
    · have h' : ¬ u x < 0 := not_lt.mpr h.le
      simp [h, h']

end EllipticPdes.Embedding
