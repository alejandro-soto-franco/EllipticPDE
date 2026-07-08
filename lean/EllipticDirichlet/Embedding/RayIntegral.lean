/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticDirichlet.Embedding.WeakGradient
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Ray fundamental theorem of calculus

For a smooth function `φ`, the increment `φ (x + v) - φ x` equals the integral, over
`[0, 1]`, of the directional derivative `(fderiv ℝ φ (x + t • v)) v` along the segment
`t ↦ x + t • v`. This is the pointwise identity consumed by the potential-estimate step
of the Morrey embedding.
-/

open MeasureTheory Set Metric
open scoped NNReal ENNReal

noncomputable section

namespace EllipticDirichlet.Embedding

variable {d : ℕ}

/-- The segment path `t ↦ φ (x + t • v)` has derivative `(fderiv ℝ φ (x + t • v)) v`. -/
private theorem hasDerivAt_comp_segment {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x v : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (x + s • v)) ((fderiv ℝ φ (x + t • v)) v) t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hφ' : HasFDerivAt φ (fderiv ℝ φ (x + t • v)) (x + t • v) :=
    (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt
  exact hφ'.comp_hasDerivAt t hline

/-- **Ray fundamental theorem of calculus.** For smooth `φ`, the increment along the
segment from `x` to `x + v` is the integral of the directional derivative. -/
theorem sub_eq_intervalIntegral_fderiv {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x v : EuclideanSpace ℝ (Fin d)) :
    φ (x + v) - φ x = ∫ t in (0 : ℝ)..1, (fderiv ℝ φ (x + t • v)) v := by
  have hcont : Continuous (fun t : ℝ => (fderiv ℝ φ (x + t • v)) v) :=
    ((hφ.continuous_fderiv (by simp)).comp (by fun_prop)).clm_apply continuous_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hasDerivAt_comp_segment hφ x v t)
        hcont.continuousOn.intervalIntegrable]
  simp

/-- **Ray-FTC average identity (Morrey rung 4a).** For smooth `φ`, the oscillation of the
ball-average of `φ` about the value `φ x` equals the average over the ball of the ray
integral of the directional derivative from `x` towards the running point `y`. This is the
mechanical half of the potential estimate: it rewrites the oscillation as an average of
gradient line-integrals, from which the kernel bound is read off. -/
theorem oscillation_eq_average_ray [Nontrivial (EuclideanSpace ℝ (Fin d))]
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (c x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    (⨍ y in ball c r, φ y) - φ x
      = ⨍ y in ball c r, ∫ t in (0 : ℝ)..1, (fderiv ℝ φ (x + t • (y - x))) (y - x) := by
  have hmeas : MeasurableSet (ball c r) := measurableSet_ball
  have hpos : volume (ball c r) ≠ 0 := (measure_ball_pos volume c hr).ne'
  have hlt : volume (ball c r) < ⊤ := measure_ball_lt_top
  have htop := hlt.ne
  -- Pointwise: replace the inner ray integral by `φ y - φ x` via Task 3.
  have hcongr : (⨍ y in ball c r, ∫ t in (0 : ℝ)..1,
      (fderiv ℝ φ (x + t • (y - x))) (y - x))
      = ⨍ y in ball c r, (φ y - φ x) := by
    refine setAverage_congr_fun hmeas ?_
    filter_upwards with y _
    have h := (sub_eq_intervalIntegral_fderiv hφ x (y - x)).symm
    rwa [add_sub_cancel] at h
  rw [hcongr]
  -- `φ` is integrable on the ball (continuous, ball has finite measure).
  have hint : IntegrableOn φ (ball c r) volume :=
    (hφ.continuous.locallyIntegrable.integrableOn_isCompact (isCompact_closedBall c r)).mono_set
      ball_subset_closedBall
  -- Split the average of the difference.
  rw [setAverage_eq, setAverage_eq, integral_sub hint (integrableOn_const htop),
    smul_sub, setIntegral_const, smul_smul]
  have hk : (volume.real (ball c r))⁻¹ * volume.real (ball c r) = 1 :=
    inv_mul_cancel₀ (by
      simp only [measureReal_def, ne_eq, ENNReal.toReal_eq_zero_iff, not_or]
      exact ⟨hpos, htop⟩)
  rw [hk, one_smul]

/-- **Region fact.** If `x, y` both lie in `ball c r` and `0 < t`, then the segment point
`x + t • (y - x)` is within distance `2 r t` of `x`. This is the geometric input feeding the
Riesz-kernel tail bound: after the affine change of variables the transformed region
`B_t = x + t • (ball c r - x)` sits inside the ball `‖z - x‖ < 2 r t`. -/
private theorem norm_smul_sub_lt_two_mul {c x y : EuclideanSpace ℝ (Fin d)} {r t : ℝ}
    (hx : x ∈ ball c r) (hy : y ∈ ball c r) (ht : 0 < t) :
    ‖t • (y - x)‖ < 2 * r * t := by
  have hyx : ‖y - x‖ < 2 * r := by
    have htri : dist y x ≤ dist y c + dist c x := dist_triangle y c x
    have h1 : dist y c < r := by rwa [mem_ball] at hy
    have h2 : dist c x < r := by rw [dist_comm]; rwa [mem_ball] at hx
    have : dist y x < 2 * r := by linarith
    rwa [dist_eq_norm] at this
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  calc t * ‖y - x‖ < t * (2 * r) := by exact mul_lt_mul_of_pos_left hyx ht
    _ = 2 * r * t := by ring

/-- **Tail bound.** For `a > 0` and dimension `d ≥ 1`, the interval integral of the singular
kernel `t ^ (-(d+1))` from `a` to `1` is bounded by `a^{-d} / d`. Applied with
`a = ‖z - x‖ / (2 r)` this produces the Riesz-kernel factor `(2 r)^d / (d ‖z - x‖^d)`. -/
private theorem tail_integral_bound (hd : 0 < d) {a : ℝ} (ha : 0 < a) :
    ∫ t in a..(1 : ℝ), t ^ (-((d : ℤ) + 1)) ≤ a ^ (-(d : ℤ)) / d := by
  have hne : (-((d : ℤ) + 1)) ≠ -1 := by
    have : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    omega
  have h0 : (0 : ℝ) ∉ Set.uIcc a 1 := by
    intro h
    rw [Set.mem_uIcc] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  rw [integral_zpow (Or.inr ⟨hne, h0⟩)]
  have hexp : (-((d : ℤ) + 1)) + 1 = -(d : ℤ) := by ring
  rw [hexp]
  have hA : (0 : ℝ) < a ^ (-(d : ℤ)) := by positivity
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hden : (((-((d : ℤ) + 1)) : ℤ) : ℝ) + 1 = -(d : ℝ) := by push_cast; ring
  have key : (1 - a ^ (-(d : ℤ))) / (-(d : ℝ)) = (a ^ (-(d : ℤ)) - 1) / (d : ℝ) := by
    rw [div_neg]; ring
  rw [hden, one_zpow, key, div_le_div_iff_of_pos_right hdR]
  linarith

/-- **Pushforward of Lebesgue measure under the affine contraction** `y ↦ x + t • (y - x)`.
Being the composition of a translation, a dilation by `t`, and a translation, it scales the
Haar measure by `t^{-d}`. This is the Jacobian input to the change of variables. -/
private theorem map_affine_dilation (x : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 < t) :
    Measure.map (fun y => x + t • (y - x)) (volume : Measure (EuclideanSpace ℝ (Fin d)))
      = ENNReal.ofReal ((t ^ d)⁻¹) • volume := by
  have hC : Measurable (fun y : EuclideanSpace ℝ (Fin d) => y - x) := measurable_id.sub_const x
  have hB : Measurable (fun w : EuclideanSpace ℝ (Fin d) => t • w) := measurable_id.const_smul t
  have hA : Measurable (fun u : EuclideanSpace ℝ (Fin d) => x + u) := measurable_id.const_add x
  have hcomp : (fun y : EuclideanSpace ℝ (Fin d) => x + t • (y - x))
      = (fun u => x + u) ∘ ((fun w => t • w) ∘ (fun y => y - x)) := by funext y; rfl
  rw [hcomp, ← Measure.map_map hA (hB.comp hC), ← Measure.map_map hB hC]
  have hmapC : Measure.map (fun y : EuclideanSpace ℝ (Fin d) => y - x) volume = volume := by
    have hrw : (fun y : EuclideanSpace ℝ (Fin d) => y - x) = (fun y => y + (-x)) := by
      funext y; rw [sub_eq_add_neg]
    rw [hrw, map_add_right_eq_self]
  rw [hmapC, Measure.map_addHaar_smul volume ht.ne', Measure.map_smul, map_add_left_eq_self]
  congr 1
  rw [finrank_euclideanSpace_fin, abs_of_nonneg (by positivity)]

/-- **Affine change of variables (the crux).** For `0 < t`, the singular line integrand over
the ball transforms, under `z = x + t • (y - x)`, into the same integrand over the contracted
region `x + t • (ball c r - x)`, with Jacobian factor `t^{-(d+1)}`. This is the change of
variables at the level of the (nonnegative) `lintegral`, built from the pushforward Jacobian
`map_affine_dilation` together with translation invariance. -/
private theorem potential_inner_cov {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 < t)
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : MeasurableSet s) :
    ∫⁻ y in s, ‖fderiv ℝ φ (x + t • (y - x))‖ₑ * ‖y - x‖ₑ ∂volume
      = ENNReal.ofReal (t ^ (-((d : ℤ) + 1)))
          * ∫⁻ z in (fun y => x + t • (y - x)) '' s, ‖fderiv ℝ φ z‖ₑ * ‖z - x‖ₑ ∂volume := by
  set e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun y => x + t • (y - x) with he
  set h : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun z => ‖fderiv ℝ φ z‖ₑ * ‖z - x‖ₑ with hh_def
  have hemb : MeasurableEmbedding e := by
    have h1 : MeasurableEmbedding (fun u : EuclideanSpace ℝ (Fin d) => x + u) :=
      measurableEmbedding_addLeft x
    have h2 : MeasurableEmbedding (fun w : EuclideanSpace ℝ (Fin d) => t • w) :=
      measurableEmbedding_const_smul₀ ht.ne'
    have h3 : MeasurableEmbedding (fun y : EuclideanSpace ℝ (Fin d) => y - x) := by
      have hrw : (fun y : EuclideanSpace ℝ (Fin d) => y - x) = (fun y => y + (-x)) := by
        funext y; rw [sub_eq_add_neg]
      rw [hrw]; exact measurableEmbedding_addRight (-x)
    exact (h1.comp h2).comp h3
  have hhmeas : Measurable h := by
    refine Measurable.mul ?_ ?_
    · exact ((hφ.continuous_fderiv (by simp)).enorm).measurable
    · exact ((continuous_id.sub continuous_const).enorm).measurable
  have hGmeas : Measurable
      (fun y : EuclideanSpace ℝ (Fin d) => ‖fderiv ℝ φ (x + t • (y - x))‖ₑ * ‖y - x‖ₑ) := by
    refine Measurable.mul ?_ ?_
    · exact (((hφ.continuous_fderiv (by simp)).comp (by fun_prop)).enorm).measurable
    · exact ((continuous_id.sub continuous_const).enorm).measurable
  have huimg : MeasurableSet (e '' s) := hemb.measurableSet_image.mpr hs
  have hmap : Measure.map e volume = ENNReal.ofReal ((t ^ d)⁻¹) • volume := by
    rw [he]; exact map_affine_dilation x ht
  -- Change of variables: `∫ over image = t^d * ∫ (h ∘ e) over s`.
  have hset := setLIntegral_map (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    huimg hhmeas hemb.measurable
  rw [hmap, setLIntegral_smul_measure,
    Set.preimage_image_eq s hemb.injective] at hset
  -- `hset : ofReal ((t^d)⁻¹) • ∫ z in e '' s, h z = ∫ y in s, h (e y)`.
  have hcov : ∫⁻ z in e '' s, h z ∂volume
      = ENNReal.ofReal (t ^ d) * ∫⁻ y in s, h (e y) ∂volume := by
    calc ∫⁻ z in e '' s, h z ∂volume
        = ENNReal.ofReal (t ^ d)
            * (ENNReal.ofReal ((t ^ d)⁻¹) • ∫⁻ z in e '' s, h z ∂volume) := by
          rw [smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]
      _ = ENNReal.ofReal (t ^ d) * ∫⁻ y in s, h (e y) ∂volume := by rw [hset]
  -- Pointwise `h (e y) = ofReal t * (target integrand)`.
  have hpt : ∀ y : EuclideanSpace ℝ (Fin d),
      h (e y) = ENNReal.ofReal t * (‖fderiv ℝ φ (x + t • (y - x))‖ₑ * ‖y - x‖ₑ) := by
    intro y
    simp only [he, hh_def]
    have hsub : x + t • (y - x) - x = t • (y - x) := by abel
    rw [hsub, enorm_smul, Real.enorm_eq_ofReal ht.le]
    ring
  have hstep : ∫⁻ y in s, h (e y) ∂volume
      = ENNReal.ofReal t
          * ∫⁻ y in s, ‖fderiv ℝ φ (x + t • (y - x))‖ₑ * ‖y - x‖ₑ ∂volume := by
    rw [setLIntegral_congr_fun hs (fun y _ => hpt y), lintegral_const_mul _ hGmeas]
  -- Solve for the target LHS.
  rw [hcov, hstep, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  have hz : (-((d : ℤ) + 1)) + ((d + 1 : ℕ) : ℤ) = 0 := by push_cast; ring
  have harith : t ^ (-((d : ℤ) + 1)) * t ^ d * t = 1 := by
    rw [mul_assoc, ← pow_succ, ← zpow_natCast t (d + 1), ← zpow_add₀ ht.ne', hz, zpow_zero]
  rw [harith, ENNReal.ofReal_one, one_mul]

/-- **Tail bound, `lintegral` form.** The ENNReal integral of the singular kernel over `Ioc a 1`
is bounded by `ofReal (a^{-d}/d)`. This is `tail_integral_bound` transported to `ℝ≥0∞`, ready to
feed the per-point Riesz estimate in the kernel bound. -/
private theorem tail_lintegral_bound (hd : 0 < d) {a : ℝ} (ha : 0 < a) :
    ∫⁻ t in Ioc a (1 : ℝ), ENNReal.ofReal (t ^ (-((d : ℤ) + 1))) ∂volume
      ≤ ENNReal.ofReal (a ^ (-(d : ℤ)) / d) := by
  rcases le_or_gt a 1 with hle | hgt
  · have hcont : ContinuousOn (fun t : ℝ => t ^ (-((d : ℤ) + 1))) (Set.Icc a 1) :=
      (continuous_id.continuousOn).zpow₀ _
        (fun t ht => Or.inl (lt_of_lt_of_le ha ht.1).ne')
    have hint : IntegrableOn (fun t : ℝ => t ^ (-((d : ℤ) + 1))) (Ioc a 1) volume :=
      (hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    have hnn : 0 ≤ᵐ[volume.restrict (Ioc a 1)] fun t : ℝ => t ^ (-((d : ℤ) + 1)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have : 0 < t := lt_of_lt_of_le ha ht.1.le
      positivity
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    apply ENNReal.ofReal_le_ofReal
    rw [← intervalIntegral.integral_of_le hle]
    exact tail_integral_bound hd ha
  · have hempty : Ioc a (1 : ℝ) = ∅ := Ioc_eq_empty (by linarith)
    rw [hempty, Measure.restrict_empty, lintegral_zero_measure]
    exact bot_le

/-- **Per-point Riesz factor.** Integrating the singular kernel over the admissible cone of
scales `{t : ‖z - x‖ < 2 r t}` produces the Riesz weight `(2 r)^d / (d ‖z - x‖^d)`. This packages
the change of the indicator region into `Ioc a 1` and applies `tail_lintegral_bound`. -/
private theorem inner_t_bound (hd : 0 < d) {r w : ℝ} (hr : 0 < r) (hw : 0 < w) :
    ∫⁻ t in Ioc (0 : ℝ) 1, {p : ℝ | w < 2 * r * p}.indicator
        (fun p => ENNReal.ofReal (p ^ (-((d : ℤ) + 1)))) t ∂volume
      ≤ ENNReal.ofReal ((2 * r) ^ d / (d * w ^ d)) := by
  set a := w / (2 * r) with ha_def
  have ha : 0 < a := by rw [ha_def]; positivity
  have h2r : (0 : ℝ) < 2 * r := by positivity
  have hset : {p : ℝ | w < 2 * r * p} = Ioi a := by
    ext p
    rw [Set.mem_setOf_eq, Set.mem_Ioi, ha_def, div_lt_iff₀ h2r, mul_comm p (2 * r)]
  rw [hset, ← lintegral_indicator measurableSet_Ioc]
  simp only [Set.indicator_indicator]
  rw [show Ioc (0 : ℝ) 1 ∩ Ioi a = Ioc a 1 by rw [Set.Ioc_inter_Ioi, max_eq_right ha.le],
    lintegral_indicator measurableSet_Ioc]
  refine (tail_lintegral_bound hd ha).trans (le_of_eq ?_)
  congr 1
  rw [ha_def, zpow_neg, zpow_natCast, div_pow, inv_div, div_div, mul_comm (w ^ d) (d : ℝ)]

/-- **Morrey kernel bound.** The double gradient line integral over the ball is controlled by the
Riesz potential of the gradient. Proof: Tonelli swap, the affine change of variables
`potential_inner_cov` for each scale `t`, the region containment `B_t ⊆ B ∩ ball x (2 r t)`, a
second Tonelli swap, and the per-point Riesz factor `inner_t_bound`. -/
private theorem kernel_bound {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hd : 0 < d) (c x : EuclideanSpace ℝ (Fin d))
    {r : ℝ} (hr : 0 < r) (hx : x ∈ ball c r) :
    ∫⁻ y in ball c r, ∫⁻ t in Ioc (0 : ℝ) 1,
        ‖fderiv ℝ φ (x + t • (y - x))‖ₑ * ‖y - x‖ₑ ∂volume ∂volume
      ≤ ENNReal.ofReal ((2 * r) ^ d / d)
          * ∫⁻ z in ball c r, ‖fderiv ℝ φ z‖ₑ / ‖z - x‖ₑ ^ (d - 1) ∂volume := by
  have hB : MeasurableSet (ball c r) := measurableSet_ball
  have hfd : Continuous (fun z : EuclideanSpace ℝ (Fin d) => fderiv ℝ φ z) :=
    hφ.continuous_fderiv (by simp)
  set h : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun z => ‖fderiv ℝ φ z‖ₑ * ‖z - x‖ₑ with hh_def
  have hhmeas : Measurable h :=
    (hfd.enorm.measurable).mul ((continuous_id.sub continuous_const).enorm.measurable)
  -- The transformed region is contained in the ball intersected with a Euclidean ball at `x`.
  have hregion : ∀ t ∈ Ioc (0 : ℝ) 1,
      (fun y => x + t • (y - x)) '' (ball c r) ⊆ ball c r ∩ ball x (2 * r * t) := by
    intro t ht z hz
    obtain ⟨y, hy, rfl⟩ := hz
    refine ⟨?_, ?_⟩
    · have hcombo := (convex_ball c r) hx hy (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t)
        ht.1.le (by ring)
      have : (1 - t) • x + t • y = x + t • (y - x) := by rw [sub_smul, one_smul, smul_sub]; abel
      rwa [this] at hcombo
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact norm_smul_sub_lt_two_mul hx hy ht.1
  -- Step 1: Tonelli swap.
  rw [show (∫⁻ y in ball c r, ∫⁻ t in Ioc (0 : ℝ) 1,
        ‖fderiv ℝ φ (x + t • (y - x))‖ₑ * ‖y - x‖ₑ ∂volume ∂volume)
      = ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y in ball c r,
        ‖fderiv ℝ φ (x + t • (y - x))‖ₑ * ‖y - x‖ₑ ∂volume ∂volume from by
    apply lintegral_lintegral_swap
    apply Measurable.aemeasurable
    apply Measurable.mul
    · exact ((hfd.comp (by fun_prop)).enorm).measurable
    · exact ((show Continuous (fun p : EuclideanSpace ℝ (Fin d) × ℝ => p.1 - x) by
        fun_prop).enorm).measurable]
  -- Step 2: change of variables for each `t`, then bound the region.
  have hbound : ∀ t ∈ Ioc (0 : ℝ) 1,
      ∫⁻ y in ball c r, ‖fderiv ℝ φ (x + t • (y - x))‖ₑ * ‖y - x‖ₑ ∂volume
        ≤ ∫⁻ z in ball c r,
            ENNReal.ofReal (t ^ (-((d : ℤ) + 1))) * (ball x (2 * r * t)).indicator h z ∂volume := by
    intro t ht
    rw [potential_inner_cov hφ x ht.1 hB,
      lintegral_const_mul _ (hhmeas.indicator (measurableSet_ball))]
    refine mul_le_mul' le_rfl ?_
    calc ∫⁻ z in (fun y => x + t • (y - x)) '' (ball c r), h z ∂volume
        ≤ ∫⁻ z in ball c r ∩ ball x (2 * r * t), h z ∂volume :=
          lintegral_mono_set (hregion t ht)
      _ = ∫⁻ z in ball c r, (ball x (2 * r * t)).indicator h z ∂volume := by
          rw [← lintegral_indicator (hB.inter measurableSet_ball), ← lintegral_indicator hB,
            Set.indicator_indicator]
  have hzpow_meas : Measurable (fun t : ℝ => t ^ (-((d : ℤ) + 1))) := by
    have hrw : (fun t : ℝ => t ^ (-((d : ℤ) + 1))) = fun t : ℝ => (t ^ (d + 1))⁻¹ := by
      funext t
      rw [zpow_neg, show ((d : ℤ) + 1) = ((d + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    rw [hrw]; exact (measurable_id.pow_const (d + 1)).inv
  -- Per-point Riesz bound (holds for every `z`; at `z = x` the left side vanishes).
  have hper : ∀ z : EuclideanSpace ℝ (Fin d),
      ∫⁻ t in Ioc (0 : ℝ) 1,
          ENNReal.ofReal (t ^ (-((d : ℤ) + 1))) * (ball x (2 * r * t)).indicator h z ∂volume
        ≤ ENNReal.ofReal ((2 * r) ^ d / d) * (‖fderiv ℝ φ z‖ₑ / ‖z - x‖ₑ ^ (d - 1)) := by
    intro z
    by_cases hzx : z = x
    · subst hzx
      have h0 : h z = 0 := by rw [hh_def]; simp
      have hzero : ∀ t : ℝ,
          ENNReal.ofReal (t ^ (-((d : ℤ) + 1))) * (ball z (2 * r * t)).indicator h z = 0 := by
        intro t; simp [h0]
      calc ∫⁻ t in Ioc (0 : ℝ) 1,
              ENNReal.ofReal (t ^ (-((d : ℤ) + 1))) * (ball z (2 * r * t)).indicator h z ∂volume
          = ∫⁻ _t in Ioc (0 : ℝ) 1, (0 : ℝ≥0∞) ∂volume :=
            setLIntegral_congr_fun measurableSet_Ioc (fun t _ => hzero t)
        _ = 0 := by simp
        _ ≤ _ := bot_le
    · have hw : 0 < ‖z - x‖ := by rw [norm_pos_iff]; exact sub_ne_zero.mpr hzx
      have hd1 : d - 1 + 1 = d := Nat.succ_pred_eq_of_pos hd
      have hwe : ‖z - x‖ₑ = ENNReal.ofReal ‖z - x‖ := (ofReal_norm (z - x)).symm
      have hNe : ‖fderiv ℝ φ z‖ₑ = ENNReal.ofReal ‖fderiv ℝ φ z‖ := (ofReal_norm _).symm
      have hne : ‖z - x‖ ^ (d - 1) ≠ 0 := by positivity
      have hreal : ‖fderiv ℝ φ z‖ * ‖z - x‖ * ((2 * r) ^ d / (d * ‖z - x‖ ^ d))
          = (2 * r) ^ d / d * (‖fderiv ℝ φ z‖ / ‖z - x‖ ^ (d - 1)) := by
        rw [show ‖z - x‖ ^ d = ‖z - x‖ ^ (d - 1) * ‖z - x‖ from by rw [← pow_succ, hd1]]
        field_simp
      have hL : h z * ENNReal.ofReal ((2 * r) ^ d / (d * ‖z - x‖ ^ d))
          = ENNReal.ofReal (‖fderiv ℝ φ z‖ * ‖z - x‖ * ((2 * r) ^ d / (d * ‖z - x‖ ^ d))) := by
        simp only [hh_def]
        rw [hwe, hNe, ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
      have hR : ENNReal.ofReal ((2 * r) ^ d / d) * (‖fderiv ℝ φ z‖ₑ / ‖z - x‖ₑ ^ (d - 1))
          = ENNReal.ofReal ((2 * r) ^ d / d * (‖fderiv ℝ φ z‖ / ‖z - x‖ ^ (d - 1))) := by
        rw [hNe, hwe, ← ENNReal.ofReal_pow (norm_nonneg _),
          ← ENNReal.ofReal_div_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      have hzeq : h z * ENNReal.ofReal ((2 * r) ^ d / (d * ‖z - x‖ ^ d))
          = ENNReal.ofReal ((2 * r) ^ d / d) * (‖fderiv ℝ φ z‖ₑ / ‖z - x‖ₑ ^ (d - 1)) := by
        rw [hL, hR, hreal]
      have hstep1 : ∀ t : ℝ,
          ENNReal.ofReal (t ^ (-((d : ℤ) + 1))) * (ball x (2 * r * t)).indicator h z
            = h z * {p : ℝ | ‖z - x‖ < 2 * r * p}.indicator
                (fun p => ENNReal.ofReal (p ^ (-((d : ℤ) + 1)))) t := by
        intro t
        by_cases hc : ‖z - x‖ < 2 * r * t
        · rw [Set.indicator_of_mem (by rw [mem_ball, dist_eq_norm]; exact hc) h,
            Set.indicator_of_mem (show t ∈ {p : ℝ | ‖z - x‖ < 2 * r * p} from hc), mul_comm]
        · rw [Set.indicator_of_notMem (by rw [mem_ball, dist_eq_norm]; exact hc) h,
            Set.indicator_of_notMem (show t ∉ {p : ℝ | ‖z - x‖ < 2 * r * p} from hc),
            mul_zero, mul_zero]
      calc ∫⁻ t in Ioc (0 : ℝ) 1,
              ENNReal.ofReal (t ^ (-((d : ℤ) + 1))) * (ball x (2 * r * t)).indicator h z ∂volume
          = ∫⁻ t in Ioc (0 : ℝ) 1, h z * {p : ℝ | ‖z - x‖ < 2 * r * p}.indicator
              (fun p => ENNReal.ofReal (p ^ (-((d : ℤ) + 1)))) t ∂volume :=
            setLIntegral_congr_fun measurableSet_Ioc (fun t _ => hstep1 t)
        _ = h z * ∫⁻ t in Ioc (0 : ℝ) 1, {p : ℝ | ‖z - x‖ < 2 * r * p}.indicator
              (fun p => ENNReal.ofReal (p ^ (-((d : ℤ) + 1)))) t ∂volume :=
            lintegral_const_mul _ ((ENNReal.continuous_ofReal.measurable.comp hzpow_meas).indicator
              (measurableSet_lt measurable_const (by fun_prop)))
        _ ≤ h z * ENNReal.ofReal ((2 * r) ^ d / (d * ‖z - x‖ ^ d)) :=
            mul_le_mul' le_rfl (inner_t_bound hd hr hw)
        _ = _ := hzeq
  calc ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y in ball c r,
          ‖fderiv ℝ φ (x + t • (y - x))‖ₑ * ‖y - x‖ₑ ∂volume ∂volume
      ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ z in ball c r,
          ENNReal.ofReal (t ^ (-((d : ℤ) + 1))) * (ball x (2 * r * t)).indicator h z
          ∂volume ∂volume :=
        lintegral_mono_ae (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact hbound t ht)
    -- Step 3: second Tonelli swap.
    _ = ∫⁻ z in ball c r, ∫⁻ t in Ioc (0 : ℝ) 1,
          ENNReal.ofReal (t ^ (-((d : ℤ) + 1))) * (ball x (2 * r * t)).indicator h z
          ∂volume ∂volume := by
        apply lintegral_lintegral_swap
        apply Measurable.aemeasurable
        apply Measurable.mul
        · exact (ENNReal.continuous_ofReal.measurable.comp hzpow_meas).comp measurable_fst
        · have hrw : (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
              (ball x (2 * r * p.1)).indicator h p.2)
              = {q : ℝ × EuclideanSpace ℝ (Fin d) | dist q.2 x < 2 * r * q.1}.indicator
                (fun q => h q.2) := by
            funext p
            by_cases hc : dist p.2 x < 2 * r * p.1
            · rw [Set.indicator_of_mem (show p.2 ∈ ball x (2 * r * p.1) from mem_ball.mpr hc) h,
                Set.indicator_of_mem
                  (show p ∈ {q : ℝ × EuclideanSpace ℝ (Fin d) | dist q.2 x < 2 * r * q.1} from hc)]
            · rw [Set.indicator_of_notMem
                  (show p.2 ∉ ball x (2 * r * p.1) from fun hm => hc (mem_ball.mp hm)) h,
                Set.indicator_of_notMem
                  (show p ∉ {q : ℝ × EuclideanSpace ℝ (Fin d) | dist q.2 x < 2 * r * q.1} from hc)]
          rw [hrw]
          exact (hhmeas.comp measurable_snd).indicator
            (measurableSet_lt (by fun_prop) (by fun_prop))
    -- Step 4: per-point Riesz bound and reassembly.
    _ ≤ ∫⁻ z in ball c r,
          ENNReal.ofReal ((2 * r) ^ d / d) * (‖fderiv ℝ φ z‖ₑ / ‖z - x‖ₑ ^ (d - 1)) ∂volume :=
        setLIntegral_mono' hB (fun z _ => hper z)
    _ = ENNReal.ofReal ((2 * r) ^ d / d)
          * ∫⁻ z in ball c r, ‖fderiv ℝ φ z‖ₑ / ‖z - x‖ₑ ^ (d - 1) ∂volume := by
        have hg : Measurable (fun z : EuclideanSpace ℝ (Fin d) =>
            ‖fderiv ℝ φ z‖ₑ / ‖z - x‖ₑ ^ (d - 1)) :=
          (hfd.enorm.measurable).div
            (((continuous_id.sub continuous_const).enorm).measurable.pow_const _)
        rw [lintegral_const_mul _ hg]

/-- **The Riesz potential is integrable.** For smooth `φ` and `x` in the ball, the singular
integrand `‖∇φ‖ / dist x ·^{d-1}` is integrable on the ball: the singularity `dist x ·^{-(d-1)}`
has exponent `d - 1 < d`, and `‖∇φ‖` is bounded on the compact closure. This is what makes the
right-hand side of the potential estimate finite (hence the estimate meaningful). -/
private theorem riesz_potential_integrableOn {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hd : 0 < d) (c x : EuclideanSpace ℝ (Fin d)) {r : ℝ}
    (hr : 0 < r) (hx : x ∈ ball c r) :
    IntegrableOn (fun z => ‖fderiv ℝ φ z‖ / dist x z ^ (d - 1)) (ball c r) volume := by
  have hfd : Continuous (fun z : EuclideanSpace ℝ (Fin d) => fderiv ℝ φ z) :=
    hφ.continuous_fderiv (by simp)
  have hfrk : 1 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) := by
    rw [finrank_euclideanSpace_fin]; exact hd
  obtain ⟨M, hM⟩ :=
    (((isCompact_closedBall c (3 * r)).image hfd.norm).bddAbove)
  have hMbound : ∀ z ∈ closedBall c (3 * r), ‖fderiv ℝ φ z‖ ≤ M :=
    fun z hz => hM ⟨z, hz, rfl⟩
  -- The translated integrand `f w = ‖∇φ (x + w)‖ / ‖w‖^{d-1}` is integrable on `ball 0 (2 r)`.
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hd)
  have hne0 : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), w ≠ 0 := by
    rw [ae_iff, show {w : EuclideanSpace ℝ (Fin d) | ¬ w ≠ 0} = {0} from by ext w; simp]
    exact measure_singleton 0
  have hf : IntegrableOn (fun w => ‖fderiv ℝ φ (x + w)‖ / ‖w‖ ^ (d - 1))
      (ball 0 (2 * r)) volume := by
    apply MeasureTheory.integrableOn_ball_of_norm_le_rpow (C := M) (α := ((d - 1 : ℕ) : ℝ)) hfrk
    · rw [finrank_euclideanSpace_fin]
      exact_mod_cast Nat.sub_lt hd Nat.one_pos
    · filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hne0] with w hw hw0
      have hwpos : 0 < ‖w‖ := by rw [norm_pos_iff]; exact hw0
      have hxw : x + w ∈ closedBall c (3 * r) := by
        rw [mem_closedBall, dist_eq_norm]
        have : ‖x + w - c‖ ≤ ‖x - c‖ + ‖w‖ := by
          rw [show x + w - c = (x - c) + w from by abel]; exact norm_add_le _ _
        have hxc : ‖x - c‖ < r := by rw [← dist_eq_norm]; rwa [mem_ball] at hx
        have hwlt : ‖w‖ < 2 * r := by rw [← dist_zero_right, ← mem_ball]; exact hw
        linarith
      have hnn : (0 : ℝ) ≤ ‖fderiv ℝ φ (x + w)‖ / ‖w‖ ^ (d - 1) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn, Real.rpow_neg (norm_nonneg _), Real.rpow_natCast,
        div_le_iff₀ (by positivity), mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
      exact hMbound _ hxw
    · refine Measurable.aestronglyMeasurable ?_
      exact ((hfd.comp (continuous_const.add continuous_id)).norm.measurable).div
        ((continuous_norm.pow (d - 1)).measurable)
  -- Transfer back along the translation `w ↦ x + w`.
  have hpre : (fun z => ‖fderiv ℝ φ z‖ / dist x z ^ (d - 1)) ∘ (fun w => x + w)
      = fun w => ‖fderiv ℝ φ (x + w)‖ / ‖w‖ ^ (d - 1) := by
    funext w
    simp only [Function.comp_apply, dist_eq_norm, show x - (x + w) = -w from by abel, norm_neg]
  have hmp : MeasurePreserving (fun w : EuclideanSpace ℝ (Fin d) => x + w) volume volume :=
    measurePreserving_add_left volume x
  rw [← hmp.integrableOn_comp_preimage (measurableEmbedding_addLeft x)]
  rw [show (fun w => x + w) ⁻¹' ball c r = ball (c - x) r from by
    ext w
    simp only [Set.mem_preimage, mem_ball, dist_eq_norm,
      show x + w - c = w - (c - x) from by abel]]
  rw [hpre]
  exact hf.mono_set (by
    intro w hw
    rw [mem_ball, dist_zero_right]
    have : dist w (c - x) < r := by rwa [mem_ball] at hw
    rw [dist_eq_norm] at this
    have hcx : ‖c - x‖ < r := by rw [← dist_eq_norm, dist_comm]; rwa [mem_ball] at hx
    have htri : ‖w‖ ≤ ‖w - (c - x)‖ + ‖c - x‖ := by
      have := norm_add_le (w - (c - x)) (c - x)
      rwa [sub_add_cancel] at this
    linarith)

/-- **Morrey potential estimate for smooth functions.** For a smooth `φ` and any point `x` of a
ball, the oscillation of `φ` about its ball average is controlled by the Riesz potential of the
gradient, with a dimensional constant `Cd = 2^d / (d ω_d)`. This is the analytic heart of the
Morrey embedding, assembled from the ray-FTC average identity, the kernel bound, and the
integrability of the Riesz potential. -/
theorem exists_potential_bound (hd : 0 < d) :
    ∃ Cd : ℝ≥0, ∀ (φ : EuclideanSpace ℝ (Fin d) → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      ∀ (c : EuclideanSpace ℝ (Fin d)) {r : ℝ}, 0 < r → ∀ x ∈ Metric.ball c r,
        |φ x - ⨍ y in Metric.ball c r, φ y|
          ≤ (Cd : ℝ) * ∫ y in Metric.ball c r,
              ‖fderiv ℝ φ y‖ / dist x y ^ (d - 1) := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hd)
  set ω : ℝ := volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hω_def
  have hω_pos : 0 < ω := by
    rw [hω_def, measureReal_def, ENNReal.toReal_pos_iff]
    exact ⟨measure_ball_pos volume 0 one_pos, measure_ball_lt_top⟩
  refine ⟨⟨2 ^ d / (d * ω), by positivity⟩, ?_⟩
  intro φ hφ c r hr x hx
  have hB : MeasurableSet (ball c r) := measurableSet_ball
  have hfd : Continuous (fun z : EuclideanSpace ℝ (Fin d) => fderiv ℝ φ z) :=
    hφ.continuous_fderiv (by simp)
  have hvolpos : 0 < volume.real (ball c r) := by
    rw [measureReal_def, ENNReal.toReal_pos_iff]
    exact ⟨measure_ball_pos volume c hr, measure_ball_lt_top⟩
  have hvol_eq : volume.real (ball c r) = r ^ d * ω := by
    rw [hω_def, measureReal_def, Measure.addHaar_ball_of_pos volume c hr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), finrank_euclideanSpace_fin, measureReal_def]
  -- Abbreviations for the ray integral `I`, the gradient integrand `g`, and its Riesz `lintegral`.
  set I : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun y => ∫ t in (0 : ℝ)..1, (fderiv ℝ φ (x + t • (y - x))) (y - x) with hI_def
  set g : EuclideanSpace ℝ (Fin d) → ℝ := fun z => ‖fderiv ℝ φ z‖ / dist x z ^ (d - 1) with hg_def
  set Rl : ℝ≥0∞ := ∫⁻ z in ball c r, ‖fderiv ℝ φ z‖ₑ / ‖z - x‖ₑ ^ (d - 1) ∂volume with hRl_def
  have hg_nn : ∀ z, 0 ≤ g z := fun z => by rw [hg_def]; positivity
  have hnex : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), z ≠ x := by
    rw [ae_iff, show {z : EuclideanSpace ℝ (Fin d) | ¬ z ≠ x} = {x} from by ext z; simp]
    exact measure_singleton x
  -- `Rl` rewrites as a genuine `enorm` integral, hence is finite and its `toReal` is `∫ g`.
  have hRl_enorm : Rl = ∫⁻ z in ball c r, ‖g z‖ₑ ∂volume := by
    rw [hRl_def]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hnex] with z hz
    have hzx : 0 < ‖z - x‖ := by rw [norm_pos_iff]; exact sub_ne_zero.mpr hz
    have hdist : dist x z = ‖z - x‖ := by rw [dist_eq_norm, ← neg_sub z x, norm_neg]
    rw [Real.enorm_eq_ofReal (hg_nn z)]
    simp only [hg_def, hdist]
    rw [← ofReal_norm (fderiv ℝ φ z), ← ofReal_norm (z - x),
      ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_div_of_pos (by positivity)]
  have hgint : IntegrableOn g (ball c r) volume := riesz_potential_integrableOn hφ hd c x hr hx
  have hRl_lt : Rl < ⊤ := by
    rw [hRl_enorm]; exact hasFiniteIntegral_iff_enorm.mp hgint.2
  have hReq : Rl.toReal = ∫ y in ball c r, g y ∂volume := by
    rw [hRl_enorm, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg_nn) hgint.1]
    congr 1
    refine lintegral_congr fun z => ?_
    rw [Real.enorm_eq_ofReal (hg_nn z)]
  -- Continuity of the ray integral in `y`.
  have hIcont : Continuous I := by
    rw [hI_def]
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact (hfd.comp (by fun_prop)).clm_apply (by fun_prop)
  -- Per-point domination of `I` by the gradient line integral.
  have hper_y : ∀ y, ENNReal.ofReal |I y| ≤
      ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (x + t • (y - x))‖ₑ * ‖y - x‖ₑ ∂volume := by
    intro y
    have hJc : Continuous (fun t : ℝ => (fderiv ℝ φ (x + t • (y - x))) (y - x)) :=
      (hfd.comp (by fun_prop)).clm_apply continuous_const
    calc ENNReal.ofReal |I y|
        ≤ ENNReal.ofReal (∫ t in Ioc (0 : ℝ) 1,
            |(fderiv ℝ φ (x + t • (y - x))) (y - x)|) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hI_def, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
          exact intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ = ∫⁻ t in Ioc (0 : ℝ) 1,
            ENNReal.ofReal |(fderiv ℝ φ (x + t • (y - x))) (y - x)| ∂volume := by
          rw [ofReal_integral_eq_lintegral_ofReal
            ((hJc.abs.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
            (ae_of_all _ (fun t => abs_nonneg _))]
      _ ≤ ∫⁻ t in Ioc (0 : ℝ) 1,
            ‖fderiv ℝ φ (x + t • (y - x))‖ₑ * ‖y - x‖ₑ ∂volume := by
          refine lintegral_mono fun t => ?_
          calc ENNReal.ofReal |(fderiv ℝ φ (x + t • (y - x))) (y - x)|
              ≤ ENNReal.ofReal (‖fderiv ℝ φ (x + t • (y - x))‖ * ‖y - x‖) := by
                apply ENNReal.ofReal_le_ofReal
                rw [← Real.norm_eq_abs]
                exact (fderiv ℝ φ (x + t • (y - x))).le_opNorm (y - x)
            _ = ‖fderiv ℝ φ (x + t • (y - x))‖ₑ * ‖y - x‖ₑ := by
                rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
  -- The kernel bound and its finiteness.
  have hker := kernel_bound hφ hd c x hr hx
  rw [← hRl_def] at hker
  have hDl_lt : (∫⁻ y in ball c r, ∫⁻ t in Ioc (0 : ℝ) 1,
      ‖fderiv ℝ φ (x + t • (y - x))‖ₑ * ‖y - x‖ₑ ∂volume ∂volume) < ⊤ :=
    lt_of_le_of_lt hker (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hRl_lt)
  -- Assemble.
  rw [abs_sub_comm, oscillation_eq_average_ray hφ c x hr, setAverage_eq, smul_eq_mul, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (volume.real (ball c r))⁻¹)]
  have hmain : |∫ y in ball c r, I y ∂volume|
      ≤ (2 * r) ^ d / d * ∫ y in ball c r, g y ∂volume := by
    calc |∫ y in ball c r, I y ∂volume|
        ≤ ∫ y in ball c r, |I y| ∂volume := abs_integral_le_integral_abs
      _ = (∫⁻ y in ball c r, ENNReal.ofReal |I y| ∂volume).toReal := by
          rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun y => abs_nonneg _))
            hIcont.abs.aestronglyMeasurable]
      _ ≤ (∫⁻ y in ball c r, ∫⁻ t in Ioc (0 : ℝ) 1,
            ‖fderiv ℝ φ (x + t • (y - x))‖ₑ * ‖y - x‖ₑ ∂volume ∂volume).toReal :=
          ENNReal.toReal_mono hDl_lt.ne (lintegral_mono hper_y)
      _ ≤ (ENNReal.ofReal ((2 * r) ^ d / d) * Rl).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hRl_lt).ne hker
      _ = (2 * r) ^ d / d * ∫ y in ball c r, g y ∂volume := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hReq]
  calc (volume.real (ball c r))⁻¹ * |∫ y in ball c r, I y ∂volume|
      ≤ (volume.real (ball c r))⁻¹ * ((2 * r) ^ d / d * ∫ y in ball c r, g y ∂volume) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = ((⟨2 ^ d / (d * ω), by positivity⟩ : ℝ≥0) : ℝ) * ∫ y in ball c r, g y ∂volume := by
        rw [← mul_assoc]
        congr 1
        rw [hvol_eq, show ((⟨2 ^ d / (d * ω), by positivity⟩ : ℝ≥0) : ℝ) = 2 ^ d / (d * ω) from rfl,
          mul_pow]
        have hrd : (r : ℝ) ^ d ≠ 0 := by positivity
        field_simp

end EllipticDirichlet.Embedding
