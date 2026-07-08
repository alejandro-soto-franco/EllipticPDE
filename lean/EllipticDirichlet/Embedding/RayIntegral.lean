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

end EllipticDirichlet.Embedding
