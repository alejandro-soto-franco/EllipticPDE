/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticDirichlet.Embedding.RayIntegral
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Tactic.Module

/-!
# Riesz-kernel `Lᵖ` bound for the Morrey embedding

For `p > d` the `(d-1)`-Riesz potential of an `Lᵖ` function over a ball of radius `R`
centred at the base point is controlled by `Cdp · R^{1-d/p} · ‖g‖_{Lᵖ}`. The exponent
`1 - d/p` is the Morrey Hölder exponent, produced here from Hölder's inequality with the
conjugate exponent `q = p/(p-1)` together with the radial `L^q` norm of the singular kernel.

The kernel-norm computation is isolated in the private lemma `setIntegral_ball_dist_rpow`,
a closed-form value for the radial integral `∫_{B(x,R)} dist x y^s` over a ball centred at the
singularity, valid for `s > -d`.
-/

open MeasureTheory Set Metric
open scoped NNReal ENNReal

noncomputable section

namespace EllipticDirichlet.Embedding

variable {d : ℕ}

/-- **Radial power integral over a ball centred at the singularity.** For `s > -d`, the integral
of `dist x ·^s` over the ball `B(x, R)` has the closed form `d · ω_d · R^{s+d}/(s+d)`, where
`ω_d` is the volume of the unit ball. Proof: translate to the origin, then apply the polar
change of variables `integral_fun_norm_addHaar` and evaluate the resulting `1`-D radial integral
with `integral_rpow`. This is the isolated kernel-norm computation feeding the Hölder step. -/
private theorem setIntegral_ball_dist_rpow (hd : 0 < d) (x : EuclideanSpace ℝ (Fin d))
    {R : ℝ} (hR : 0 < R) {s : ℝ} (hs : -(d : ℝ) < s) :
    ∫ y in ball x R, dist x y ^ s ∂volume
      = (d : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
          * (R ^ (s + (d : ℝ)) / (s + (d : ℝ))) := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hd)
  -- Translate the integral to the origin.
  have hmp : MeasurePreserving (fun w : EuclideanSpace ℝ (Fin d) => x + w) volume volume :=
    measurePreserving_add_left volume x
  have hpre : (fun w : EuclideanSpace ℝ (Fin d) => x + w) ⁻¹' ball x R
      = ball (0 : EuclideanSpace ℝ (Fin d)) R := by
    ext w
    simp only [Set.mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
  rw [show (∫ y in ball x R, dist x y ^ s ∂volume)
        = ∫ w in ball (0 : EuclideanSpace ℝ (Fin d)) R, ‖w‖ ^ s ∂volume from by
    rw [← hmp.setIntegral_preimage_emb (measurableEmbedding_addLeft x)
          (fun y => dist x y ^ s) (ball x R), hpre]
    refine setIntegral_congr_fun measurableSet_ball (fun w _ => ?_)
    rw [dist_eq_norm, show x - (x + w) = -w from by abel, norm_neg]]
  -- Rewrite as an integral over the whole space of a radial function.
  rw [← integral_indicator
      (measurableSet_ball : MeasurableSet (ball (0 : EuclideanSpace ℝ (Fin d)) R))]
  rw [show (fun w : EuclideanSpace ℝ (Fin d) => (ball (0 : EuclideanSpace ℝ (Fin d)) R).indicator
        (fun w => ‖w‖ ^ s) w) = (fun w => (Set.Iio R).indicator (fun t : ℝ => t ^ s) ‖w‖) from by
    funext w
    by_cases hw : ‖w‖ < R
    · rw [Set.indicator_of_mem (by rw [mem_ball, dist_zero_right]; exact hw),
        Set.indicator_of_mem (show ‖w‖ ∈ Set.Iio R from hw)]
    · rw [Set.indicator_of_notMem (by rw [mem_ball, dist_zero_right]; exact hw),
        Set.indicator_of_notMem (show ‖w‖ ∉ Set.Iio R from hw)]]
  rw [integral_fun_norm_addHaar volume (fun t : ℝ => (Set.Iio R).indicator (fun u => u ^ s) t)]
  -- Evaluate the resulting radial integral.
  have hinner : ∫ y in Set.Ioi (0 : ℝ),
        y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) - 1)
          • (Set.Iio R).indicator (fun u => u ^ s) y
      = R ^ (s + (d : ℝ)) / (s + (d : ℝ)) := by
    rw [finrank_euclideanSpace_fin]
    rw [show (fun y : ℝ => y ^ (d - 1) • (Set.Iio R).indicator (fun u => u ^ s) y)
          = (Set.Iio R).indicator (fun y : ℝ => y ^ (d - 1) * y ^ s) from by
      funext y
      by_cases hy : y ∈ Set.Iio R
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, smul_eq_mul]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, smul_zero]]
    rw [setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]
    rw [setIntegral_congr_fun measurableSet_Ioo
        (g := fun y : ℝ => y ^ (((d - 1 : ℕ) : ℝ) + s)) (fun y hy => ?_)]
    · rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hR.le,
        integral_rpow (Or.inl (by rw [Nat.cast_sub hd]; push_cast; linarith [hs]))]
      rw [show (((d - 1 : ℕ) : ℝ) + s) + 1 = s + (d : ℝ) from by
          rw [Nat.cast_sub hd]; push_cast; ring]
      rw [Real.zero_rpow (ne_of_gt (show (0 : ℝ) < s + (d : ℝ) by linarith [hs])), sub_zero]
    · obtain ⟨hy0, _⟩ := hy
      rw [← Real.rpow_natCast y (d - 1), ← Real.rpow_add hy0]
  rw [hinner, finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul]
  ring

/-- **Riesz-kernel `Lᵖ` bound.** For `p > d` there is a constant `Cdp` (depending only on
`d, p`) such that the `(d-1)`-Riesz potential of any `Lᵖ` function over a ball of radius
`R` centred at the base point is bounded by `Cdp · R^{1-d/p} · ‖g‖_{Lᵖ}`. The exponent
`1 - d/p` is precisely the Morrey Hölder exponent. -/
theorem exists_kernel_bound (hd : 0 < d) {p : ℝ} (hp : (d : ℝ) < p) :
    ∃ Cdp : ℝ≥0, ∀ (x : EuclideanSpace ℝ (Fin d)) {R : ℝ}, 0 < R →
      ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ),
        MemLp g (ENNReal.ofReal p) (volume.restrict (Metric.ball x R)) →
        ∫ y in Metric.ball x R, ‖g y‖ / dist x y ^ (d - 1)
          ≤ (Cdp : ℝ) * R ^ (1 - (d : ℝ) / p)
              * (eLpNorm g (ENNReal.ofReal p) (volume.restrict (Metric.ball x R))).toReal := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hd)
  have h1d : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hp1 : (1 : ℝ) < p := lt_of_le_of_lt h1d hp
  obtain ⟨q, hpq⟩ : ∃ q, p.HolderConjugate q := ⟨_, Real.HolderConjugate.conjExponent hp1⟩
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  have hqconj : q = p / (p - 1) := hpq.conjugate_eq
  have hpm1 : 0 < p - 1 := hpq.sub_one_pos
  have hp0' : p ≠ 0 := hp0.ne'
  have hpm1' : p - 1 ≠ 0 := hpm1.ne'
  have hq0' : q ≠ 0 := hq0.ne'
  set n : ℕ := d - 1 with hn_def
  have hn : ((n : ℝ)) = (d : ℝ) - 1 := by rw [hn_def, Nat.cast_sub hd, Nat.cast_one]
  set s : ℝ := (-(n : ℝ)) * q with hs_def
  set ω : ℝ := volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hω_def
  have hω_pos : 0 < ω := by
    rw [hω_def, measureReal_def, ENNReal.toReal_pos_iff]
    exact ⟨measure_ball_pos volume 0 one_pos, measure_ball_lt_top⟩
  have ha_eq : s + (d : ℝ) = (p - (d : ℝ)) / (p - 1) := by
    rw [hs_def, hn, hqconj]; field_simp; ring
  have ha_pos : 0 < s + (d : ℝ) := by
    rw [ha_eq]; exact div_pos (by linarith) hpm1
  have hs_lb : -(d : ℝ) < s := by linarith [ha_pos]
  have haq : (s + (d : ℝ)) / q = 1 - (d : ℝ) / p := by
    rw [ha_eq, hqconj]; field_simp
  have hp_ne0 : ENNReal.ofReal p ≠ 0 := by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hp0
  have hp_netop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hCnn : 0 ≤ ((d : ℝ) * ω / (s + (d : ℝ))) ^ (1 / q) :=
    Real.rpow_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg d) hω_pos.le) ha_pos.le) _
  refine ⟨⟨((d : ℝ) * ω / (s + (d : ℝ))) ^ (1 / q), hCnn⟩, ?_⟩
  intro x R hR g hmem
  -- Almost-everywhere the running point differs from the centre.
  have hxne : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), y ≠ x := by
    rw [ae_iff, show {y : EuclideanSpace ℝ (Fin d) | ¬ y ≠ x} = {x} from by ext z; simp]
    exact measure_singleton x
  -- Pointwise: the `q`-power of the kernel is a `dist`-power with exponent `s`.
  have hpt : ∀ y : EuclideanSpace ℝ (Fin d), y ≠ x →
      ((dist x y ^ n)⁻¹) ^ q = dist x y ^ s := by
    intro y hy
    have hD : 0 < dist x y := dist_pos.mpr (fun h => hy h.symm)
    rw [← Real.rpow_natCast (dist x y) n, ← Real.rpow_neg hD.le, ← Real.rpow_mul hD.le, hs_def]
  -- Integrability of the `dist`-power on the ball (Task 4b pattern).
  have hdist_int : IntegrableOn (fun y => dist x y ^ s) (ball x R) volume := by
    have hfrk : 1 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) := by
      rw [finrank_euclideanSpace_fin]; exact hd
    have hmp : MeasurePreserving (fun w : EuclideanSpace ℝ (Fin d) => x + w) volume volume :=
      measurePreserving_add_left volume x
    rw [← hmp.integrableOn_comp_preimage (measurableEmbedding_addLeft x)]
    rw [show (fun w : EuclideanSpace ℝ (Fin d) => x + w) ⁻¹' ball x R
        = ball (0 : EuclideanSpace ℝ (Fin d)) R from by
      ext w; simp only [Set.mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left,
        sub_zero]]
    rw [show (fun y => dist x y ^ s) ∘ (fun w : EuclideanSpace ℝ (Fin d) => x + w)
        = fun w => ‖w‖ ^ s from by
      funext w
      simp only [Function.comp_apply, dist_eq_norm, show x - (x + w) = -w from by abel, norm_neg]]
    apply MeasureTheory.integrableOn_ball_of_norm_le_rpow (C := 1) (α := -s) hfrk
    · rw [finrank_euclideanSpace_fin]; linarith [hs_lb]
    · filter_upwards with w
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), neg_neg, one_mul]
    · exact (measurable_norm.pow measurable_const).aestronglyMeasurable
  -- Transfer integrability to the kernel's `q`-power.
  have hae : (fun y => dist x y ^ s)
      =ᵐ[volume.restrict (ball x R)] (fun y => ((dist x y ^ n)⁻¹) ^ q) := by
    filter_upwards [ae_restrict_of_ae hxne] with y hy
    exact (hpt y hy).symm
  have hKint : IntegrableOn (fun y => ((dist x y ^ n)⁻¹) ^ q) (ball x R) volume :=
    hdist_int.congr hae
  -- Membership of the kernel in `L^q`.
  have hpe : ∀ y : EuclideanSpace ℝ (Fin d),
      ‖(dist x y ^ n)⁻¹‖ₑ ^ q = ‖((dist x y ^ n)⁻¹) ^ q‖ₑ := by
    intro y
    have ha : (0 : ℝ) ≤ (dist x y ^ n)⁻¹ := by positivity
    rw [← ofReal_norm ((dist x y ^ n)⁻¹ ^ q), ← ofReal_norm ((dist x y ^ n)⁻¹),
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
      abs_of_nonneg (Real.rpow_nonneg ha q), ENNReal.ofReal_rpow_of_nonneg ha hq0.le]
  have hKmem : MemLp (fun y => (dist x y ^ n)⁻¹) (ENNReal.ofReal q)
      (volume.restrict (ball x R)) := by
    refine ⟨(((continuous_const.dist continuous_id).pow n).measurable.inv).aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hq0) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq0.le, lintegral_congr hpe]
    exact hasFiniteIntegral_iff_enorm.mp hKint.2
  -- Hölder's inequality at the Bochner level.
  have hf_nn : 0 ≤ᵐ[volume.restrict (ball x R)] (fun y => ‖g y‖) :=
    ae_of_all _ (fun y => norm_nonneg _)
  have hK_nn : 0 ≤ᵐ[volume.restrict (ball x R)] (fun y => (dist x y ^ n)⁻¹) :=
    ae_of_all _ (fun y => by positivity)
  have holder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hf_nn hK_nn hmem.norm hKmem
  -- The `Lᵖ` factor equals the `toReal` of the `eLpNorm`.
  have hpint_nn : 0 ≤ ∫ y in ball x R, ‖g y‖ ^ p ∂volume :=
    integral_nonneg (fun y => Real.rpow_nonneg (norm_nonneg _) _)
  have heLp : (eLpNorm g (ENNReal.ofReal p) (volume.restrict (ball x R))).toReal
      = (∫ y in ball x R, ‖g y‖ ^ p ∂volume) ^ (1 / p) := by
    rw [hmem.eLpNorm_eq_integral_rpow_norm hp_ne0 hp_netop, ENNReal.toReal_ofReal hp0.le,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hpint_nn _), one_div]
  -- The kernel factor equals the constant times `R^{1-d/p}`.
  have hker_val : ∫ y in ball x R, ((dist x y ^ n)⁻¹) ^ q ∂volume
      = (d : ℝ) * ω * (R ^ (s + (d : ℝ)) / (s + (d : ℝ))) := by
    rw [setIntegral_congr_ae measurableSet_ball (g := fun y => dist x y ^ s)
        (by filter_upwards [hxne] with y hy; exact fun _ => hpt y hy),
      setIntegral_ball_dist_rpow hd x hR hs_lb, ← hω_def]
  have hKfac : (∫ y in ball x R, ((dist x y ^ n)⁻¹) ^ q ∂volume) ^ (1 / q)
      = ((d : ℝ) * ω / (s + (d : ℝ))) ^ (1 / q) * R ^ (1 - (d : ℝ) / p) := by
    rw [hker_val]
    rw [show (d : ℝ) * ω * (R ^ (s + (d : ℝ)) / (s + (d : ℝ)))
        = ((d : ℝ) * ω / (s + (d : ℝ))) * R ^ (s + (d : ℝ)) from by field_simp]
    rw [Real.mul_rpow (div_nonneg (mul_nonneg (Nat.cast_nonneg d) hω_pos.le) ha_pos.le)
        (Real.rpow_nonneg hR.le _), ← Real.rpow_mul hR.le, mul_one_div, haq]
  -- Assemble.
  calc ∫ y in ball x R, ‖g y‖ / dist x y ^ n ∂volume
      = ∫ y in ball x R, ‖g y‖ * (dist x y ^ n)⁻¹ ∂volume := by simp_rw [div_eq_mul_inv]
    _ ≤ (∫ y in ball x R, ‖g y‖ ^ p ∂volume) ^ (1 / p)
          * (∫ y in ball x R, ((dist x y ^ n)⁻¹) ^ q ∂volume) ^ (1 / q) := holder
    _ = (eLpNorm g (ENNReal.ofReal p) (volume.restrict (ball x R))).toReal
          * (((d : ℝ) * ω / (s + (d : ℝ))) ^ (1 / q) * R ^ (1 - (d : ℝ) / p)) := by
        rw [← heLp, hKfac]
    _ = ((d : ℝ) * ω / (s + (d : ℝ))) ^ (1 / q) * R ^ (1 - (d : ℝ) / p)
          * (eLpNorm g (ENNReal.ofReal p) (volume.restrict (ball x R))).toReal := by ring

/-- **Gradient norm is `Lᵖ` on a ball.** For a smooth `φ` the map `y ↦ ‖fderiv ℝ φ y‖` is
continuous, hence bounded on the compact closed ball, hence `Lᵖ` on the finite-measure
restricted ball. This is the `MemLp` witness fed to `exists_kernel_bound`. -/
private theorem memLp_norm_fderiv {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {p : ℝ} (z : EuclideanSpace ℝ (Fin d)) {r : ℝ} (_hr : 0 < r) :
    MemLp (fun y => ‖fderiv ℝ φ y‖) (ENNReal.ofReal p) (volume.restrict (Metric.ball z r)) := by
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball z r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin d) => ‖fderiv ℝ φ y‖) :=
    (hφ.continuous_fderiv (by simp)).norm
  obtain ⟨C, hC⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn hcont.continuousOn
  refine MemLp.of_bound hcont.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
  exact hC y (ball_subset_closedBall hy)

/-- **Centred oscillation bound (Task 4 ∘ Task 5).** For `p > d` there is a
dimensional/exponent constant `C` such that for every smooth `φ`, at the centre of any ball
the oscillation of `φ` about its ball average is controlled by `C · R^{1-d/p} · ‖∇φ‖_{Lᵖ}`.
This fuses the potential estimate with the Riesz-kernel bound; it is the mechanical core of
the Morrey Hölder estimate. -/
private theorem exists_oscillation_bound (hd : 0 < d) {p : ℝ} (hp : (d : ℝ) < p) :
    ∃ C : ℝ≥0, ∀ (φ : EuclideanSpace ℝ (Fin d) → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      ∀ (z : EuclideanSpace ℝ (Fin d)) {r : ℝ}, 0 < r →
        |φ z - ⨍ y in Metric.ball z r, φ y|
          ≤ (C : ℝ) * r ^ (1 - (d : ℝ) / p)
              * (eLpNorm (fun y => ‖fderiv ℝ φ y‖) (ENNReal.ofReal p)
                  (volume.restrict (Metric.ball z r))).toReal := by
  obtain ⟨Cd, hCd⟩ := exists_potential_bound hd
  obtain ⟨Cdp, hCdp⟩ := exists_kernel_bound hd hp
  refine ⟨Cd * Cdp, ?_⟩
  intro φ hφ z r hr
  have hpot := hCd φ hφ z hr z (mem_ball_self hr)
  have hmem := memLp_norm_fderiv (p := p) hφ z hr
  have hker := hCdp z hr (fun y => ‖fderiv ℝ φ y‖) hmem
  simp only [norm_norm] at hker
  have hCd0 : (0 : ℝ) ≤ (Cd : ℝ) := Cd.coe_nonneg
  calc |φ z - ⨍ y in Metric.ball z r, φ y|
      ≤ (Cd : ℝ) * ∫ y in Metric.ball z r, ‖fderiv ℝ φ y‖ / dist z y ^ (d - 1) := hpot
    _ ≤ (Cd : ℝ) * ((Cdp : ℝ) * r ^ (1 - (d : ℝ) / p)
          * (eLpNorm (fun y => ‖fderiv ℝ φ y‖) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball z r))).toReal) :=
        mul_le_mul_of_nonneg_left hker hCd0
    _ = ((Cd * Cdp : ℝ≥0) : ℝ) * r ^ (1 - (d : ℝ) / p)
          * (eLpNorm (fun y => ‖fderiv ℝ φ y‖) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball z r))).toReal := by push_cast; ring

/-- **Subset Riesz-kernel bound.** The indicator corollary of `exists_kernel_bound`: for a
measurable subset `S` of the ball `ball x R` (singularity at the centre `x`), the `(d-1)`-Riesz
potential of an `Lᵖ` function `g` over `S` is bounded by `Cdp · R^{1-d/p} · ‖g‖_{Lᵖ(S)}`, the
`Lᵖ` norm being taken over `S`. This lets the averaging domain of the Morrey estimate shrink to a
convex lens while retaining the correct radial scaling. -/
private theorem exists_kernel_bound_subset (hd : 0 < d) {p : ℝ} (hp : (d : ℝ) < p) :
    ∃ Cdp : ℝ≥0, ∀ (x : EuclideanSpace ℝ (Fin d)) {R : ℝ}, 0 < R →
      ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ),
        MemLp g (ENNReal.ofReal p) (volume.restrict (Metric.ball x R)) →
        ∀ {S : Set (EuclideanSpace ℝ (Fin d))}, MeasurableSet S → S ⊆ Metric.ball x R →
          ∫ y in S, ‖g y‖ / dist x y ^ (d - 1)
            ≤ (Cdp : ℝ) * R ^ (1 - (d : ℝ) / p)
                * (eLpNorm g (ENNReal.ofReal p) (volume.restrict S)).toReal := by
  obtain ⟨Cdp, hCdp⟩ := exists_kernel_bound hd hp
  refine ⟨Cdp, ?_⟩
  intro x R hR g hg S hSmeas hSsub
  have key := hCdp x hR (S.indicator g) (hg.indicator hSmeas)
  have hfun : (fun y => ‖(S.indicator g) y‖ / dist x y ^ (d - 1))
      = S.indicator (fun y => ‖g y‖ / dist x y ^ (d - 1)) := by
    funext y
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, norm_zero, zero_div]
  rw [hfun, setIntegral_indicator hSmeas, Set.inter_eq_right.mpr hSsub,
    eLpNorm_indicator_eq_eLpNorm_restrict hSmeas,
    Measure.restrict_restrict_of_subset hSsub] at key
  exact key

/-- **Lens measure lower bound.** For `x, x'` in `ball c r` with `ρ = dist x x' > 0`, the convex
lens `ball x (2ρ) ∩ ball x' (2ρ) ∩ ball c r` — which contains both points and lies inside the
domain — has volume at least `(ρ/4)^d · ω_d`, where `ω_d` is the unit-ball volume. Proof: exhibit
an inscribed ball `ball q (ρ/4)`, with `q` the midpoint pushed towards the centre `c` when the
midpoint sits near the boundary, contained in all three balls, and compare volumes. -/
private theorem lens_volume_lower_bound (_hd : 0 < d) (c x x' : EuclideanSpace ℝ (Fin d))
    {r : ℝ} (_hr : 0 < r) (hx : x ∈ ball c r) (hx' : x' ∈ ball c r) (hne : x ≠ x') :
    (dist x x' / 4) ^ d * volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
      ≤ volume.real (ball x (2 * dist x x') ∩ ball x' (2 * dist x x') ∩ ball c r) := by
  set ρ := dist x x' with hρ_def
  have hρ_pos : 0 < ρ := dist_pos.mpr hne
  have hρ4 : (0 : ℝ) < ρ / 4 := by linarith
  set m := midpoint ℝ x x' with hm_def
  have hmc : dist m c < r := by
    have hmem : m ∈ ball c r := (convex_ball c r).midpoint_mem hx hx'
    rwa [mem_ball] at hmem
  have hdmx : dist m x = ρ / 2 := by
    rw [hm_def, dist_midpoint_left, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      ← hρ_def]
    ring
  have hdmx' : dist m x' = ρ / 2 := by
    rw [hm_def, dist_midpoint_right, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      ← hρ_def]
    ring
  have hρ_lt : ρ < 2 * r := by
    have h1 : dist x c < r := by rwa [mem_ball] at hx
    have h2 : dist x' c < r := by rwa [mem_ball] at hx'
    calc ρ = dist x x' := hρ_def
      _ ≤ dist x c + dist c x' := dist_triangle x c x'
      _ = dist x c + dist x' c := by rw [dist_comm c x']
      _ < 2 * r := by linarith
  have hr2 : (0 : ℝ) < r - ρ / 2 := by linarith
  -- Choose an inscribed centre `q` with `dist q c ≤ r - ρ/2` and `dist q m ≤ ρ/2`.
  obtain ⟨q, hqc, hqm⟩ : ∃ q : EuclideanSpace ℝ (Fin d),
      dist q c ≤ r - ρ / 2 ∧ dist q m ≤ ρ / 2 := by
    by_cases hcase : dist m c ≤ r - ρ / 2
    · exact ⟨m, hcase, by rw [dist_self]; linarith⟩
    · replace hcase : r - ρ / 2 < dist m c := not_le.mp hcase
      have hDpos : 0 < dist m c := lt_trans hr2 hcase
      set lam := (r - ρ / 2) / dist m c with hlam
      have hlam_nn : 0 ≤ lam := by rw [hlam]; exact div_nonneg hr2.le hDpos.le
      have hlam_lt : lam < 1 := by rw [hlam, div_lt_one hDpos]; exact hcase
      refine ⟨c + lam • (m - c), le_of_eq ?_, ?_⟩
      · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hlam_nn, ← dist_eq_norm, hlam, div_eq_mul_inv, mul_assoc,
          inv_mul_cancel₀ (ne_of_gt hDpos), mul_one]
      · have heq : (c + lam • (m - c)) - m = (1 - lam) • (c - m) := by module
        have hval : dist (c + lam • (m - c)) m = dist m c - (r - ρ / 2) := by
          rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - lam), ← dist_eq_norm, dist_comm c m,
            sub_mul, one_mul, hlam, div_eq_mul_inv, mul_assoc,
            inv_mul_cancel₀ (ne_of_gt hDpos), mul_one]
        rw [hval]; linarith
  -- The inscribed ball lies inside all three balls.
  have hsub : ball q (ρ / 4) ⊆ ball x (2 * ρ) ∩ ball x' (2 * ρ) ∩ ball c r := by
    refine subset_inter (subset_inter ?_ ?_) ?_
    · refine ball_subset_ball' ?_
      have hqx : dist q x ≤ ρ := by
        calc dist q x ≤ dist q m + dist m x := dist_triangle q m x
          _ ≤ ρ / 2 + ρ / 2 := by rw [hdmx]; linarith
          _ = ρ := by ring
      linarith
    · refine ball_subset_ball' ?_
      have hqx' : dist q x' ≤ ρ := by
        calc dist q x' ≤ dist q m + dist m x' := dist_triangle q m x'
          _ ≤ ρ / 2 + ρ / 2 := by rw [hdmx']; linarith
          _ = ρ := by ring
      linarith
    · refine ball_subset_ball' ?_
      linarith
  -- Compare volumes.
  have hWtop : volume (ball x (2 * ρ) ∩ ball x' (2 * ρ) ∩ ball c r) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (fun z hz => hz.2))
  have hvolq : volume.real (ball q (ρ / 4))
      = (ρ / 4) ^ d * volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
    rw [measureReal_def, Measure.addHaar_ball_of_pos volume q hρ4, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hρ4.le _), finrank_euclideanSpace_fin, measureReal_def]
  calc (ρ / 4) ^ d * volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
      = volume.real (ball q (ρ / 4)) := hvolq.symm
    _ ≤ volume.real (ball x (2 * ρ) ∩ ball x' (2 * ρ) ∩ ball c r) :=
        ENNReal.toReal_mono hWtop (measure_mono hsub)

end EllipticDirichlet.Embedding
