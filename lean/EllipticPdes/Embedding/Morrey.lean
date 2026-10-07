/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.RayIntegral
public import EllipticPdes.Embedding.Convolution
public import EllipticPdes.Sobolev.WeakDerivClassical
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.Topology.MetricSpace.HolderNorm
public import Mathlib.Tactic.Module
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique

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

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal Convolution Topology

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The restriction of a measure that is finite on compact sets to a ball is a finite
measure. -/
instance {X : Type*} [PseudoMetricSpace X] [ProperSpace X] {m : MeasurableSpace X}
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (c : X) (r : ℝ) :
    IsFiniteMeasure (μ.restrict (Metric.ball c r)) :=
  isFiniteMeasure_restrict.2 measure_ball_lt_top.ne

/-- **Radial power integral over a ball centred at the singularity.** For `s > -d`, the integral
of `dist x ·^s` over the ball `B(x, R)` has the closed form `d · ω_d · R^{s+d}/(s+d)`, where
`ω_d` is the μ of the unit ball. Proof: translate to the origin, then apply the polar
change of variables `integral_fun_norm_addHaar` and evaluate the resulting `1`-D radial integral
with `integral_rpow`. This is the isolated kernel-norm computation feeding the Hölder step. -/
private theorem setIntegral_ball_dist_rpow (hE : Module.finrank ℝ E = d) (hd : 0 < d) (x : E)
    {R : ℝ} (hR : 0 < R) {s : ℝ} (hs : -(d : ℝ) < s) :
    ∫ y in ball x R, dist x y ^ s ∂μ
      = (d : ℝ) * μ.real (ball (0 : E) 1)
          * (R ^ (s + (d : ℝ)) / (s + (d : ℝ))) := by
  have : Nontrivial (E) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (hE ▸ hd)
  -- Translate the integral to the origin.
  have hmp : MeasurePreserving (fun w : E => x + w) μ μ :=
    measurePreserving_add_left μ x
  have hpre : (fun w : E => x + w) ⁻¹' ball x R
      = ball (0 : E) R := by
    ext w
    simp only [Set.mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
  rw [show (∫ y in ball x R, dist x y ^ s ∂μ)
        = ∫ w in ball (0 : E) R, ‖w‖ ^ s ∂μ from by
    rw [← hmp.setIntegral_preimage_emb (measurableEmbedding_addLeft x)
          (fun y => dist x y ^ s) (ball x R), hpre]
    refine setIntegral_congr_fun measurableSet_ball (fun w _ => ?_)
    rw [dist_eq_norm, show x - (x + w) = -w from by abel, norm_neg]]
  -- Rewrite as an integral over the whole space of a radial function.
  rw [← integral_indicator
      (measurableSet_ball : MeasurableSet (ball (0 : E) R))]
  rw [show (fun w : E => (ball (0 : E) R).indicator
        (fun w => ‖w‖ ^ s) w) = (fun w => (Set.Iio R).indicator (fun t : ℝ => t ^ s) ‖w‖) from by
    funext w
    by_cases hw : ‖w‖ < R
    · rw [Set.indicator_of_mem (by rw [mem_ball, dist_zero_right]; exact hw),
        Set.indicator_of_mem (show ‖w‖ ∈ Set.Iio R from hw)]
    · rw [Set.indicator_of_notMem (by rw [mem_ball, dist_zero_right]; exact hw),
        Set.indicator_of_notMem (show ‖w‖ ∉ Set.Iio R from hw)]]
  rw [integral_fun_norm_addHaar μ (fun t : ℝ => (Set.Iio R).indicator (fun u => u ^ s) t)]
  -- Evaluate the resulting radial integral.
  have hinner : ∫ y in Set.Ioi (0 : ℝ),
        y ^ (Module.finrank ℝ (E) - 1)
          • (Set.Iio R).indicator (fun u => u ^ s) y
      = R ^ (s + (d : ℝ)) / (s + (d : ℝ)) := by
    rw [hE]
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
  rw [hinner, hE, nsmul_eq_mul, smul_eq_mul]
  ring

/-- Almost every point of Euclidean space differs from a given point. -/
private theorem ae_ne_point [Nontrivial (E)]
    (x : E) :
    ∀ᵐ y ∂μ, y ≠ x := by
  filter_upwards [(Set.countable_singleton x).ae_notMem μ] with y hy h
  exact hy (by simp [h])

/-- **The Riesz kernel is in `Lq` of a ball about its singularity.** The kernel
`y ↦ dist x y ^ (-(d-1))` lies in `Lq(ball x R)` as soon as `(d - 1) q < d`, and the `q`-th power
of the kernel is a power of the distance. -/
theorem memLp_inv_dist_pow_ball (hE : Module.finrank ℝ E = d) (hd : 0 < d) (x : E) {R q : ℝ}
    (hq0 : 0 < q) (hs : -(d : ℝ) < -((d - 1 : ℕ) : ℝ) * q) :
    MemLp (fun y => (dist x y ^ (d - 1))⁻¹) (ENNReal.ofReal q) (μ.restrict (ball x R)) := by
  have : Nontrivial (E) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (hE ▸ hd)
  set n : ℕ := d - 1 with hn_def
  set s : ℝ := -(n : ℝ) * q with hs_def
  have hxne := ae_ne_point (μ := μ) x
  -- The `q`-power of the kernel is a `dist`-power with exponent `s`.
  have hpt : ∀ y : E, y ≠ x → ((dist x y ^ n)⁻¹) ^ q = dist x y ^ s := by
    intro y hy
    have hD : 0 < dist x y := dist_pos.mpr (fun h => hy h.symm)
    rw [← Real.rpow_natCast (dist x y) n, ← Real.rpow_neg hD.le, ← Real.rpow_mul hD.le, hs_def,
      neg_mul]
  -- Integrability of the `dist`-power on the ball.
  have hdist_int : IntegrableOn (fun y => dist x y ^ s) (ball x R) μ := by
    have hmp : MeasurePreserving (fun w : E => x + w) μ μ :=
      measurePreserving_add_left μ x
    rw [← hmp.integrableOn_comp_preimage (measurableEmbedding_addLeft x)]
    rw [show (fun w : E => x + w) ⁻¹' ball x R
        = ball (0 : E) R from by
      ext w; simp only [Set.mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left,
        sub_zero]]
    rw [show (fun y => dist x y ^ s) ∘ (fun w : E => x + w)
        = fun w => ‖w‖ ^ s from by
      funext w
      simp only [Function.comp_apply, dist_eq_norm, show x - (x + w) = -w from by abel, norm_neg]]
    apply MeasureTheory.integrableOn_ball_of_norm_le_rpow (C := 1) (α := -s)
      (hE ▸ hd)
    · rw [hE]; linarith [hs]
    · filter_upwards with w
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), neg_neg, one_mul]
    · exact (measurable_norm.pow measurable_const).aestronglyMeasurable
  have hKint : IntegrableOn (fun y => ((dist x y ^ n)⁻¹) ^ q) (ball x R) μ :=
    hdist_int.congr (by filter_upwards [ae_restrict_of_ae hxne] with y hy using (hpt y hy).symm)
  have hpe : ∀ y : E,
      ‖(dist x y ^ n)⁻¹‖ₑ ^ q = ‖((dist x y ^ n)⁻¹) ^ q‖ₑ := fun y => by
    have ha : (0 : ℝ) ≤ (dist x y ^ n)⁻¹ := by positivity
    rw [← ofReal_norm ((dist x y ^ n)⁻¹ ^ q), ← ofReal_norm ((dist x y ^ n)⁻¹),
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
      abs_of_nonneg (Real.rpow_nonneg ha q), ENNReal.ofReal_rpow_of_nonneg ha hq0.le]
  have hKm : AEStronglyMeasurable (fun y => (dist x y ^ n)⁻¹) (μ.restrict (ball x R)) :=
    (((continuous_const.dist continuous_id).pow n).measurable.inv).aestronglyMeasurable
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hq0) ENNReal.ofReal_ne_top hKm,
    ENNReal.toReal_ofReal hq0.le, lintegral_congr hpe]
  exact hasFiniteIntegral_iff_enorm.mp hKint.2

/-- **Riesz-kernel `Lᵖ` bound.** For `p > d` there is a constant `Cdp` (depending only on
`d, p`) such that the `(d-1)`-Riesz potential of any `Lᵖ` function over a ball of radius
`R` centred at the base point is bounded by `Cdp · R^{1-d/p} · ‖g‖_{Lᵖ}`. The exponent
`1 - d/p` is precisely the Morrey Hölder exponent. -/
theorem exists_kernel_bound (hE : Module.finrank ℝ E = d) (hd : 0 < d) {p : ℝ} (hp : (d : ℝ) < p) :
    ∃ Cdp : ℝ≥0, ∀ (x : E) {R : ℝ}, 0 < R →
      ∀ (g : E → ℝ),
        MemLp g (ENNReal.ofReal p) (μ.restrict (Metric.ball x R)) →
        ∫ y in Metric.ball x R, ‖g y‖ / dist x y ^ (d - 1) ∂μ
          ≤ (Cdp : ℝ) * R ^ (1 - (d : ℝ) / p)
              * (eLpNorm g (ENNReal.ofReal p) (μ.restrict (Metric.ball x R))).toReal := by
  have : Nontrivial (E) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (hE ▸ hd)
  have hp1 : (1 : ℝ) < p := lt_of_le_of_lt (by exact_mod_cast hd) hp
  obtain ⟨q, hpq⟩ : ∃ q, p.HolderConjugate q := ⟨_, Real.HolderConjugate.conjExponent hp1⟩
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  have hpm1 : 0 < p - 1 := hpq.sub_one_pos
  set n : ℕ := d - 1 with hn_def
  have hn : ((n : ℝ)) = (d : ℝ) - 1 := by rw [hn_def, Nat.cast_sub hd, Nat.cast_one]
  set s : ℝ := (-(n : ℝ)) * q with hs_def
  set ω : ℝ := μ.real (ball (0 : E) 1) with hω_def
  have hω_pos : 0 < ω := by
    rw [hω_def, measureReal_def, ENNReal.toReal_pos_iff]
    exact ⟨measure_ball_pos μ 0 one_pos, measure_ball_lt_top⟩
  have ha_eq : s + (d : ℝ) = (p - (d : ℝ)) / (p - 1) := by
    rw [hs_def, hn, hpq.conjugate_eq]; field_simp; ring
  have ha_pos : 0 < s + (d : ℝ) := by rw [ha_eq]; exact div_pos (by linarith) hpm1
  have haq : (s + (d : ℝ)) / q = 1 - (d : ℝ) / p := by
    rw [ha_eq, hpq.conjugate_eq]; field_simp
  have hCnn : 0 ≤ ((d : ℝ) * ω / (s + (d : ℝ))) ^ (1 / q) :=
    Real.rpow_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg d) hω_pos.le) ha_pos.le) _
  refine ⟨⟨((d : ℝ) * ω / (s + (d : ℝ))) ^ (1 / q), hCnn⟩, fun x R hR g hmem => ?_⟩
  have hKmem := memLp_inv_dist_pow_ball (μ := μ) hE hd x (R := R) hq0 (by linarith [ha_pos])
  -- Hölder's inequality at the Bochner level.
  have holder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (ae_of_all _ (fun y => norm_nonneg (g y)) : 0 ≤ᵐ[μ.restrict (ball x R)] fun y => ‖g y‖)
    (ae_of_all _ (fun y => by positivity) : 0 ≤ᵐ[μ.restrict (ball x R)]
      fun y => (dist x y ^ n)⁻¹) hmem.norm hKmem
  -- The `Lᵖ` factor equals the `toReal` of the `eLpNorm`.
  have heLp : (eLpNorm g (ENNReal.ofReal p) (μ.restrict (ball x R))).toReal
      = (∫ y in ball x R, ‖g y‖ ^ p ∂μ) ^ (1 / p) := by
    rw [hmem.eLpNorm_eq_integral_rpow_norm (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hp0)
        ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun y =>
        Real.rpow_nonneg (norm_nonneg _) _) _), one_div]
  -- The kernel factor equals the constant times `R^{1-d/p}`.
  have hker_val : ∫ y in ball x R, ((dist x y ^ n)⁻¹) ^ q ∂μ
      = (d : ℝ) * ω * (R ^ (s + (d : ℝ)) / (s + (d : ℝ))) := by
    rw [setIntegral_congr_ae measurableSet_ball (g := fun y => dist x y ^ s)
        (by
          filter_upwards [ae_ne_point x] with y hy _
          rw [← Real.rpow_natCast (dist x y) n, ← Real.rpow_neg dist_nonneg,
            ← Real.rpow_mul dist_nonneg, hs_def, neg_mul]),
      setIntegral_ball_dist_rpow hE hd x hR (by linarith [ha_pos]), ← hω_def]
  have hKfac : (∫ y in ball x R, ((dist x y ^ n)⁻¹) ^ q ∂μ) ^ (1 / q)
      = ((d : ℝ) * ω / (s + (d : ℝ))) ^ (1 / q) * R ^ (1 - (d : ℝ) / p) := by
    rw [hker_val, show (d : ℝ) * ω * (R ^ (s + (d : ℝ)) / (s + (d : ℝ)))
        = ((d : ℝ) * ω / (s + (d : ℝ))) * R ^ (s + (d : ℝ)) from by field_simp,
      Real.mul_rpow (div_nonneg (mul_nonneg (Nat.cast_nonneg d) hω_pos.le) ha_pos.le)
        (Real.rpow_nonneg hR.le _), ← Real.rpow_mul hR.le, mul_one_div, haq]
  calc ∫ y in ball x R, ‖g y‖ / dist x y ^ n ∂μ
      = ∫ y in ball x R, ‖g y‖ * (dist x y ^ n)⁻¹ ∂μ := by simp_rw [div_eq_mul_inv]
    _ ≤ (∫ y in ball x R, ‖g y‖ ^ p ∂μ) ^ (1 / p)
          * (∫ y in ball x R, ((dist x y ^ n)⁻¹) ^ q ∂μ) ^ (1 / q) := holder
    _ = ((d : ℝ) * ω / (s + (d : ℝ))) ^ (1 / q) * R ^ (1 - (d : ℝ) / p)
          * (eLpNorm g (ENNReal.ofReal p) (μ.restrict (ball x R))).toReal := by
        rw [← heLp, hKfac]; ring

/-- **Gradient norm is `Lᵖ` on a ball.** For a smooth `φ` the map `y ↦ ‖fderiv ℝ φ y‖` is
continuous, hence bounded on the compact closed ball, hence `Lᵖ` on the finite-measure
restricted ball. This is the `MemLp` witness fed to `exists_kernel_bound`. -/
private theorem memLp_norm_fderiv {φ : E → F}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {p : ℝ} (z : E) {r : ℝ} (_hr : 0 < r) :
    MemLp (fun y => ‖fderiv ℝ φ y‖) (ENNReal.ofReal p) (μ.restrict (Metric.ball z r)) := by
  have hcont : Continuous (fun y : E => ‖fderiv ℝ φ y‖) :=
    (hφ.continuous_fderiv (by simp)).norm
  obtain ⟨C, hC⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn hcont.continuousOn
  refine MemLp.of_bound hcont.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
  exact hC y (ball_subset_closedBall hy)

/-- **Subset Riesz-kernel bound.** The indicator corollary of `exists_kernel_bound`: for a
measurable subset `S` of the ball `ball x R` (singularity at the centre `x`), the `(d-1)`-Riesz
potential of an `Lᵖ` function `g` over `S` is bounded by `Cdp · R^{1-d/p} · ‖g‖_{Lᵖ(S)}`, the
`Lᵖ` norm being taken over `S`. This lets the averaging domain of the Morrey estimate shrink to a
convex lens while retaining the correct radial scaling. -/
private theorem exists_kernel_bound_subset (hE : Module.finrank ℝ E = d) (hd : 0 < d) {p : ℝ}
    (hp : (d : ℝ) < p) :
    ∃ Cdp : ℝ≥0, ∀ (x : E) {R : ℝ}, 0 < R →
      ∀ (g : E → ℝ),
        MemLp g (ENNReal.ofReal p) (μ.restrict (Metric.ball x R)) →
        ∀ {S : Set (E)}, MeasurableSet S → S ⊆ Metric.ball x R →
          ∫ y in S, ‖g y‖ / dist x y ^ (d - 1) ∂μ
            ≤ (Cdp : ℝ) * R ^ (1 - (d : ℝ) / p)
                * (eLpNorm g (ENNReal.ofReal p) (μ.restrict S)).toReal := by
  obtain ⟨Cdp, hCdp⟩ := exists_kernel_bound (μ := μ) hE hd hp
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
lens `ball x (2ρ) ∩ ball x' (2ρ) ∩ ball c r`, which contains both points and lies inside the
domain, has μ at least `(ρ/4)^d · ω_d`, where `ω_d` is the unit-ball μ. Proof: exhibit
an inscribed ball `ball q (ρ/4)`, with `q` the midpoint pushed towards the centre `c` when the
midpoint sits near the boundary, contained in all three balls, and compare volumes. -/
private theorem lens_volume_lower_bound (hE : Module.finrank ℝ E = d) (c x x' : E)
    {r : ℝ} (_hr : 0 < r) (hx : x ∈ ball c r) (hx' : x' ∈ ball c r) (hne : x ≠ x') :
    (dist x x' / 4) ^ d * μ.real (ball (0 : E) 1)
      ≤ μ.real (ball x (2 * dist x x') ∩ ball x' (2 * dist x x') ∩ ball c r) := by
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
  obtain ⟨q, hqc, hqm⟩ : ∃ q : E,
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
  have hWtop : μ (ball x (2 * ρ) ∩ ball x' (2 * ρ) ∩ ball c r) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (fun z hz => hz.2))
  have hvolq : μ.real (ball q (ρ / 4))
      = (ρ / 4) ^ d * μ.real (ball (0 : E) 1) := by
    rw [measureReal_def, Measure.addHaar_ball_of_pos μ q hρ4, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hρ4.le _), hE, measureReal_def]
  calc (ρ / 4) ^ d * μ.real (ball (0 : E) 1)
      = μ.real (ball q (ρ / 4)) := hvolq.symm
    _ ≤ μ.real (ball x (2 * ρ) ∩ ball x' (2 * ρ) ∩ ball c r) :=
        ENNReal.toReal_mono hWtop (measure_mono hsub)

/-- **Hölder continuity from a pointwise bound.** A function whose increments are bounded by
`C · dist x y ^ γ` on `s` is Hölder-`γ` on `s` with constant `C`. -/
theorem holderOnWith_of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {s : Set X} {C γ : ℝ≥0}
    (h : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ C * dist x y ^ (γ : ℝ)) : HolderOnWith C γ f s := by
  intro x hx y hy
  rw [edist_dist, edist_dist, ← ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg γ.coe_nonneg, ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (h x hx y hy)

/-- **Oscillation of a smooth function over a convex set.** For `p > d` there is a constant `K`
such that, for a smooth `φ`, a convex measurable `W ⊆ ball c r` of μ at least
`(ρ/4)^d ω_d`, and a point `a ∈ W` with `W ⊆ ball a (2ρ)`, the oscillation of `φ` at `a` about
its `W`-average is at most `K ρ^{1-d/p} ‖∇φ‖_{Lᵖ(ball c r)}`. The averaging identity bounds it by
the Riesz potential of the gradient over `W`, which the subset kernel bound estimates. -/
theorem exists_norm_sub_average_le [CompleteSpace F] (hE : Module.finrank ℝ E = d) (hd : 0 < d)
    {p : ℝ} (hp : (d : ℝ) < p) :
    ∃ K : ℝ≥0, ∀ (φ : E → F), ContDiff ℝ (⊤ : ℕ∞) φ →
      ∀ (c : E) {r : ℝ}, 0 < r → ∀ {ρ : ℝ}, 0 < ρ →
      ∀ {W : Set (E)}, MeasurableSet W → Convex ℝ W → W ⊆ ball c r →
      (ρ / 4) ^ d * μ.real (ball (0 : E) 1) ≤ μ.real W →
      ∀ a ∈ W, W ⊆ ball a (2 * ρ) →
        ‖φ a - ⨍ y in W, φ y ∂μ‖ ≤ K * ρ ^ (1 - (d : ℝ) / p)
          * (eLpNorm (fun y => ‖fderiv ℝ φ y‖) (ENNReal.ofReal p)
              (μ.restrict (ball c r))).toReal := by
  have : Nontrivial (E) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (hE ▸ hd)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set ω : ℝ := μ.real (ball (0 : E) 1) with hω_def
  have hω_pos : 0 < ω := by
    rw [hω_def, measureReal_def, ENNReal.toReal_pos_iff]
    exact ⟨measure_ball_pos μ 0 one_pos, measure_ball_lt_top⟩
  obtain ⟨Cdp, hCdp⟩ := exists_kernel_bound_subset (μ := μ) hE hd hp
  set K : ℝ := 8 ^ d / ((d : ℝ) * ω) * (Cdp : ℝ) * (2 : ℝ) ^ (1 - (d : ℝ) / p) with hK_def
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K.toNNReal, fun φ hφ c r hr ρ hρ W hWmeas hWconv hWc hBlb a haW hWsub => ?_⟩
  set N := eLpNorm (fun y => ‖fderiv ℝ φ y‖) (ENNReal.ofReal p) (μ.restrict (ball c r))
    with hN_def
  have hN_ne_top : N ≠ ⊤ := (memLp_norm_fderiv (p := p) hφ c hr).eLpNorm_lt_top.ne
  have h2ρ : (0 : ℝ) < 2 * ρ := by positivity
  have hWposR : 0 < μ.real W :=
    lt_of_lt_of_le (mul_pos (pow_pos (by positivity) d) hω_pos) hBlb
  obtain ⟨hWpos, hWtop⟩ := ENNReal.toReal_pos_iff.mp (measureReal_def (μ := μ) W ▸ hWposR)
  have hEW_le_N :
      (eLpNorm (fun y => ‖fderiv ℝ φ y‖) (ENNReal.ofReal p) (μ.restrict W)).toReal
        ≤ N.toReal :=
    ENNReal.toReal_mono hN_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono hWc le_rfl))
  have hosc := oscillation_le_potential_convex hE hφ hd a hWmeas hWconv haW hWpos.ne' hWtop.ne h2ρ
    hWsub ((riesz_potential_integrableOn hE hφ hd c a hr (hWc haW)).mono_set hWc)
  have hker_a := hCdp a h2ρ (fun y => ‖fderiv ℝ φ y‖) (memLp_norm_fderiv (p := p) hφ a h2ρ)
    hWmeas hWsub
  simp only [norm_norm] at hker_a
  have hP_bound : (∫ z in W, ‖fderiv ℝ φ z‖ / dist a z ^ (d - 1) ∂μ)
      ≤ (Cdp : ℝ) * (2 * ρ) ^ (1 - (d : ℝ) / p) * N.toReal :=
    hker_a.trans (mul_le_mul_of_nonneg_left hEW_le_N (by positivity))
  have hA_bound : (2 * ρ) ^ d / ((d : ℝ) * μ.real W) ≤ 8 ^ d / ((d : ℝ) * ω) := by
    rw [div_le_div_iff₀ (mul_pos hdR hWposR) (mul_pos hdR hω_pos)]
    calc (2 * ρ) ^ d * ((d : ℝ) * ω) = 8 ^ d * (d : ℝ) * ((ρ / 4) ^ d * ω) := by
          rw [show (2 * ρ) ^ d = 8 ^ d * (ρ / 4) ^ d by rw [← mul_pow]; congr 1; ring]; ring
      _ ≤ 8 ^ d * (d : ℝ) * μ.real W := mul_le_mul_of_nonneg_left hBlb (by positivity)
      _ = 8 ^ d * ((d : ℝ) * μ.real W) := by ring
  calc ‖φ a - ⨍ y in W, φ y ∂μ‖
      ≤ (2 * ρ) ^ d / ((d : ℝ) * μ.real W)
          * ∫ z in W, ‖fderiv ℝ φ z‖ / dist a z ^ (d - 1) ∂μ := hosc
    _ ≤ 8 ^ d / ((d : ℝ) * ω) * ((Cdp : ℝ) * (2 * ρ) ^ (1 - (d : ℝ) / p) * N.toReal) :=
        mul_le_mul hA_bound hP_bound (integral_nonneg fun z => by positivity)
          (div_nonneg (by positivity) (mul_nonneg hdR.le hω_pos.le))
    _ = K.toNNReal * ρ ^ (1 - (d : ℝ) / p) * N.toReal := by
        rw [Real.coe_toNNReal _ hK0, Real.mul_rpow (by norm_num) hρ.le, hK_def]; ring

/-- **Smooth Morrey Hölder estimate on a ball.** For `p > d` there is a constant `C`,
depending only on `d` and `p`, such that every smooth `φ` is Hölder continuous on `ball c r`
with exponent `1 - d/p` and constant `C · ‖∇φ‖_{Lᵖ(ball c r)}`. This is Gilbarg–Trudinger
Theorem 7.19: the interior Hölder seminorm is controlled by the domain-restricted `Lᵖ` norm of
the gradient. The proof averages over the convex lens
`ball x (2ρ) ∩ ball x' (2ρ) ∩ ball c r`, which contains both points and stays inside the domain,
so the averaging never sees the gradient outside `ball c r`. -/
theorem exists_holder_smooth [CompleteSpace F] (hE : Module.finrank ℝ E = d) (hd : 0 < d)
    {p : ℝ} (hp : (d : ℝ) < p) :
    ∃ C : ℝ≥0, ∀ (φ : E → F), ContDiff ℝ (⊤ : ℕ∞) φ →
      ∀ (c : E) {r : ℝ}, 0 < r →
        HolderOnWith
          (C * (eLpNorm (fun y => ‖fderiv ℝ φ y‖) (ENNReal.ofReal p)
                  (μ.restrict (Metric.ball c r))).toNNReal)
          (morreyExponent d p) φ (Metric.ball c r) := by
  obtain ⟨K, hK⟩ := exists_norm_sub_average_le (μ := μ) (F := F) hE hd hp
  refine ⟨2 * K, fun φ hφ c r hr => holderOnWith_of_dist_le fun x hx x' hx' => ?_⟩
  rw [NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal, coe_morreyExponent hp hd]
  by_cases hxx : x = x'
  · subst hxx
    simp only [dist_self]
    positivity
  have hρpos : 0 < dist x x' := dist_pos.mpr hxx
  set W : Set (E) :=
    ball x (2 * dist x x') ∩ ball x' (2 * dist x x') ∩ ball c r with hW_def
  have hWmeas : MeasurableSet W :=
    (measurableSet_ball.inter measurableSet_ball).inter measurableSet_ball
  have hWconv : Convex ℝ W := ((convex_ball _ _).inter (convex_ball _ _)).inter (convex_ball _ _)
  have hBlb := lens_volume_lower_bound (μ := μ) hE c x x' hr hx hx' hxx
  have hxW : x ∈ W := ⟨⟨mem_ball_self (by positivity), mem_ball.mpr (by linarith)⟩, hx⟩
  have hx'W : x' ∈ W :=
    ⟨⟨mem_ball.mpr (by rw [dist_comm]; linarith), mem_ball_self (by positivity)⟩, hx'⟩
  have hbx := hK φ hφ c hr hρpos hWmeas hWconv (fun z hz => hz.2) hBlb x hxW (fun z hz => hz.1.1)
  have hbx' := hK φ hφ c hr hρpos hWmeas hWconv (fun z hz => hz.2) hBlb x' hx'W
    (fun z hz => hz.1.2)
  have htri := norm_sub_le_norm_sub_add_norm_sub (φ x) (⨍ y in W, φ y ∂μ) (φ x')
  rw [norm_sub_rev (⨍ y in W, φ y ∂μ) (φ x')] at htri
  rw [dist_eq_norm]
  push_cast
  linarith


/-- **Convergence at every point from convergence on a dense set.** If the maps `Uₙ` are
eventually `γ`-Hölder with a common constant on pairs of points of an open set `B`, converge on a
set `G` that meets every nonempty open subset of `B`, then they converge at every point of `B`.
The Hölder bound makes `Uₙ x` Cauchy, being within `M dist x p ^ γ` of the convergent `Uₙ p` for
a nearby `p ∈ G`. -/
theorem exists_tendsto_of_holder_of_dense {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] [CompleteSpace Y] {B G : Set X}
    (hB : IsOpen B) {M γ : ℝ≥0} (hγ : 0 < γ) {U : ℕ → X → Y}
    (hHol : ∀ x ∈ B, ∀ y ∈ B, ∀ᶠ n in Filter.atTop,
      edist (U n x) (U n y) ≤ (M : ℝ≥0∞) * edist x y ^ (γ : ℝ))
    (hG : ∀ x ∈ G, ∃ ℓ : Y, Filter.Tendsto (fun n => U n x) Filter.atTop (𝓝 ℓ))
    (hdense : ∀ W : Set X, IsOpen W → W ⊆ B → ∀ x ∈ W, ∃ p ∈ W, p ∈ G) :
    ∀ x ∈ B, ∃ ℓ : Y, Filter.Tendsto (fun n => U n x) Filter.atTop (𝓝 ℓ) := by
  intro x hxB
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.mpr fun ε hε => ?_)
  set f : X → ℝ := fun y => (M : ℝ) * dist x y ^ (γ : ℝ) with hf_def
  have hfcont : Continuous f :=
    continuous_const.mul ((continuous_const.dist continuous_id).rpow_const
      fun y => Or.inr γ.coe_nonneg)
  have hfx : f x = 0 := by
    have hγ0 : (γ : ℝ) ≠ 0 := by exact_mod_cast hγ.ne'
    simp only [hf_def, dist_self, Real.zero_rpow hγ0, mul_zero]
  have hxW : x ∈ {y | f y < ε / 3} ∩ B := ⟨by rw [Set.mem_ofPred_eq, hfx]; positivity, hxB⟩
  obtain ⟨p, hpW, hpG⟩ := hdense _ ((isOpen_lt hfcont continuous_const).inter hB)
    Set.inter_subset_right x hxW
  -- Eventually the sequence at `x` stays within `f p` of the sequence at `p`.
  have hev : ∀ᶠ n in Filter.atTop, dist (U n x) (U n p) ≤ f p := by
    filter_upwards [hHol x hxB p hpW.2] with n hn
    rw [edist_dist, edist_dist, ← ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg γ.coe_nonneg, ← ENNReal.ofReal_mul M.coe_nonneg,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hn
    exact hn
  obtain ⟨N1, hN1⟩ := Metric.cauchySeq_iff.mp (hG p hpG).choose_spec.cauchySeq (ε / 3)
    (by positivity)
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N1 N2, fun m hm n hn => ?_⟩
  have e1 := hN2 m (le_trans (le_max_right N1 N2) hm)
  have e2 : dist (U n p) (U n x) ≤ f p := by
    rw [dist_comm]; exact hN2 n (le_trans (le_max_right N1 N2) hn)
  have e3 := hN1 m (le_trans (le_max_left N1 N2) hm) n (le_trans (le_max_left N1 N2) hn)
  calc dist (U m x) (U n x)
      ≤ dist (U m x) (U m p) + dist (U m p) (U n p) + dist (U n p) (U n x) :=
        dist_triangle4 _ _ _ _
    _ < ε := by linarith [hpW.1.out]

/-- **Uniform-limit engine.** A sequence `U n` that is eventually (in `n`) `γ`-Hölder with a common
constant `M` on each pair of points of an open set `B`, and converges pointwise almost everywhere
on `B` to `u`, admits a limit `u'` that is `HolderOnWith M γ` on all of `B` and agrees
with `u` almost everywhere. No Arzelà–Ascoli or continuous-extension machinery is needed: the
Hölder bound provides equicontinuity, density of the almost-everywhere convergence set forces
`U · x` to be Cauchy at every point of `B`, and the closed-ness of `≤` passes the Hölder
inequality to the pointwise limit. -/
theorem exists_holderOnWith_of_ae_tendsto {X Y : Type*} [PseudoMetricSpace X]
    [MetricSpace Y] [CompleteSpace Y] [Nonempty Y] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure] {B : Set X} (hB : IsOpen B) {M γ : ℝ≥0}
    (hγ : 0 < γ)
    {U : ℕ → X → Y} {u : X → Y}
    (hHol : ∀ x ∈ B, ∀ y ∈ B, ∀ᶠ n in Filter.atTop,
        edist (U n x) (U n y) ≤ (M : ℝ≥0∞) * edist x y ^ (γ : ℝ))
    (hae : ∀ᵐ x ∂(μ.restrict B), Filter.Tendsto (fun n => U n x) Filter.atTop (𝓝 (u x))) :
    ∃ u' : X → Y, HolderOnWith M γ u' B ∧ u' =ᵐ[μ.restrict B] u := by
  have := hB.measurableSet
  set G : Set X := {x | Filter.Tendsto (fun n => U n x) Filter.atTop (𝓝 (u x))} with hG_def
  have hbad : μ (Gᶜ ∩ B) = 0 := by
    have h0 := ae_iff.mp hae
    rwa [Measure.restrict_apply' hB.measurableSet] at h0
  -- `G` is dense in every open subset of `B`, because its complement is null.
  have hdense : ∀ W : Set X, IsOpen W → W ⊆ B → ∀ x ∈ W, ∃ p ∈ W, p ∈ G := by
    intro W hW hWB x hxW
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    exact (hW.measure_pos μ ⟨x, hxW⟩).ne' (measure_mono_null
      (fun z hz => ⟨hcon z hz, hWB hz⟩ : W ⊆ Gᶜ ∩ B) hbad)
  have hconv := exists_tendsto_of_holder_of_dense hB hγ hHol (fun x hx => ⟨u x, hx⟩) hdense
  have hu'lim : ∀ x ∈ B, Filter.Tendsto (fun n => U n x) Filter.atTop
      (𝓝 (Filter.limUnder Filter.atTop (fun n => U n x))) :=
    fun x hxB => tendsto_nhds_limUnder (hconv x hxB)
  refine ⟨fun x => Filter.limUnder Filter.atTop (fun n => U n x), fun x hxB y hyB =>
    le_of_tendsto ((hu'lim x hxB).edist (hu'lim y hyB)) (hHol x hxB y hyB), ?_⟩
  filter_upwards [hae, ae_restrict_mem hB.measurableSet] with x hxtend hxB
  exact tendsto_nhds_unique (hu'lim x hxB) hxtend

/-- Two points of a ball lie in a concentric ball of smaller radius. -/
theorem exists_lt_ball_of_mem_ball {X : Type*} [PseudoMetricSpace X] {c x y : X} {r : ℝ}
    (hx : x ∈ Metric.ball c r) (hy : y ∈ Metric.ball c r) :
    ∃ r' : ℝ, 0 < r' ∧ r' < r ∧ x ∈ Metric.ball c r' ∧ y ∈ Metric.ball c r' := by
  rw [Metric.mem_ball] at hx hy
  have h0 : 0 ≤ max (dist x c) (dist y c) := le_max_of_le_left dist_nonneg
  have hlt := max_lt hx hy
  refine ⟨(max (dist x c) (dist y c) + r) / 2, by linarith, by linarith, ?_, ?_⟩ <;>
    rw [Metric.mem_ball]
  · linarith [le_max_left (dist x c) (dist y c)]
  · linarith [le_max_right (dist x c) (dist y c)]

/-- **A mollification of a function with `Lᵖ` weak derivative is uniformly Hölder.** For
`p > d` there is one constant `C` such that, if `u` is integrable on `ball c r` with weak
derivative `G` in `Lᵖ` there, then the mollification of the extension by zero of `u` against any
bump `ρ` is Hölder-`(1 - d/p)` on `ball c r'` with constant `C · ‖G‖_{Lᵖ(ball c r)}`, as soon as
`r' + ρ.rOut ≤ r`. The mollification is smooth, its derivative is the mollified weak
derivative, and Young's inequality bounds that by `G`. -/
theorem exists_holderOnWith_mollify [CompleteSpace F] (hE : Module.finrank ℝ E = d) (hd : 0 < d)
    {p : ℝ} (hp : (d : ℝ) < p) :
    ∃ C : ℝ≥0, ∀ (c : E) {r : ℝ} (u : E → F) (G : E → E →L[ℝ] F),
      IntegrableOn u (ball c r) μ → MemLp G (ENNReal.ofReal p) (μ.restrict (ball c r)) →
      HasWeakFDerivOn ⟨ball c r, isOpen_ball⟩ u G μ →
      ∀ (ρ : ContDiffBump (0 : E)) {r' : ℝ}, 0 < r' → r' + ρ.rOut ≤ r →
        HolderOnWith (C * (eLpNorm G (ENNReal.ofReal p) (μ.restrict (ball c r))).toNNReal)
          (morreyExponent d p) (ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
            (ball c r).indicator u) (ball c r') := by
  obtain ⟨C, hC⟩ := exists_holder_smooth (μ := μ) (F := F) hE hd hp
  refine ⟨C, fun c r u G hu hG hw ρ r' hr' hρr => ?_⟩
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p :=
    ENNReal.one_le_ofReal.mpr (by linarith [(by exact_mod_cast hd : (1 : ℝ) ≤ d)])
  have hGi : IntegrableOn G (ball c r) μ := hG.integrable hp1
  have hsmooth := contDiff_normed_convolution (μ := μ) ρ
    (hu.integrable_indicator measurableSet_ball).locallyIntegrable
  have hderiv : ∀ y ∈ ball c r', fderiv ℝ
      (ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (ball c r).indicator u) y
      = (ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (ball c r).indicator G) y :=
    fun y hy => (hw.hasFDerivAt_convolution measurableSet_ball subset_rfl hu hGi ρ
      (fun w hw => by
        rw [mem_closedBall] at hw
        rw [mem_ball] at hy ⊢
        linarith [dist_triangle w y c])).fderiv
  have hgB : MemLp ((ball c r).indicator G) (ENNReal.ofReal p) μ :=
    (memLp_indicator_iff_restrict (f := G) (p := ENNReal.ofReal p) measurableSet_ball).mpr hG
  have hbound : eLpNorm (fun y => ‖fderiv ℝ
      (ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (ball c r).indicator u) y‖)
      (ENNReal.ofReal p) (μ.restrict (ball c r'))
      ≤ eLpNorm G (ENNReal.ofReal p) (μ.restrict (ball c r)) := by
    rw [eLpNorm_norm _ (hsmooth.continuous_fderiv (by simp)).aestronglyMeasurable,
      eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_ball).2
        (Filter.Eventually.of_forall hderiv))]
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
      ((eLpNorm_convolution_le_of_integral_eq_one hp1 ENNReal.ofReal_ne_top
        (fun x => ρ.nonneg_normed x) ρ.continuous_normed.aestronglyMeasurable ρ.integral_normed
        hgB.aestronglyMeasurable).trans_eq ?_)
    exact eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball
  exact (hC _ hsmooth c hr').mono_const (mul_le_mul_right
    (ENNReal.toNNReal_mono hG.eLpNorm_lt_top.ne hbound) C)

/-- **Morrey's inequality on a ball (weak derivative form).** Let `E` be a finite-dimensional
real normed space of dimension `d` with an additive Haar measure and `p > d`. A function
`u : E → F` into a Banach space that is integrable on `ball c r`, with weak Fréchet derivative
`G` in `Lᵖ` there, has a representative `u'` that is Hölder-`(1 - d/p)` on the ball, with
constant linear in `‖G‖_{Lᵖ(ball c r)}`. The representative is the almost everywhere limit of
the mollifications: each is smooth and, by the smooth estimate on interior sub-balls, uniformly
Hölder with the target constant, and the uniform-limit engine passes to the limit. -/
theorem exists_holderOnWith_of_hasWeakFDerivOn [CompleteSpace F] (hE : Module.finrank ℝ E = d)
    (hd : 0 < d) {p : ℝ} (hp : (d : ℝ) < p) (c : E) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ≥0, ∀ (u : E → F) (G : E → E →L[ℝ] F),
      IntegrableOn u (ball c r) μ → MemLp G (ENNReal.ofReal p) (μ.restrict (ball c r)) →
      HasWeakFDerivOn ⟨ball c r, isOpen_ball⟩ u G μ →
      ∃ u' : E → F, u' =ᵐ[μ.restrict (ball c r)] u ∧
        HolderOnWith (C * (eLpNorm G (ENNReal.ofReal p) (μ.restrict (ball c r))).toNNReal)
          (morreyExponent d p) u' (ball c r) := by
  have hγpos : 0 < morreyExponent d p :=
    Real.toNNReal_pos.mpr (sub_pos.mpr ((div_lt_one ((Nat.cast_nonneg d).trans_lt hp)).mpr hp))
  obtain ⟨C₀, hC₀⟩ := exists_holderOnWith_mollify (μ := μ) (F := F) hE hd hp
  refine ⟨C₀, fun u G hu hG hw => ?_⟩
  have hHol : ∀ x ∈ ball c r, ∀ y ∈ ball c r, ∀ᶠ n in Filter.atTop,
      edist (((mollifier hr n : ContDiffBump (0 : E)).normed μ
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (ball c r).indicator u) x)
        (((mollifier hr n : ContDiffBump (0 : E)).normed μ
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (ball c r).indicator u) y)
        ≤ ((C₀ * (eLpNorm G (ENNReal.ofReal p) (μ.restrict (ball c r))).toNNReal : ℝ≥0) : ℝ≥0∞)
          * edist x y ^ (morreyExponent d p : ℝ) := fun x hx y hy => by
    obtain ⟨r', hr', hrr, hxr, hyr⟩ := exists_lt_ball_of_mem_ball hx hy
    filter_upwards [(tendsto_rOut_mollifier (E := E) hr).eventually
      (Iio_mem_nhds (sub_pos.mpr hrr))]
      with n hn
    exact (hC₀ c u G hu hG hw (mollifier hr n) hr' (by
      simp only [rOut_mollifier] at hn ⊢; linarith)).edist_le hxr hyr
  have hae : ∀ᵐ x ∂(μ.restrict (ball c r)), Filter.Tendsto (fun n =>
      ((mollifier hr n : ContDiffBump (0 : E)).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
        (ball c r).indicator u) x) Filter.atTop (𝓝 (u x)) := by
    have hae0 := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := μ) (g := (ball c r).indicator u) (tendsto_rOut_mollifier hr)
      (Filter.Eventually.of_forall (rOut_mollifier_le_two_mul_rIn hr))
      (hu.integrable_indicator measurableSet_ball).locallyIntegrable
    filter_upwards [ae_restrict_of_ae hae0, ae_restrict_mem measurableSet_ball] with x hx hxmem
    rwa [indicator_of_mem hxmem u] at hx
  obtain ⟨u', hu'H, hu'ae⟩ := exists_holderOnWith_of_ae_tendsto isOpen_ball hγpos hHol hae
  exact ⟨u', hu'ae, hu'H⟩

/-! ### The coordinate statements on `EuclideanSpace ℝ (Fin d)` -/

section Coordinates

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Operator norm bounded by the coordinate values.** On `EuclideanSpace ℝ (Fin d)` the
operator norm of a continuous linear map is at most the sum of the norms of its values on the
standard basis vectors. -/
theorem norm_le_sum_norm_apply_single (L : EuclideanSpace ℝ (Fin d) →L[ℝ] G) :
    ‖L‖ ≤ ∑ k, ‖L (EuclideanSpace.single k (1 : ℝ))‖ := by
  refine ContinuousLinearMap.opNorm_le_bound L (by positivity) (fun x => ?_)
  have hx : x = ∑ k, x k • EuclideanSpace.single k (1 : ℝ) := by
    conv_lhs => rw [← (PiLp.basisFun 2 ℝ (Fin d)).sum_repr x]
    simp only [PiLp.basisFun_repr, PiLp.basisFun_apply, EuclideanSpace.single]
  calc ‖L x‖ = ‖L (∑ k, x k • EuclideanSpace.single k (1 : ℝ))‖ := by rw [← hx]
    _ = ‖∑ k, x k • L (EuclideanSpace.single k (1 : ℝ))‖ := by
        rw [map_sum]; simp_rw [map_smul]
    _ ≤ ∑ k, ‖x k • L (EuclideanSpace.single k (1 : ℝ))‖ := norm_sum_le _ _
    _ = ∑ k, ‖x k‖ * ‖L (EuclideanSpace.single k (1 : ℝ))‖ := by simp_rw [norm_smul]
    _ ≤ ∑ k, ‖x‖ * ‖L (EuclideanSpace.single k (1 : ℝ))‖ :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x k) (norm_nonneg _)
    _ = (∑ k, ‖L (EuclideanSpace.single k (1 : ℝ))‖) * ‖x‖ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **`Lᵖ` seminorm of an operator-valued function by its coordinate components.** For `1 ≤ p`,
the `Lᵖ` seminorm of `Φ : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] G)` is at
most the sum of the `Lᵖ` seminorms of the components `y ↦ Φ y eₖ`. -/
theorem eLpNorm_le_sum_eLpNorm_apply_single {Φ : EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] G} {m : MeasurableSpace (EuclideanSpace ℝ (Fin d))}
    {ν : Measure (EuclideanSpace ℝ (Fin d))} (hΦ : AEStronglyMeasurable Φ ν) {p : ℝ≥0∞}
    (hp : 1 ≤ p)
    (hmeas : ∀ k, AEStronglyMeasurable (fun y => Φ y (EuclideanSpace.single k (1 : ℝ))) ν) :
    eLpNorm Φ p ν ≤ ∑ k, eLpNorm (fun y => Φ y (EuclideanSpace.single k (1 : ℝ))) p ν := by
  calc eLpNorm Φ p ν
      ≤ eLpNorm (fun y => ∑ k, ‖Φ y (EuclideanSpace.single k (1 : ℝ))‖) p ν :=
        eLpNorm_mono_real hΦ fun y => norm_le_sum_norm_apply_single (Φ y)
    _ = eLpNorm (∑ k, fun y => ‖Φ y (EuclideanSpace.single k (1 : ℝ))‖) p ν := by
        refine eLpNorm_congr_ae (Filter.EventuallyEq.of_eq (funext fun y => ?_))
        rw [Finset.sum_apply]
    _ ≤ ∑ k, eLpNorm (fun y => ‖Φ y (EuclideanSpace.single k (1 : ℝ))‖) p ν :=
        eLpNorm_sum_le hp
    _ = ∑ k, eLpNorm (fun y => Φ y (EuclideanSpace.single k (1 : ℝ))) p ν :=
        Finset.sum_congr rfl fun k _ => eLpNorm_norm _ (hmeas k)

/-- The `toNNReal` form of `eLpNorm_le_sum_eLpNorm_apply_single`, for components in `Lᵖ`. -/
theorem toNNReal_eLpNorm_le_sum_apply_single {Φ : EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] G} {m : MeasurableSpace (EuclideanSpace ℝ (Fin d))}
    {ν : Measure (EuclideanSpace ℝ (Fin d))} (hΦ : AEStronglyMeasurable Φ ν) {p : ℝ≥0∞}
    (hp : 1 ≤ p)
    (hmem : ∀ k, MemLp (fun y => Φ y (EuclideanSpace.single k (1 : ℝ))) p ν) :
    (eLpNorm Φ p ν).toNNReal
      ≤ ∑ k, (eLpNorm (fun y => Φ y (EuclideanSpace.single k (1 : ℝ))) p ν).toNNReal :=
  (ENNReal.toNNReal_mono (ENNReal.sum_ne_top.mpr fun k _ => (hmem k).eLpNorm_lt_top.ne)
    (eLpNorm_le_sum_eLpNorm_apply_single hΦ hp fun k => (hmem k).aestronglyMeasurable)).trans_eq
    (ENNReal.toNNReal_sum fun k _ => (hmem k).eLpNorm_lt_top.ne)

end Coordinates


/-- **`Lᵖ` seminorm of a derivative by its coordinate partials.** For a function with continuous
derivative, the `Lᵖ` seminorm of `fderiv ℝ u` is at most the sum of the `Lᵖ` seminorms of the
coordinate partials, for `1 ≤ p`. -/
theorem eLpNorm_fderiv_le_sum_partialD {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : Continuous (fderiv ℝ u)) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {μ : Measure (EuclideanSpace ℝ (Fin d))} (hmeas : ∀ k, AEStronglyMeasurable (partialD k u) μ) :
    eLpNorm (fderiv ℝ u) p μ ≤ ∑ k, eLpNorm (partialD k u) p μ :=
  eLpNorm_le_sum_eLpNorm_apply_single hu.aestronglyMeasurable hp hmeas

/-- **A partial derivative of a mollification falls on the mollifier.** For a locally integrable
`f` and a bump `ρ`, `∂ₖ (f ⋆ ρ_normed) = f ⋆ ∂ₖ ρ_normed`. -/
theorem partialD_convolution_normed {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : LocallyIntegrable f volume) (ρ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (k : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    partialD k (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ.normed volume) x
      = (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] partialD k (ρ.normed volume)) x := by
  have hρ_cd : ContDiff ℝ (⊤ : ℕ∞) (ρ.normed volume) := ρ.contDiff_normed
  have hρ_cd1 : ContDiff ℝ 1 (ρ.normed volume) := hρ_cd.of_le (by exact_mod_cast le_top)
  have hderiv := ρ.hasCompactSupport_normed.hasFDerivAt_convolution_right
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hf hρ_cd1 x
  have hprec := convolution_precompR_apply (𝕜 := ℝ) (L := ContinuousLinearMap.lsmul ℝ ℝ) hf
    (ρ.hasCompactSupport_normed.fderiv (𝕜 := ℝ)) (hρ_cd.continuous_fderiv (by simp)) x
    (EuclideanSpace.single k 1)
  change (fderiv ℝ _ x) (EuclideanSpace.single k 1) = _
  rw [hderiv.fderiv, hprec]
  rfl

/-- The partial derivative of a reflected function. -/
theorem partialD_comp_sub_left {ρ : EuclideanSpace ℝ (Fin d) → ℝ} (hρ : Differentiable ℝ ρ)
    (k : Fin d) (x y : EuclideanSpace ℝ (Fin d)) :
    partialD k (fun z => ρ (x - z)) y = -partialD k ρ (x - y) := by
  have hfd : HasFDerivAt (fun z => ρ (x - z))
      ((fderiv ℝ ρ (x - y)).comp (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)))) y :=
    (hρ (x - y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
  change (fderiv ℝ _ y) (EuclideanSpace.single k 1) = _
  rw [hfd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, _root_.neg_apply, ContinuousLinearMap.id_apply,
    map_neg, partialD]

/-- **Gradient-convolution bridge.** If `g` is the weak gradient of `u` on a measurable
set `B` and `ρ` is a normalised bump of outer radius `ε` centred at `0`, then at every interior
point `x` with `Metric.closedBall x ε ⊆ B` the `k`-th partial of the mollification equals the
mollified gradient component: `partialD k (uB ⋆ ρ) x = (gBk ⋆ ρ) x`, where `uB`, `gBk` are the
extensions by zero off `B`. At `B = Set.univ` the support hypothesis is vacuous and the
indicators are the identity, which is the form the `Lᵖ` bootstrap consumes. -/
theorem partialD_convolution_eq_of_hasWeakGradOn
    {B : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u B volume)
    (hg : HasWeakGradOn B u g)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))) (k : Fin d)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : Metric.closedBall x φ.rOut ⊆ B) :
    partialD k
        (B.indicator u ⋆[ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ), volume]
          (φ.normed volume)) x
      = (B.indicator (g k)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ), volume] (φ.normed volume)) x := by
  have hρ_diff : Differentiable ℝ (φ.normed volume) :=
    (φ.contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) (φ.normed volume)).differentiable (by simp)
  -- Rewrite an indicator-kernel convolution at `x` as a set integral over `B`.
  have conv_setInt : ∀ (w f : EuclideanSpace ℝ (Fin d) → ℝ),
      (B.indicator w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x
        = ∫ y in B, w y * f (x - y) := fun w f => by
    rw [convolution_def, ← MeasureTheory.integral_indicator hB]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change ContinuousLinearMap.lsmul ℝ ℝ (B.indicator w y) (f (x - y))
      = B.indicator (fun z => w z * f (x - z)) y
    rw [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    exact (Set.indicator_mul_left B w (fun z => f (x - z))).symm
  -- The test function `ψ y = ρ (x - y)` is supported in `closedBall x φ.rOut ⊆ B`.
  set ψ : EuclideanSpace ℝ (Fin d) → ℝ := fun y => φ.normed volume (x - y) with hψ_def
  have hsub_tsup : tsupport ψ ⊆ Metric.closedBall x φ.rOut := by
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    have hxy : x - y ∈ tsupport (φ.normed volume) :=
      subset_tsupport _ (show x - y ∈ Function.support (φ.normed volume) from hy)
    rw [φ.tsupport_normed_eq, Metric.mem_closedBall, dist_zero_right] at hxy
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    exact hxy
  have hibp := hg ψ (φ.contDiff_normed.comp (contDiff_const.sub contDiff_id))
    (IsCompact.of_isClosed_subset (isCompact_closedBall x φ.rOut) (isClosed_tsupport ψ) hsub_tsup)
    (hsub_tsup.trans hx) k
  simp only [hψ_def, partialD_comp_sub_left hρ_diff, mul_neg] at hibp
  rw [MeasureTheory.integral_neg] at hibp
  rw [partialD_convolution_normed (hu.integrable_indicator hB).locallyIntegrable,
    conv_setInt u (partialD k (φ.normed volume)), conv_setInt (g k) (φ.normed volume)]
  exact neg_inj.mp hibp


/-- **Morrey on a ball in the smooth case, coordinate-partial form.** For `p > d` there is one
constant `C` such that every smooth `v` with coordinate partials in `Lᵖ(ball c r)` is
Hölder-`(1 - d/p)` on the ball with constant `C · ∑ₖ ‖∂ₖ v‖_{Lᵖ(ball c r)}`, whatever the centre
and the radius. -/
theorem exists_holder_smooth_partialD (hd : 0 < d) {p : ℝ} (hp : (d : ℝ) < p) :
    ∃ C : ℝ≥0, ∀ (v : EuclideanSpace ℝ (Fin d) → ℝ), ContDiff ℝ (⊤ : ℕ∞) v →
      ∀ (c : EuclideanSpace ℝ (Fin d)) {r : ℝ}, 0 < r →
        (∀ k, MemLp (fun y => partialD k v y) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball c r))) →
          HolderOnWith
            (C * ∑ k, (eLpNorm (fun y => partialD k v y) (ENNReal.ofReal p)
                        (volume.restrict (Metric.ball c r))).toNNReal)
            (morreyExponent d p) v (Metric.ball c r) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p :=
    ENNReal.one_le_ofReal.mpr (by linarith [(by exact_mod_cast hd : (1 : ℝ) ≤ d)])
  obtain ⟨C, hC⟩ := exists_holder_smooth (E := EuclideanSpace ℝ (Fin d)) (F := ℝ)
    (μ := volume) finrank_euclideanSpace_fin hd hp
  refine ⟨C, fun v hv c r hr hmem x hx y hy => (hC v hv c hr x hx y hy).trans
    (mul_le_mul_left (ENNReal.coe_le_coe.mpr (mul_le_mul_right ?_ C)) _)⟩
  have hfd := hv.continuous_fderiv (by simp)
  rw [eLpNorm_norm _ hfd.aestronglyMeasurable]
  exact toNNReal_eLpNorm_le_sum_apply_single hfd.aestronglyMeasurable hp1 hmem

/-- **Morrey on a ball in the smooth case.** A smooth `u` with gradient components `gₖ = ∂ₖu`
in `Lᵖ(ball c r)` (`p > d`) is Hölder-`(1−d/p)` on the ball, with constant linear in
`∑ₖ ‖gₖ‖_{Lᵖ(ball c r)}`. -/
theorem morrey_ball_contDiff (hd : 0 < d) {p : ℝ} (hp : (d : ℝ) < p)
    (c : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ), ContDiff ℝ (⊤ : ℕ∞) u →
      (∀ k, MemLp (fun y => partialD k u y) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball c r))) →
        HolderOnWith
          (C * ∑ k, (eLpNorm (fun y => partialD k u y) (ENNReal.ofReal p)
                      (volume.restrict (Metric.ball c r))).toNNReal)
          (morreyExponent d p) u (Metric.ball c r) := by
  obtain ⟨C, hC⟩ := exists_holder_smooth_partialD hd hp
  exact ⟨C, fun u hu hmem => hC u hu c hr hmem⟩

/-- **Morrey embedding on a ball (weak-gradient form).** For `p > d`, a function `u` that is
integrable on `Metric.ball c r` with an `Lᵖ` weak gradient `g` there has a continuous
representative `u'` which is Hölder-`(1 - d/p)` on the ball, with constant linear in
`∑ₖ ‖gₖ‖_{Lᵖ(ball c r)}`. This is the coordinate form of
`exists_holderOnWith_of_hasWeakFDerivOn`. -/
theorem morrey_ball (hd : 0 < d) {p : ℝ} (hp : (d : ℝ) < p)
    (c : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      IntegrableOn u (Metric.ball c r) volume →
      (∀ k, MemLp (g k) (ENNReal.ofReal p) (volume.restrict (Metric.ball c r))) →
      HasWeakGradOn (Metric.ball c r) u g →
      ∃ u' : EuclideanSpace ℝ (Fin d) → ℝ,
        u' =ᵐ[volume.restrict (Metric.ball c r)] u ∧
        HolderOnWith
          (C * ∑ k, (eLpNorm (g k) (ENNReal.ofReal p)
                      (volume.restrict (Metric.ball c r))).toNNReal)
          (morreyExponent d p) u' (Metric.ball c r) := by
  obtain ⟨C, hC⟩ := exists_holderOnWith_of_hasWeakFDerivOn (E := EuclideanSpace ℝ (Fin d))
    (F := ℝ) (μ := volume) finrank_euclideanSpace_fin hd hp c hr
  refine ⟨C, fun u g hu hmemg hweak => ?_⟩
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p :=
    ENNReal.one_le_ofReal.mpr (by linarith [(by exact_mod_cast hd : (1 : ℝ) ≤ d)])
  have hgi : ∀ k, LocallyIntegrableOn (g k) (Metric.ball c r) volume := fun k => by
    have h : IntegrableOn (g k) (Metric.ball c r) volume := (hmemg k).integrable hp1
    exact h.locallyIntegrableOn
  have hw := (hasWeakGradOn_iff_hasWeakFDerivOn Metric.isOpen_ball hu.locallyIntegrableOn hgi).1
    hweak
  have hG : ∀ k, MemLp (fun y => gradCLM g y (EuclideanSpace.single k (1 : ℝ))) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball c r)) := fun k => by simpa using hmemg k
  have hGm : AEStronglyMeasurable (gradCLM g) (volume.restrict (Metric.ball c r)) := by
    rw [show gradCLM g = ∑ k, fun y => g k y • (EuclideanSpace.proj k :
      EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) from funext fun y => by simp [gradCLM]]
    exact Finset.aestronglyMeasurable_sum Finset.univ fun k _ =>
      (hmemg k).aestronglyMeasurable.smul_const _
  have hbound := toNNReal_eLpNorm_le_sum_apply_single hGm hp1 hG
  simp only [gradCLM_apply_single] at hbound
  have hGp : MemLp (gradCLM g) (ENNReal.ofReal p) (volume.restrict (Metric.ball c r)) :=
    memLp_iff.2 ((eLpNorm_le_sum_eLpNorm_apply_single hGm hp1
      fun k => (hG k).aestronglyMeasurable).trans_lt (ENNReal.sum_lt_top.mpr fun k _ =>
      (hG k).eLpNorm_lt_top))
  obtain ⟨u', hu'ae, hu'H⟩ := hC u (gradCLM g) hu hGp hw
  exact ⟨u', hu'ae, hu'H.mono_const (mul_le_mul_right hbound C)⟩

/-- At the exponent `2d` the Morrey exponent is `1/2`, whatever the dimension. -/
theorem morreyExponent_two_mul (hd : 0 < d) : morreyExponent d (2 * (d : ℝ)) = (1 / 2 : ℝ≥0) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hnn : 0 ≤ 1 - (d : ℝ) / (2 * (d : ℝ)) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  refine NNReal.coe_injective ?_
  rw [morreyExponent, Real.coe_toNNReal _ hnn]
  push_cast
  field_simp
  norm_num

end EllipticPdes.Embedding
