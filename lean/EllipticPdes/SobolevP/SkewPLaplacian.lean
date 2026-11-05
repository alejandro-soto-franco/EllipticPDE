/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Monotone.BrowderMinty
public import EllipticPdes.SobolevP.PLaplacian

/-!
# `p`-Laplacian with a skew principal part

For `2 ≤ p`, a set `Ω` of finite measure, `0 < c` and a bounded strongly measurable field `S` of
bilinear forms on `E` with `S x ξ ξ = 0`, the operator
`u ↦ -div (|∇u|^{p-2} ∇u) + c |u|^{p-2} u - div (S ∇u)` on `W₀^{1,p}(Ω)` is strictly monotone,
hemicontinuous and coercive. It is therefore a bijection onto the dual by the Browder–Minty
theorem. The gradient is read in `E` by the Riesz isometry `PLap.dualE`, as in `pForm`. The skew
part `skewForm` is a bounded bilinear form with `skewForm u u = 0`. A nonzero `S` makes
`skewForm` antisymmetric and nonzero. The operator is then not a potential operator. For `S` built
from a stream function it is a divergence-free drift. The hypothesis `2 ≤ p` puts `∇u` in `L²` on
a set of finite measure. This bounds `skewForm`.

Hemicontinuity of the `p`-Laplacian part follows from convexity of its energy alone: the Gateaux
derivative of a convex continuous functional is continuous along lines
(`continuous_apply_add_smul_of_convex_gateaux`).

## Main declarations

* `EllipticPdes.skewForm`: the bilinear form `∫_Ω S ∇u ∇v`.
* `EllipticPdes.skewCLM`: `skewForm` as a continuous bilinear map, with `skewCLM_apply`.
* `EllipticPdes.skewForm_self`: `skewForm u u = 0`.
* `EllipticPdes.continuous_apply_add_smul_of_convex_gateaux`: continuity of the derivative of a
  convex potential along a line.
* `EllipticPdes.existsUnique_weakSolution_skewPLaplacian`: existence and uniqueness for the
  `p`-Laplacian with a skew principal part (Brezis, Theorem 5.16, p. 145).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace EllipticPdes

section Convex

private lemma continuous_segment {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (U V : X) :
    Continuous fun t : ℝ => (1 - t) • U + t • V := by fun_prop

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {J : X → ℝ}
  {A : X → StrongDual ℝ X}

/-- **Continuity of a convex derivative along a line.** If `J` is convex and continuous with
Gateaux derivative `A`, then `t ↦ ⟨A (x + t y), w⟩` is continuous. The gradient inequality bounds
`⟨A z, w⟩` above by the continuous difference quotient `(J (z + h w) - J z) / h` and below by
`(J z - J (z - h w)) / h`; both quotients tend to `⟨A z₀, w⟩` as `h → 0` at the base point. -/
theorem continuous_apply_add_smul_of_convex_gateaux (hJc : ConvexOn ℝ univ J)
    (hJ0 : Continuous J)
    (hJ : ∀ u v, HasDerivAt (fun t : ℝ => J (u + t • v)) (A u v) 0) (x y w : X) :
    Continuous (fun t : ℝ => A (x + t • y) w) := by
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  set z₀ := x + t₀ • y with hz₀
  have hz : ∀ t : ℝ, x + t • y = z₀ + (t - t₀) • y := fun t => by
    rw [hz₀]; module
  have hzc : Continuous (fun t : ℝ => x + t • y) := by fun_prop
  -- upper and lower gradient bounds
  have up : ∀ (t h : ℝ), 0 < h → A (x + t • y) w ≤ (J (x + t • y + h • w) - J (x + t • y)) / h := by
    intro t h hh
    have := gradient_inequality_of_convex_gateaux hJc hJ (x + t • y) (x + t • y + h • w)
    rw [le_div_iff₀ hh]
    simp only [add_sub_cancel_left, map_smul, smul_eq_mul] at this
    linarith
  have lo : ∀ (t h : ℝ), 0 < h → (J (x + t • y) - J (x + t • y - h • w)) / h ≤ A (x + t • y) w := by
    intro t h hh
    have := gradient_inequality_of_convex_gateaux hJc hJ (x + t • y) (x + t • y - h • w)
    rw [div_le_iff₀ hh]
    simp only [sub_sub_cancel_left, map_neg, map_smul, smul_eq_mul] at this
    linarith
  rw [Metric.continuousAt_iff]
  intro ε hε
  -- base-point quotients
  have h1 := (hJ z₀ w).tendsto_slope_zero_right
  have h2 := (hJ z₀ (-w)).tendsto_slope_zero_right
  have e1 := (Metric.tendsto_nhds.1 h1) (ε / 2) (by positivity)
  have e2 := (Metric.tendsto_nhds.1 h2) (ε / 2) (by positivity)
  obtain ⟨h, hh, hh1, hh2⟩ : ∃ h : ℝ, 0 < h ∧
      dist (h⁻¹ • (J (z₀ + h • w) - J z₀)) (A z₀ w) < ε / 2 ∧
      dist (h⁻¹ • (J (z₀ + h • -w) - J z₀)) (A z₀ (-w)) < ε / 2 := by
    have := (e1.and e2).and (Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1))
    obtain ⟨h, ⟨⟨a, b⟩, c⟩⟩ := this.exists
    refine ⟨h, c.1, ?_, ?_⟩
    · simpa using a
    · simpa using b
  have cu : Continuous (fun t : ℝ => (J (x + t • y + h • w) - J (x + t • y)) / h) := by
    refine Continuous.div_const (Continuous.sub ?_ ?_) _
    · exact hJ0.comp (by fun_prop)
    · exact hJ0.comp hzc
  have cl : Continuous (fun t : ℝ => (J (x + t • y) - J (x + t • y - h • w)) / h) := by
    refine Continuous.div_const (Continuous.sub ?_ ?_) _
    · exact hJ0.comp hzc
    · exact hJ0.comp (by fun_prop)
  have hε2 : 0 < ε / 2 := by positivity
  have ev1 := (cu.continuousAt (x := t₀)).eventually (Metric.ball_mem_nhds _ hε2)
  have ev2 := (cl.continuousAt (x := t₀)).eventually (Metric.ball_mem_nhds _ hε2)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 (ev1.and ev2)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  obtain ⟨u1, l1⟩ := hδ' ht
  have c1 : (J (x + t₀ • y + h • w) - J (x + t₀ • y)) / h = h⁻¹ * (J (z₀ + h • w) - J z₀) := by
    rw [div_eq_inv_mul]
  have c2 : (J (x + t₀ • y) - J (x + t₀ • y - h • w)) / h =
      -(h⁻¹ * (J (z₀ + h • -w) - J z₀)) := by
    rw [div_eq_inv_mul]
    simp only [smul_neg, ← sub_eq_add_neg]
    ring
  simp only [Real.dist_eq] at u1 l1 hh1 hh2 ⊢
  simp only [smul_eq_mul, map_neg] at hh1 hh2
  rw [c1] at u1
  rw [c2] at l1
  have U := up t h hh
  have L := lo t h hh
  rw [abs_lt] at u1 l1 hh1 hh2 ⊢
  constructor <;> linarith [u1.1, u1.2, l1.1, l1.2, hh1.1, hh1.2, hh2.1, hh2.2]

/-- The derivative of a convex potential is continuous along the segment `(1 - t) u + t v`. -/
private theorem continuous_apply_segment_of_convex_gateaux (hJc : ConvexOn ℝ univ J)
    (hJ0 : Continuous J)
    (hJ : ∀ u v, HasDerivAt (fun t : ℝ => J (u + t • v)) (A u v) 0) (u v w : X) :
    Continuous (fun t : ℝ => A ((1 - t) • u + t • v) w) := by
  have e : ∀ t : ℝ, (1 - t) • u + t • v = u + t • (v - u) := fun t => by module
  simp only [e]
  exact continuous_apply_add_smul_of_convex_gateaux hJc hJ0 hJ u (v - u) w

end Convex

section Holder

variable {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
variable {F : Type*} [NormedAddCommGroup F]

/-- **`L²` bound on a finite measure space.** For `2 ≤ p` and `G`, `H` in `L^p`, the product
`‖G‖ ‖H‖` is integrable and `∫ ‖G‖ ‖H‖ ≤ ν(univ)^{1 - 2/p} ‖G‖_p ‖H‖_p`. This is Cauchy–Schwarz
after the embedding `L^p ⊆ L²` on a finite measure space. -/
private theorem integral_norm_mul_le_of_two_le {p : ℝ} (hp : 2 ≤ p) [Fact (1 ≤ ENNReal.ofReal p)]
    (G H : Lp F (ENNReal.ofReal p) ν) :
    Integrable (fun x => ‖G x‖ * ‖H x‖) ν ∧
      ∫ x, ‖G x‖ * ‖H x‖ ∂ν ≤
        ((ν univ ^ (1 / (2 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p).toReal)).toReal) ^ 2 *
          (‖G‖ * ‖H‖) := by
  have hP : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have hG2 : MemLp (fun x => ‖G x‖) 2 ν := (Lp.memLp G).norm.mono_exponent hP
  have hH2 : MemLp (fun x => ‖H x‖) 2 ν := (Lp.memLp H).norm.mono_exponent hP
  have hmul : MemLp ((fun x => ‖G x‖) * (fun x => ‖H x‖)) 1 ν := hG2.mul hH2
  have hint : Integrable (fun x => ‖G x‖ * ‖H x‖) ν := memLp_one_iff_integrable.1 hmul
  refine ⟨hint, ?_⟩
  set c : ℝ≥0∞ := ν univ ^ (1 / (2 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p).toReal) with hc
  have hexp : 0 ≤ 1 / (2 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p).toReal := by
    rw [ENNReal.toReal_ofReal (by linarith)]
    have : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [this]
    have : 1 / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp
    linarith
  have hcfin : c ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top ν _)
  have hGe : eLpNorm (fun x => ‖G x‖) 2 ν ≤ ENNReal.ofReal ‖G‖ * c := by
    rw [eLpNorm_norm _ (Lp.memLp G).aestronglyMeasurable, ofReal_norm, Lp.enorm_def]
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hP (Lp.memLp G).aestronglyMeasurable
  have hHe : eLpNorm (fun x => ‖H x‖) 2 ν ≤ ENNReal.ofReal ‖H‖ * c := by
    rw [eLpNorm_norm _ (Lp.memLp H).aestronglyMeasurable, ofReal_norm, Lp.enorm_def]
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hP (Lp.memLp H).aestronglyMeasurable
  have hsm := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) (μ := ν)
    hG2.aestronglyMeasurable hH2.aestronglyMeasurable
  have h1 : ENNReal.ofReal (∫ x, ‖G x‖ * ‖H x‖ ∂ν) ≤
      (ENNReal.ofReal ‖G‖ * c) * (ENNReal.ofReal ‖H‖ * c) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    have e : ∫⁻ x, ENNReal.ofReal (‖G x‖ * ‖H x‖) ∂ν =
        eLpNorm ((fun x => ‖G x‖) • (fun x => ‖H x‖)) 1 ν := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      · refine lintegral_congr fun x => ?_
        simp [Real.enorm_eq_ofReal (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      · exact hG2.aestronglyMeasurable.mul hH2.aestronglyMeasurable
    rw [e]
    exact hsm.trans (mul_le_mul' hGe hHe)
  have e2 : (ENNReal.ofReal ‖G‖ * c) * (ENNReal.ofReal ‖H‖ * c) =
      ENNReal.ofReal (c.toReal ^ 2 * (‖G‖ * ‖H‖)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (norm_nonneg _),
      ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hcfin]
    ring
  rw [e2] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1

end Holder

section Main

open PLap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}
  {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
  (S : E → E →L[ℝ] E →L[ℝ] ℝ)

/-- The skew form `∫_Ω S(x) (∇u(x)) (∇v(x)) dμ` on `W₀^{1,p}(Ω)`, where `S(x)` is a bilinear form
on `E` and `∇u` is read in `E` by the Riesz isometry `PLap.dualE`, as in `pForm`. -/
def skewForm (U V : W1p0 (ENNReal.ofReal p) μ Ω) : ℝ :=
  ∫ x, S x (dualE E (W1p0.gradL U x)) (dualE E (W1p0.gradL V x)) ∂(μ.restrict Ω)

variable {S}

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The integrand of `skewForm` is integrable when `S` is measurable and bounded and `2 ≤ p`. -/
private lemma integrable_skew (hΩ : μ Ω ≠ ∞) (hp : 2 ≤ p) (hS : StronglyMeasurable S) {M : ℝ}
    (hM : ∀ x, ‖S x‖ ≤ M) (G H : Lp (StrongDual ℝ E) (ENNReal.ofReal p) (μ.restrict Ω)) :
    Integrable (fun x => S x (dualE E (G x)) (dualE E (H x))) (μ.restrict Ω) := by
  have : IsFiniteMeasure (μ.restrict Ω) := ⟨by simpa [lt_top_iff_ne_top] using hΩ⟩
  have hM0 : 0 ≤ M := (ContinuousLinearMap.opNorm_nonneg _).trans (hM 0)
  refine ((integral_norm_mul_le_of_two_le hp G H).1.const_mul M).mono' ?_
    (Eventually.of_forall fun x => ?_)
  · have hΦ : Continuous (fun q : (E →L[ℝ] E →L[ℝ] ℝ) × E × E => q.1 q.2.1 q.2.2) :=
      (continuous_fst.clm_apply continuous_snd.fst).clm_apply continuous_snd.snd
    exact hΦ.comp_aestronglyMeasurable (hS.aestronglyMeasurable.prodMk
      ((memLp_comp (dualE E) G).aestronglyMeasurable.prodMk
        (memLp_comp (dualE E) H).aestronglyMeasurable))
  · calc ‖S x (dualE E (G x)) (dualE E (H x))‖
        ≤ ‖S x‖ * ‖G x‖ * ‖H x‖ := by
          refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
          have := ContinuousLinearMap.le_opNorm (S x) (dualE E (G x))
          rw [LinearIsometryEquiv.norm_map] at this ⊢
          nlinarith [norm_nonneg (H x), norm_nonneg (S x (dualE E (G x)))]
      _ ≤ M * (‖G x‖ * ‖H x‖) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (hM x) (by positivity)

omit [FiniteDimensional ℝ E] in
private lemma norm_gradL_le (hp : 1 < p) (U : W1p0 (ENNReal.ofReal p) μ Ω) :
    ‖W1p0.gradL U‖ ≤ ‖U‖ := by
  have hp0 : 0 < p := by linarith
  have h := W1p0.norm_rpow_eq hp U
  have a1 : 0 ≤ ‖W1p0.fnL U‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp0).1 (by linarith)

/-- `skewForm` is bounded: `|skewForm u v| ≤ C ‖u‖ ‖v‖` for some constant `C`. -/
private lemma exists_abs_skewForm_le (hΩ : μ Ω ≠ ∞) (hp : 2 ≤ p) (hS : StronglyMeasurable S) {M : ℝ}
    (hM : ∀ x, ‖S x‖ ≤ M) :
    ∃ C : ℝ, ∀ U V : W1p0 (ENNReal.ofReal p) μ Ω, |skewForm S U V| ≤ C * (‖U‖ * ‖V‖) := by
  have : IsFiniteMeasure (μ.restrict Ω) := ⟨by simpa [lt_top_iff_ne_top] using hΩ⟩
  have hM0 : 0 ≤ M := (ContinuousLinearMap.opNorm_nonneg _).trans (hM 0)
  set K : ℝ := ((μ.restrict Ω) univ ^ (1 / (2 : ℝ≥0∞).toReal -
    1 / (ENNReal.ofReal p).toReal)).toReal ^ 2 with hK
  refine ⟨M * K, fun U V => ?_⟩
  have hb := integral_norm_mul_le_of_two_le hp (W1p0.gradL U) (W1p0.gradL V)
  have hint := integrable_skew hΩ hp hS hM (W1p0.gradL U) (W1p0.gradL V)
  have h1 : |skewForm S U V| ≤ ∫ x, M * (‖W1p0.gradL U x‖ * ‖W1p0.gradL V x‖) ∂(μ.restrict Ω) := by
    unfold skewForm
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono hint.norm (hb.1.const_mul M) fun x => ?_
    calc ‖S x (dualE E (W1p0.gradL U x)) (dualE E (W1p0.gradL V x))‖
        ≤ ‖S x‖ * ‖W1p0.gradL U x‖ * ‖W1p0.gradL V x‖ := by
          refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
          have := ContinuousLinearMap.le_opNorm (S x) (dualE E (W1p0.gradL U x))
          rw [LinearIsometryEquiv.norm_map] at this ⊢
          nlinarith [norm_nonneg (W1p0.gradL V x), norm_nonneg (S x (dualE E (W1p0.gradL U x)))]
      _ ≤ M * (‖W1p0.gradL U x‖ * ‖W1p0.gradL V x‖) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (hM x) (by positivity)
  rw [integral_const_mul] at h1
  have hu := norm_gradL_le (by linarith) U
  have hv := norm_gradL_le (by linarith) V
  have hK0 : 0 ≤ K := sq_nonneg _
  calc |skewForm S U V| ≤ M * ∫ x, ‖W1p0.gradL U x‖ * ‖W1p0.gradL V x‖ ∂(μ.restrict Ω) := h1
    _ ≤ M * (K * (‖W1p0.gradL U‖ * ‖W1p0.gradL V‖)) := mul_le_mul_of_nonneg_left hb.2 hM0
    _ ≤ M * (K * (‖U‖ * ‖V‖)) := by
        gcongr
    _ = M * K * (‖U‖ * ‖V‖) := by ring

private lemma skewForm_smul_left (a : ℝ) (U V : W1p0 (ENNReal.ofReal p) μ Ω) :
    skewForm S (a • U) V = a * skewForm S U V := by
  unfold skewForm
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul a (W1p0.gradL U)] with x hx
  simp only [hx, Pi.smul_apply, map_smul, smul_apply, smul_eq_mul]

private lemma skewForm_smul_right (a : ℝ) (U V : W1p0 (ENNReal.ofReal p) μ Ω) :
    skewForm S U (a • V) = a * skewForm S U V := by
  unfold skewForm
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul a (W1p0.gradL V)] with x hx
  simp only [hx, Pi.smul_apply, map_smul, smul_eq_mul]

section Linear

variable (hΩ : μ Ω ≠ ∞) (hp : 2 ≤ p) (hS : StronglyMeasurable S) {M : ℝ}
  (hM : ∀ x, ‖S x‖ ≤ M)

include hΩ hp hS hM

private lemma skewForm_add_left (U U' V : W1p0 (ENNReal.ofReal p) μ Ω) :
    skewForm S (U + U') V = skewForm S U V + skewForm S U' V := by
  unfold skewForm
  rw [← integral_add (integrable_skew hΩ hp hS hM _ _) (integrable_skew hΩ hp hS hM _ _)]
  refine integral_congr_ae ?_
  rw [map_add]
  filter_upwards [Lp.coeFn_add (W1p0.gradL U) (W1p0.gradL U')] with x hx
  simp only [hx, Pi.add_apply, map_add, add_apply]

private lemma skewForm_add_right (U V V' : W1p0 (ENNReal.ofReal p) μ Ω) :
    skewForm S U (V + V') = skewForm S U V + skewForm S U V' := by
  unfold skewForm
  rw [← integral_add (integrable_skew hΩ hp hS hM _ _) (integrable_skew hΩ hp hS hM _ _)]
  refine integral_congr_ae ?_
  rw [map_add]
  filter_upwards [Lp.coeFn_add (W1p0.gradL V) (W1p0.gradL V')] with x hx
  simp only [hx, Pi.add_apply, map_add]

end Linear

/-- **`skewForm` as a continuous bilinear map.** For a bounded strongly measurable field `S` and
`2 ≤ p`, `skewCLM` is `skewForm S` as a continuous bilinear map on `W₀^{1,p}(Ω)`. -/
@[no_expose] def skewCLM (hΩ : μ Ω ≠ ∞) (hp : 2 ≤ p) (hS : StronglyMeasurable S) {M : ℝ}
    (hM : ∀ x, ‖S x‖ ≤ M) :
    W1p0 (ENNReal.ofReal p) μ Ω →L[ℝ] W1p0 (ENNReal.ofReal p) μ Ω →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ (skewForm S) (skewForm_add_left hΩ hp hS hM)
      skewForm_smul_left (skewForm_add_right hΩ hp hS hM)
      skewForm_smul_right).mkContinuous₂ (Classical.choose (exists_abs_skewForm_le hΩ hp hS hM))
    fun U V => by
      rw [mul_assoc]
      exact (Real.norm_eq_abs _).le.trans
        (Classical.choose_spec (exists_abs_skewForm_le hΩ hp hS hM) U V)

/-- `skewCLM` agrees with `skewForm`. -/
theorem skewCLM_apply (hΩ : μ Ω ≠ ∞) (hp : 2 ≤ p) (hS : StronglyMeasurable S) {M : ℝ}
    (hM : ∀ x, ‖S x‖ ≤ M) (U V : W1p0 (ENNReal.ofReal p) μ Ω) :
    skewCLM hΩ hp hS hM U V = skewForm S U V := by
  simp [skewCLM]

/-- A skew field makes the diagonal of `skewForm` vanish. -/
theorem skewForm_self (hskew : ∀ x ξ, S x ξ ξ = 0) (U : W1p0 (ENNReal.ofReal p) μ Ω) :
    skewForm S U U = 0 := by
  unfold skewForm
  simp [hskew]

/-- The operator `u ↦ pOp u + B u`, the screened `p`-Laplacian plus the skew part. -/
def skewPOp (hp : 1 < p) (c : ℝ)
    (B : W1p0 (ENNReal.ofReal p) μ Ω →L[ℝ] W1p0 (ENNReal.ofReal p) μ Ω →L[ℝ] ℝ)
    (U : W1p0 (ENNReal.ofReal p) μ Ω) : StrongDual ℝ (W1p0 (ENNReal.ofReal p) μ Ω) :=
  pOp hp c U + B U

section Operator

variable {c : ℝ} (B : W1p0 (ENNReal.ofReal p) μ Ω →L[ℝ] W1p0 (ENNReal.ofReal p) μ Ω →L[ℝ] ℝ)

private lemma skewPOp_apply (hp : 1 < p) (U V : W1p0 (ENNReal.ofReal p) μ Ω) :
    skewPOp hp c B U V = pOp hp c U V + B U V := rfl

private lemma skewPOp_sub_apply (hp : 1 < p) (U V W : W1p0 (ENNReal.ofReal p) μ Ω) :
    (skewPOp hp c B U - skewPOp hp c B V) W = (pOp hp c U - pOp hp c V) W + B (U - V) W := by
  simp only [skewPOp, sub_apply, add_apply, map_sub]
  ring

variable {B}

/-- The operator `skewPOp` is strictly monotone: the skew part has `B w w = 0`. -/
theorem isStrictlyMonotoneOp_skewPOp (hp : 1 < p) (hc : 0 < c) (hB : ∀ w, B w w = 0) :
    IsStrictlyMonotoneOp Set.univ (skewPOp hp c B) := by
  intro U _ V _ hUV
  have h := isStrictlyMonotoneOp_of_strictConvex_gateaux (pEnergy_strictConvex hp hc)
    (hasDerivAt_pOp hp c) U (mem_univ _) V (mem_univ _) hUV
  rw [skewPOp_sub_apply, hB, add_zero]
  exact h

/-- The operator `skewPOp` is hemicontinuous. -/
theorem isHemicontinuousOp_skewPOp (hp : 1 < p) (hc : 0 < c) :
    IsHemicontinuousOp Set.univ (skewPOp hp c B) := by
  intro U _ V _ W
  have h1 := continuous_apply_segment_of_convex_gateaux
    (J := pEnergy (p := p) (μ := μ) (Ω := Ω) c) (A := pOp hp c)
    (pEnergy_convex hp hc.le) (pEnergy_continuous hp c) (hasDerivAt_pOp hp c) U V W
  have h2 := ((ContinuousLinearMap.apply ℝ ℝ W).continuous.comp B.continuous).comp
    (continuous_segment U V)
  exact (h1.add h2).continuousOn

/-- The operator `skewPOp` is coercive: the skew part has `B w w = 0`. -/
theorem isCoerciveOp_skewPOp (hp : 1 < p) (hc : 0 < c) (hB : ∀ w, B w w = 0) :
    IsCoerciveOp Set.univ (skewPOp hp c B) := by
  obtain ⟨v₀, hv₀, h⟩ := isCoerciveOp_pOp (p := p) (μ := μ) (Ω := Ω) hp hc
  refine ⟨v₀, hv₀, h.congr fun v => ?_⟩
  rw [skewPOp_sub_apply, hB, add_zero]

end Operator

/-- **`p`-Laplacian with a skew principal part.** Let `E` be a finite-dimensional real
inner-product space with an additive Haar measure `μ`, `Ω` a set of finite measure, `2 ≤ p < ∞`
and `0 < c`. Let `S` be a bounded strongly measurable field of bilinear forms on `E` with
`S x ξ ξ = 0`. For every `f` in the dual of `W₀^{1,p}(Ω)` there is a unique `u` with
`∫ ‖∇u‖^{p-2} ⟪∇u, ∇v⟫ + c ∫ |u|^{p-2} u v + ∫ S ∇u ∇v = f v` for all `v`. The operator is the
screened `p`-Laplacian plus `-div (S ∇u)`. It is strictly monotone, hemicontinuous and coercive
on the reflexive space `W₀^{1,p}(Ω)`, hence bijective by the Browder–Minty theorem (Brezis,
Theorem 5.16, p. 145). It is not a potential operator in general. Callers supply
`[Fact (1 ≤ ENNReal.ofReal p)]` with `fact_one_le_ofReal`. -/
theorem existsUnique_weakSolution_skewPLaplacian (hΩ : μ Ω ≠ ∞) (hp : 2 ≤ p) {c : ℝ}
    (hc : 0 < c) (hS : StronglyMeasurable S) {M : ℝ} (hM : ∀ x, ‖S x‖ ≤ M)
    (hskew : ∀ x ξ, S x ξ ξ = 0) (f : StrongDual ℝ (W1p0 (ENNReal.ofReal p) μ Ω)) :
    ∃! u : W1p0 (ENNReal.ofReal p) μ Ω, ∀ v : W1p0 (ENNReal.ofReal p) μ Ω,
      pForm c u v + skewForm S u v = f v := by
  have hp1 : 1 < p := by linarith
  have hX := isReflexive_W1p0 (p := ENNReal.ofReal p) (μ := μ) (Ω := Ω) hΩ
    (ENNReal.one_lt_ofReal.2 hp1) ENNReal.ofReal_ne_top
  have hcomplete : CompleteSpace (W1p0 (ENNReal.ofReal p) μ Ω) :=
    (isClosed_W1p0 (ENNReal.ofReal p) μ Ω).completeSpace_coe
  set B := skewCLM hΩ hp hS hM with hBdef
  have hB : ∀ U V, B U V = skewForm S U V := skewCLM_apply hΩ hp hS hM
  have hBself : ∀ w, B w w = 0 := fun w => by rw [hB, skewForm_self hskew]
  have hAapp : ∀ U V, skewPOp hp1 c B U V = pForm c U V + skewForm S U V := fun U V => by
    rw [skewPOp_apply, pOp_apply, hB]
  obtain ⟨u, hu, huniq⟩ := (bijective_of_strictlyMonotone hX
    (isStrictlyMonotoneOp_skewPOp hp1 hc hBself) (isHemicontinuousOp_skewPOp hp1 hc)
    (isCoerciveOp_skewPOp hp1 hc hBself)).existsUnique f
  refine ⟨u, fun v => by rw [← hAapp, hu], fun w hw => huniq w ?_⟩
  ext v
  rw [hAapp]
  exact hw v

end Main

end EllipticPdes
