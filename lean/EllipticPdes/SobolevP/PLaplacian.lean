/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Analysis.LqDerivative
public import EllipticPdes.Monotone.Potential
public import EllipticPdes.SobolevP.Reflexive
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Screened `p`-Laplacian on `W₀^{1,p}`

For `1 < p < ∞`, a finite-dimensional real inner-product space `E`, an additive Haar measure
`μ`, a set `Ω` of finite measure and `0 < c`, the energy
`pEnergy c u = (1/p) ∫ ‖∇u‖^p + (c/p) ∫ |u|^p` on `W₀^{1,p}(Ω)` is convex, continuous and
Gateaux differentiable, and its derivative `pOp` is coercive. The space is reflexive, so the
direct method of `Monotone/Potential.lean` gives a weak solution of
`∫ ‖∇u‖^{p-2} ⟪∇u, ∇v⟫ + c ∫ |u|^{p-2} u v = f v` for every `f` in the dual. Strict convexity
of the energy gives uniqueness.

The gradient part takes values in `E*`. The Riesz isometry `dualE` reads it in `E`, where
`‖·‖^p` is differentiable because the norm of an inner-product space is smooth. The derivative
of `t ↦ ∫ ‖g + t h‖^p` is proved here for functions into an inner-product space, following
`EllipticPdes.Analysis.hasDerivAt_integral_abs_rpow`.

## Main declarations

* `EllipticPdes.pEnergy`: the energy.
* `EllipticPdes.pEnergy_convex`, `EllipticPdes.pEnergy_continuous`,
  `EllipticPdes.pEnergy_gateaux`: its convexity, continuity and Gateaux derivative `pForm`.
* `EllipticPdes.exists_weakSolution_pLaplacian`: existence for `0 < c`.
* `EllipticPdes.existsUnique_weakSolution_pLaplacian`: uniqueness.
* `EllipticPdes.PLap.hasDerivAt_integral_norm_rpow`: the derivative of the `L^p` modulus.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace EllipticPdes

namespace PLap

section Pointwise

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
/-- `‖y‖^{r-2} ‖y‖ ≤ a^{r-1}` whenever `‖y‖ ≤ a`. -/
lemma rpow_sub_two_mul_le {r : ℝ} (hr : 1 < r) {y : F} {a : ℝ} (hy : ‖y‖ ≤ a) (ha : 0 ≤ a) :
    ‖y‖ ^ (r - 2) * ‖y‖ ≤ a ^ (r - 1) := by
  rcases eq_or_lt_of_le (norm_nonneg y) with h | h
  · rw [← h, mul_zero]
    exact Real.rpow_nonneg ha _
  · have hsplit : ‖y‖ ^ (r - 2) * ‖y‖ ^ (1 : ℝ) = ‖y‖ ^ (r - 2 + 1) :=
      (Real.rpow_add h _ _).symm
    rw [Real.rpow_one] at hsplit
    rw [hsplit, show r - 2 + 1 = r - 1 by ring]
    exact Real.rpow_le_rpow (norm_nonneg y) hy (by linarith)

lemma norm_combo_le' (a b : F) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ‖s • a + t • b‖ ≤ s * ‖a‖ + t * ‖b‖ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]

/-- Convexity of `‖·‖^r` in a normed space. -/
lemma norm_rpow_combo_le {r : ℝ} (hr : 1 ≤ r) (a b : F) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s + t = 1) : ‖s • a + t • b‖ ^ r ≤ s * ‖a‖ ^ r + t * ‖b‖ ^ r := by
  calc ‖s • a + t • b‖ ^ r ≤ (s * ‖a‖ + t * ‖b‖) ^ r :=
        Real.rpow_le_rpow (norm_nonneg _) (norm_combo_le' a b hs ht) (by linarith)
    _ ≤ s * ‖a‖ ^ r + t * ‖b‖ ^ r := by
      have := (convexOn_rpow hr).2 (Set.mem_Ici.2 (norm_nonneg a))
        (Set.mem_Ici.2 (norm_nonneg b)) hs ht hst
      simpa [smul_eq_mul] using this

/-- Strict convexity of `‖·‖^r` in a strictly convex normed space. -/
lemma norm_rpow_combo_lt [StrictConvexSpace ℝ F] {r : ℝ} (hr : 1 < r) {a b : F} (hab : a ≠ b)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t = 1) :
    ‖s • a + t • b‖ ^ r < s * ‖a‖ ^ r + t * ‖b‖ ^ r := by
  have hr0 : 0 < r := by linarith
  by_cases hn : ‖a‖ = ‖b‖
  · have h := norm_combo_lt_of_ne (le_refl ‖a‖) hn.symm.le hab hs ht hst
    calc ‖s • a + t • b‖ ^ r < ‖a‖ ^ r := Real.rpow_lt_rpow (norm_nonneg _) h hr0
      _ = s * ‖a‖ ^ r + t * ‖b‖ ^ r := by rw [← hn, ← add_mul, hst, one_mul]
  · calc ‖s • a + t • b‖ ^ r ≤ (s * ‖a‖ + t * ‖b‖) ^ r :=
          Real.rpow_le_rpow (norm_nonneg _) (norm_combo_le' a b hs.le ht.le) (by positivity)
      _ < s * ‖a‖ ^ r + t * ‖b‖ ^ r := by
        have := (strictConvexOn_rpow hr).2 (Set.mem_Ici.2 (norm_nonneg a))
          (Set.mem_Ici.2 (norm_nonneg b)) hn hs ht hst
        simpa [smul_eq_mul] using this

end Pointwise

section Integral

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma ofReal_toReal_aux {r : ℝ} (hr : 1 < r) : (ENNReal.ofReal r).toReal = r :=
  ENNReal.toReal_ofReal (by linarith)

omit [InnerProductSpace ℝ H] in
/-- `(‖g‖)^{r-1} ‖h‖` is integrable for `g`, `h` in `L^r`. -/
lemma integrable_norm_rpow_mul {r : ℝ} (hr : 1 < r) {g h : α → H}
    (hg : MemLp g (ENNReal.ofReal r) ν) (hh : MemLp h (ENNReal.ofReal r) ν) :
    Integrable (fun x => ‖g x‖ ^ (r - 1) * ‖h x‖) ν := by
  have hp1 : 1 < (ENNReal.ofReal r).toReal := by rwa [ofReal_toReal_aux hr]
  have hint := Analysis.integrable_abs_rpow_sub_one_mul ENNReal.ofReal_ne_top hp1
    (u := fun x => ‖g x‖) (v := fun x => ‖h x‖) hg.norm hh.norm
  rw [ofReal_toReal_aux hr] at hint
  refine hint.mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (hg.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable.mul
      hh.aestronglyMeasurable.norm
  · simp only [norm_norm, norm_mul]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (norm_nonneg _) (by linarith [norm_nonneg (h x)]) (by linarith))
      (norm_nonneg _)

/-- The pairing integrand is integrable. -/
lemma integrable_pair {r : ℝ} (hr : 1 < r) {g h : α → H}
    (hg : MemLp g (ENNReal.ofReal r) ν) (hh : MemLp h (ENNReal.ofReal r) ν) :
    Integrable (fun x => ‖g x‖ ^ (r - 2) * inner ℝ (g x) (h x)) ν := by
  refine (integrable_norm_rpow_mul hr hg hh).mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (hg.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable.mul
      (hg.aestronglyMeasurable.inner hh.aestronglyMeasurable)
  · rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    calc ‖g x‖ ^ (r - 2) * ‖inner ℝ (g x) (h x)‖
        ≤ ‖g x‖ ^ (r - 2) * (‖g x‖ * ‖h x‖) :=
          mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _)
            (Real.rpow_nonneg (norm_nonneg _) _)
      _ = (‖g x‖ ^ (r - 2) * ‖g x‖) * ‖h x‖ := by ring
      _ ≤ ‖g x‖ ^ (r - 1) * ‖h x‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact rpow_sub_two_mul_le hr le_rfl (norm_nonneg _)

/-- **Derivative of the `L^r` norm functional along a line.** For `g`, `h` in `L^r` with `r > 1`,
`t ↦ ∫ ‖g + t h‖^r` is differentiable at `0` with derivative `r ∫ ‖g‖^{r-2} ⟪g, h⟫`. The proof
repeats `EllipticPdes.Analysis.hasDerivAt_integral_abs_rpow` with the Fréchet derivative of
`‖·‖^r` on an inner-product space (Evans, §8.1.2). -/
theorem hasDerivAt_integral_norm_rpow {r : ℝ} (hr : 1 < r) {g h : α → H}
    (hg : MemLp g (ENNReal.ofReal r) ν) (hh : MemLp h (ENNReal.ofReal r) ν) :
    HasDerivAt (fun t : ℝ => ∫ x, ‖g x + t • h x‖ ^ r ∂ν)
      (r * ∫ x, ‖g x‖ ^ (r - 2) * inner ℝ (g x) (h x) ∂ν) 0 := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hp0 : ENNReal.ofReal r ≠ 0 := by simpa using hr0
  set F : ℝ → α → ℝ := fun t x => ‖g x + t • h x‖ ^ r with hFdef
  set F' : ℝ → α → ℝ := fun t x =>
    r * (‖g x + t • h x‖ ^ (r - 2) * inner ℝ (g x + t • h x) (h x)) with hF'def
  set bound : α → ℝ := fun x => r * (‖g x‖ + ‖h x‖) ^ (r - 1) * ‖h x‖ with hbdef
  have hline : ∀ t : ℝ, AEStronglyMeasurable (fun x => g x + t • h x) ν := fun t =>
    hg.aestronglyMeasurable.add (hh.aestronglyMeasurable.const_smul t)
  have hFmeas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) ν :=
    Eventually.of_forall (fun t =>
      ((hline t).norm.aemeasurable.pow_const r).aestronglyMeasurable)
  have hFint : Integrable (F 0) ν := by
    have := hg.integrable_norm_rpow hp0 ENNReal.ofReal_ne_top
    simpa [hFdef, ofReal_toReal_aux hr] using this
  have hF'meas : AEStronglyMeasurable (F' 0) ν := by
    simp only [hF'def, zero_smul, add_zero]
    exact ((hg.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable.mul
      (hg.aestronglyMeasurable.inner hh.aestronglyMeasurable)).const_mul r
  have hbound_int : Integrable bound ν := by
    have := (Analysis.integrable_abs_rpow_sub_one_mul (p := ENNReal.ofReal r)
      ENNReal.ofReal_ne_top (by rwa [ofReal_toReal_aux hr])
      (u := fun x => ‖g x‖) (v := fun x => ‖h x‖) hg.norm hh.norm).const_mul r
    rw [ofReal_toReal_aux hr] at this
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [norm_norm, hbdef]
    ring
  have hbound : ∀ᵐ x ∂ν, ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖F' t x‖ ≤ bound x := by
    refine Eventually.of_forall (fun x t ht => ?_)
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    set y := g x + t • h x with hy
    have hy1 : ‖y‖ ≤ ‖g x‖ + ‖h x‖ := by
      refine (norm_add_le _ _).trans ?_
      have : ‖t • h x‖ ≤ ‖h x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) ht.le
      linarith
    have hstep := rpow_sub_two_mul_le hr hy1 (by positivity)
    have hnn : (0 : ℝ) ≤ r * ‖y‖ ^ (r - 2) :=
      mul_nonneg hr0.le (Real.rpow_nonneg (norm_nonneg _) _)
    calc ‖F' t x‖ = r * ‖y‖ ^ (r - 2) * ‖inner ℝ y (h x)‖ := by
          simp only [hF'def, ← hy, norm_mul, Real.norm_of_nonneg hr0.le,
            Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg y) _)]
          ring
      _ ≤ r * ‖y‖ ^ (r - 2) * (‖y‖ * ‖h x‖) :=
          mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) hnn
      _ = r * (‖y‖ ^ (r - 2) * ‖y‖) * ‖h x‖ := by ring
      _ ≤ r * (‖g x‖ + ‖h x‖) ^ (r - 1) * ‖h x‖ := by
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hr0.le)
            (norm_nonneg (h x))
          linarith [this]
  have hdiff : ∀ᵐ x ∂ν, ∀ t ∈ Metric.ball (0 : ℝ) 1, HasDerivAt (F · x) (F' t x) t := by
    refine Eventually.of_forall (fun x t _ => ?_)
    have h1 : HasDerivAt (fun t : ℝ => g x + t • h x) (h x) t := by
      simpa using ((hasDerivAt_id t).smul_const (h x)).const_add (g x)
    have := (hasFDerivAt_norm_rpow (g x + t • h x) hr).comp_hasDerivAt t h1
    refine HasDerivAt.congr_deriv this ?_
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, mul_assoc,
      hF'def]
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
    (bound := bound) (Metric.ball_mem_nhds (0 : ℝ) one_pos) hFmeas hFint hF'meas hbound
    hbound_int hdiff
  have := hmain.2
  simp only [hF'def, zero_smul, add_zero] at this
  rw [integral_const_mul] at this
  simpa [hFdef] using this

/-- Strict convexity of the `L^r` modulus along a segment between distinct classes. -/
lemma integral_norm_rpow_combo_lt [StrictConvexSpace ℝ H] {r : ℝ} (hr : 1 < r) {g h : α → H}
    (hg : MemLp g (ENNReal.ofReal r) ν) (hh : MemLp h (ENNReal.ofReal r) ν)
    (hne : ¬ g =ᵐ[ν] h) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t = 1) :
    ∫ x, ‖s • g x + t • h x‖ ^ r ∂ν < s * ∫ x, ‖g x‖ ^ r ∂ν + t * ∫ x, ‖h x‖ ^ r ∂ν := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hp0 : ENNReal.ofReal r ≠ 0 := by simpa using hr0
  have ev := ofReal_toReal_aux hr
  have hgi : Integrable (fun x => ‖g x‖ ^ r) ν := by
    simpa [ev] using hg.integrable_norm_rpow hp0 ENNReal.ofReal_ne_top
  have hhi : Integrable (fun x => ‖h x‖ ^ r) ν := by
    simpa [ev] using hh.integrable_norm_rpow hp0 ENNReal.ofReal_ne_top
  have hci : Integrable (fun x => ‖s • g x + t • h x‖ ^ r) ν := by
    simpa [ev] using ((hg.const_smul s).add (hh.const_smul t)).integrable_norm_rpow hp0
      ENNReal.ofReal_ne_top
  have hrhs : Integrable (fun x => s * ‖g x‖ ^ r + t * ‖h x‖ ^ r) ν :=
    (hgi.const_mul s).add (hhi.const_mul t)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hgi.const_mul s)
    (hhi.const_mul t), ← sub_pos, ← integral_sub hrhs hci]
  refine (integral_pos_iff_support_of_nonneg_ae
    (f := fun x => s * ‖g x‖ ^ r + t * ‖h x‖ ^ r - ‖s • g x + t • h x‖ ^ r)
    (Eventually.of_forall fun x => sub_nonneg.2
      (norm_rpow_combo_le hr.le _ _ hs.le ht.le hst)) (hrhs.sub hci)).2 ?_
  rw [Filter.EventuallyEq, ae_iff] at hne
  refine lt_of_lt_of_le (pos_iff_ne_zero.2 hne) (measure_mono fun x hx => ?_)
  have := norm_rpow_combo_lt hr hx hs ht hst
  simp only [Function.mem_support, ne_eq]
  linarith

end Integral

section Lp

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}
variable {F : Type*} [NormedAddCommGroup F]

/-- **Modulus of an `L^r` class.** The `r`-th power of the norm equals the modulus integral. -/
lemma integral_norm_rpow_eq {r : ℝ} (hr : 1 < r)
    (G : Lp F (ENNReal.ofReal r) ν) : ∫ x, ‖G x‖ ^ r ∂ν = ‖G‖ ^ r := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hp0 : ENNReal.ofReal r ≠ 0 := by simpa using hr0
  have h := (Lp.memLp G).eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top
  rw [ofReal_toReal_aux hr] at h
  have hI : 0 ≤ ∫ x, ‖G x‖ ^ r ∂ν := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  rw [Lp.norm_def, h, ENNReal.toReal_ofReal (Real.rpow_nonneg hI _),
    Real.rpow_inv_rpow hI hr0.ne']

end Lp

section Pairing

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (T : F ≃ₗᵢ[ℝ] H) {r : ℝ} [Fact (1 ≤ ENNReal.ofReal r)]

omit [Fact (1 ≤ ENNReal.ofReal r)] in
lemma pair_bound (hr : 1 < r) (a b : H) :
    |‖a‖ ^ (r - 2) * inner ℝ a b| ≤ ‖a‖ ^ (r - 1) * ‖b‖ := by
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  calc ‖a‖ ^ (r - 2) * |inner ℝ a b| ≤ ‖a‖ ^ (r - 2) * (‖a‖ * ‖b‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _)
          (Real.rpow_nonneg (norm_nonneg _) _)
    _ = (‖a‖ ^ (r - 2) * ‖a‖) * ‖b‖ := by ring
    _ ≤ ‖a‖ ^ (r - 1) * ‖b‖ := by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact rpow_sub_two_mul_le hr le_rfl (norm_nonneg _)

omit [Fact (1 ≤ ENNReal.ofReal r)] in
lemma memLp_comp (V : Lp F (ENNReal.ofReal r) ν) :
    MemLp (fun x => T (V x)) (ENNReal.ofReal r) ν :=
  T.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' (Lp.memLp V)

/-- The pairing `∫ ‖G‖^{r-2} ⟪T G, T V⟫`. -/
def pairing (G V : Lp F (ENNReal.ofReal r) ν) : ℝ :=
  ∫ x, ‖G x‖ ^ (r - 2) * inner ℝ (T (G x)) (T (V x)) ∂ν

omit [Fact (1 ≤ ENNReal.ofReal r)] in
lemma integrable_pairing (hr : 1 < r) (G V : Lp F (ENNReal.ofReal r) ν) :
    Integrable (fun x => ‖G x‖ ^ (r - 2) * inner ℝ (T (G x)) (T (V x))) ν := by
  have := integrable_pair hr (memLp_comp T G) (memLp_comp T V)
  simpa only [T.norm_map] using this

omit [Fact (1 ≤ ENNReal.ofReal r)] in
lemma pairing_add (hr : 1 < r) (G V W : Lp F (ENNReal.ofReal r) ν) :
    pairing T G (V + W) = pairing T G V + pairing T G W := by
  unfold pairing
  rw [← integral_add (integrable_pairing T hr G V) (integrable_pairing T hr G W)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add V W] with x hx
  simp only [hx, Pi.add_apply, map_add, inner_add_right, mul_add]

omit [Fact (1 ≤ ENNReal.ofReal r)] in
lemma pairing_smul (G : Lp F (ENNReal.ofReal r) ν) (c : ℝ)
    (V : Lp F (ENNReal.ofReal r) ν) : pairing T G (c • V) = c * pairing T G V := by
  unfold pairing
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c V] with x hx
  simp only [hx, Pi.smul_apply, map_smul, inner_smul_right]
  ring

lemma abs_pairing_le (hr : 1 < r) (G V : Lp F (ENNReal.ofReal r) ν) :
    |pairing T G V| ≤ ‖G‖ ^ (r - 1) * ‖V‖ := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  set q := Real.conjExponent r with hq
  have hqdef : q = r / (r - 1) := rfl
  have hconj : q.HolderConjugate r := (Real.HolderConjugate.conjExponent hr).symm
  have hfmem : MemLp (fun x => ‖G x‖ ^ (r - 1)) (ENNReal.ofReal q) ν := by
    have h := (Lp.memLp G).norm_rpow_div (ENNReal.ofReal (r - 1))
    rw [ENNReal.toReal_ofReal hr1.le, ← ENNReal.ofReal_div_of_pos hr1] at h
    exact h
  have hVmem : MemLp (fun x => ‖V x‖) (ENNReal.ofReal r) ν := (Lp.memLp V).norm
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg (G x)) (r - 1) :
      0 ≤ᵐ[ν] fun x => ‖G x‖ ^ (r - 1))
    (Eventually.of_forall fun x => norm_nonneg (V x) : 0 ≤ᵐ[ν] fun x => ‖V x‖) hfmem hVmem
  have hint : Integrable (fun x => ‖G x‖ ^ (r - 1) * ‖V x‖) ν :=
    integrable_norm_rpow_mul hr (Lp.memLp G) (Lp.memLp V)
  have h1 : |pairing T G V| ≤ ∫ x, ‖G x‖ ^ (r - 1) * ‖V x‖ ∂ν := by
    rw [pairing]
    refine abs_integral_le_integral_abs.trans ?_
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hint
      (Eventually.of_forall fun x => ?_)
    have := pair_bound hr (T (G x)) (T (V x))
    simpa only [T.norm_map] using this
  have h2 : ∫ x, (‖G x‖ ^ (r - 1)) ^ q ∂ν = ‖G‖ ^ r := by
    rw [← integral_norm_rpow_eq hr G]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← Real.rpow_mul (norm_nonneg _), hqdef]
    congr 1
    field_simp
  have h3 : ∫ x, ‖V x‖ ^ r ∂ν = ‖V‖ ^ r := integral_norm_rpow_eq hr V
  refine h1.trans (hH.trans (le_of_eq ?_))
  rw [h2, h3, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_mul (norm_nonneg _)]
  have e : r * (1 / q) = r - 1 := by rw [hqdef]; field_simp
  rw [e, mul_one_div_cancel hr0.ne', Real.rpow_one]

/-- The continuous linear functional `V ↦ ∫ ‖G‖^{r-2} ⟪T G, T V⟫` on `L^r`. -/
def pairCLM (hr : 1 < r) (G : Lp F (ENNReal.ofReal r) ν) :
    Lp F (ENNReal.ofReal r) ν →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := pairing T G
      map_add' := pairing_add T hr G
      map_smul' := pairing_smul T G }
    (‖G‖ ^ (r - 1)) (fun V => by rw [Real.norm_eq_abs]; exact abs_pairing_le T hr G V)

lemma pairCLM_apply (hr : 1 < r) (G V : Lp F (ENNReal.ofReal r) ν) :
    pairCLM T hr G V = ∫ x, ‖G x‖ ^ (r - 2) * inner ℝ (T (G x)) (T (V x)) ∂ν := rfl

end Pairing

section PairingLp

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (T : F ≃ₗᵢ[ℝ] H) {r : ℝ} [Fact (1 ≤ ENNReal.ofReal r)]

omit [Fact (1 ≤ ENNReal.ofReal r)] in
/-- The modulus of a line in `L^r` is the modulus of the transported line. -/
lemma integral_norm_rpow_add_smul (G V : Lp F (ENNReal.ofReal r) ν) (t : ℝ) :
    ∫ x, ‖(G + t • V) x‖ ^ r ∂ν = ∫ x, ‖T (G x) + t • T (V x)‖ ^ r ∂ν := by
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add G (t • V), Lp.coeFn_smul t V] with x h1 h2
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, ← T.norm_map]
  simp

include T in
omit [Fact (1 ≤ ENNReal.ofReal r)] in
/-- Strict convexity of `‖·‖^r` on `L^r` along a segment between distinct classes. -/
lemma lp_norm_rpow_combo_lt [StrictConvexSpace ℝ H] (hr : 1 < r) {G W : Lp F (ENNReal.ofReal r) ν}
    (hne : G ≠ W) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t = 1) :
    ‖s • G + t • W‖ ^ r < s * ‖G‖ ^ r + t * ‖W‖ ^ r := by
  rw [← integral_norm_rpow_eq hr G, ← integral_norm_rpow_eq hr W,
    ← integral_norm_rpow_eq hr (s • G + t • W)]
  have hcongr : ∫ x, ‖(s • G + t • W) x‖ ^ r ∂ν = ∫ x, ‖s • T (G x) + t • T (W x)‖ ^ r ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add (s • G) (t • W), Lp.coeFn_smul s G, Lp.coeFn_smul t W]
      with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, ← T.norm_map]
    simp
  rw [hcongr]
  have hn : ¬ (fun x => T (G x)) =ᵐ[ν] fun x => T (W x) := by
    intro h
    apply hne
    refine Lp.ext ?_
    filter_upwards [h] with x hx using T.injective hx
  have := integral_norm_rpow_combo_lt hr (memLp_comp T G) (memLp_comp T W) hn hs ht hst
  simpa only [T.norm_map] using this

end PairingLp

end PLap

section Abstract

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {J : X → ℝ}
  {A : X → StrongDual ℝ X}

/-- **Strict convexity gives strict monotonicity.** The Gateaux derivative of a strictly convex
functional is strictly monotone. Strict convexity at the midpoint, combined with the gradient
inequality at the base point, gives `⟨A u, v - u⟩ < J v - J u` for `u ≠ v`; adding the two
instances yields the claim. -/
theorem isStrictlyMonotoneOp_of_strictConvex_gateaux (hJs : StrictConvexOn ℝ Set.univ J)
    (hJ : ∀ u v, HasDerivAt (fun t : ℝ => J (u + t • v)) (A u v) 0) :
    IsStrictlyMonotoneOp Set.univ A := by
  have key : ∀ u v : X, u ≠ v → A u (v - u) < J v - J u := by
    intro u v huv
    have hs := hJs.2 (Set.mem_univ u) (Set.mem_univ v) huv
      (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    have hg := gradient_inequality_of_convex_gateaux hJs.convexOn hJ u
      ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v)
    have e : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v - u = (1 / 2 : ℝ) • (v - u) := by module
    rw [e, map_smul, smul_eq_mul] at hg
    simp only [smul_eq_mul] at hs
    linarith
  intro u _ v _ huv
  have h1 := key u v huv
  have h2 := key v u huv.symm
  have e : (A u - A v) (u - v) = -(A u (v - u)) - A v (u - v) := by
    have : u - v = -(v - u) := by abel
    rw [sub_apply, this, map_neg, map_neg]
  rw [e]
  linarith

end Abstract

section Main

open PLap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}
  {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

variable (E) in
/-- The Riesz identification of the dual `E*` with `E`, as a real linear isometry equivalence. -/
def dualE : StrongDual ℝ E ≃ₗᵢ[ℝ] E where
  toFun := (InnerProductSpace.toDual ℝ E).symm
  invFun := InnerProductSpace.toDual ℝ E
  map_add' := map_add _
  map_smul' c x := by simp
  left_inv := fun x => (InnerProductSpace.toDual ℝ E).apply_symm_apply x
  right_inv := fun x => (InnerProductSpace.toDual ℝ E).symm_apply_apply x
  norm_map' := (InnerProductSpace.toDual ℝ E).symm.norm_map

/-- The function part of an element of `W₀^{1,p}`, as a continuous linear map. -/
def W1p0.fnL : W1p0 (ENNReal.ofReal p) μ Ω →L[ℝ] Lp ℝ (ENNReal.ofReal p) (μ.restrict Ω) :=
  (W1pGraph.fnL (p := ENNReal.ofReal p) (μ := μ) (Ω := Ω)).comp
    (W1p0 (ENNReal.ofReal p) μ Ω).subtypeL

/-- The gradient part of an element of `W₀^{1,p}`, as a continuous linear map. -/
def W1p0.gradL :
    W1p0 (ENNReal.ofReal p) μ Ω →L[ℝ] Lp (StrongDual ℝ E) (ENNReal.ofReal p) (μ.restrict Ω) :=
  (W1pGraph.gradL (p := ENNReal.ofReal p) (μ := μ) (Ω := Ω)).comp
    (W1p0 (ENNReal.ofReal p) μ Ω).subtypeL

/-- The energy `(1/p) ∫ ‖∇u‖^p + (c/p) ∫ |u|^p` of the screened `p`-Laplacian on `W₀^{1,p}(Ω)`,
with the integrals over `Ω`. -/
def pEnergy (c : ℝ) (U : W1p0 (ENNReal.ofReal p) μ Ω) : ℝ :=
  (1 / p) * ∫ x, ‖W1p0.gradL U x‖ ^ p ∂(μ.restrict Ω) +
    (c / p) * ∫ x, |W1p0.fnL U x| ^ p ∂(μ.restrict Ω)

/-- The weak form `∫ ‖∇u‖^{p-2} ⟪∇u, ∇v⟫ + c ∫ |u|^{p-2} u v` of the screened `p`-Laplacian, with
`∇u` read in `E` by `dualE`. -/
def pForm (c : ℝ) (U V : W1p0 (ENNReal.ofReal p) μ Ω) : ℝ :=
  (∫ x, ‖W1p0.gradL U x‖ ^ (p - 2) *
      inner ℝ (dualE E (W1p0.gradL U x)) (dualE E (W1p0.gradL V x)) ∂(μ.restrict Ω)) +
    c * ∫ x, |W1p0.fnL U x| ^ (p - 2) * W1p0.fnL U x * W1p0.fnL V x ∂(μ.restrict Ω)

omit [Fact (1 ≤ ENNReal.ofReal p)] in
/-- `1 < p` gives the exponent fact needed for the norm on `L^p`. -/
theorem fact_one_le_ofReal (hp : 1 < p) : Fact (1 ≤ ENNReal.ofReal p) :=
  ⟨by simpa using hp.le⟩

omit [FiniteDimensional ℝ E] in
lemma pEnergy_eq (hp : 1 < p) (c : ℝ) (U : W1p0 (ENNReal.ofReal p) μ Ω) :
    pEnergy c U = (1 / p) * ‖W1p0.gradL U‖ ^ p + (c / p) * ‖W1p0.fnL U‖ ^ p := by
  unfold pEnergy
  rw [integral_norm_rpow_eq hp (W1p0.gradL U)]
  have : ∫ x, |W1p0.fnL U x| ^ p ∂(μ.restrict Ω) = ‖W1p0.fnL U‖ ^ p := by
    simp_rw [← Real.norm_eq_abs]
    exact integral_norm_rpow_eq hp _
  rw [this]

omit [FiniteDimensional ℝ E] in
/-- The energy is continuous. -/
theorem pEnergy_continuous (hp : 1 < p) (c : ℝ) :
    Continuous (pEnergy (p := p) (μ := μ) (Ω := Ω) c) := by
  have hp0 : 0 ≤ p := by linarith
  have : (pEnergy (p := p) (μ := μ) (Ω := Ω) c) = fun U =>
      (1 / p) * ‖W1p0.gradL U‖ ^ p + (c / p) * ‖W1p0.fnL U‖ ^ p := funext (pEnergy_eq hp c)
  rw [this]
  exact (continuous_const.mul ((W1p0.gradL.continuous.norm).rpow_const fun _ => Or.inr hp0)).add
    (continuous_const.mul ((W1p0.fnL.continuous.norm).rpow_const fun _ => Or.inr hp0))

omit [FiniteDimensional ℝ E] in
/-- The energy is convex for a non-negative screening coefficient. -/
theorem pEnergy_convex (hp : 1 < p) {c : ℝ} (hc : 0 ≤ c) :
    ConvexOn ℝ Set.univ (pEnergy (p := p) (μ := μ) (Ω := Ω) c) := by
  have hp0 : 0 < p := by linarith
  refine ⟨convex_univ, fun U _ W _ a b ha hb hab => ?_⟩
  rw [pEnergy_eq hp, pEnergy_eq hp, pEnergy_eq hp]
  have h1 := norm_rpow_combo_le hp.le (W1p0.gradL U) (W1p0.gradL W) ha hb hab
  have h2 := norm_rpow_combo_le hp.le (W1p0.fnL U) (W1p0.fnL W) ha hb hab
  rw [← map_smul, ← map_smul, ← map_add] at h1 h2
  simp only [smul_eq_mul]
  have k1 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 / p by positivity)
  have k2 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ c / p by positivity)
  nlinarith [k1, k2]

/-- The derivative of `pEnergy c` at `u` as a continuous linear functional on `W₀^{1,p}(Ω)`; its
value at `v` is `pForm c u v`. -/
def pOp (hp : 1 < p) (c : ℝ) (U : W1p0 (ENNReal.ofReal p) μ Ω) :
    StrongDual ℝ (W1p0 (ENNReal.ofReal p) μ Ω) :=
  (pairCLM (dualE E) hp (W1p0.gradL U)).comp W1p0.gradL +
    c • (pairCLM (LinearIsometryEquiv.refl ℝ ℝ) hp (W1p0.fnL U)).comp W1p0.fnL

omit [Fact (1 ≤ ENNReal.ofReal p)] in
lemma scalar_pair (f v : ℝ) :
    ‖f‖ ^ (p - 2) * inner ℝ f v = |f| ^ (p - 2) * f * v := by
  rw [Real.norm_eq_abs, mul_assoc]
  congr 1
  simp [mul_comm]

lemma pOp_apply (hp : 1 < p) (c : ℝ) (U V : W1p0 (ENNReal.ofReal p) μ Ω) :
    pOp hp c U V = pForm c U V := by
  simp only [pOp, pForm, add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, pairCLM_apply, smul_eq_mul, LinearIsometryEquiv.coe_refl, id_eq, scalar_pair]

/-- **Gateaux derivative of the energy.** Along the line `u + t v`, `pEnergy c` has derivative
`pForm c u v` at `t = 0` (Evans, §8.1.2, for the Euler-Lagrange computation). -/
theorem pEnergy_gateaux (hp : 1 < p) (c : ℝ) (U V : W1p0 (ENNReal.ofReal p) μ Ω) :
    HasDerivAt (fun t : ℝ => pEnergy c (U + t • V)) (pForm c U V) 0 := by
  have hp0 : 0 < p := by linarith
  have h1 := hasDerivAt_integral_norm_rpow hp (memLp_comp (dualE E) (W1p0.gradL U))
    (memLp_comp (dualE E) (W1p0.gradL V))
  have h2 := hasDerivAt_integral_norm_rpow hp
    (memLp_comp (LinearIsometryEquiv.refl ℝ ℝ) (W1p0.fnL U))
    (memLp_comp (LinearIsometryEquiv.refl ℝ ℝ) (W1p0.fnL V))
  simp only [LinearIsometryEquiv.coe_refl, id_eq] at h2
  have e1 : ∀ t : ℝ, ∫ x, ‖W1p0.gradL (U + t • V) x‖ ^ p ∂(μ.restrict Ω) =
      ∫ x, ‖dualE E (W1p0.gradL U x) + t • dualE E (W1p0.gradL V x)‖ ^ p ∂(μ.restrict Ω) :=
    fun t => by
      rw [map_add, map_smul]
      exact integral_norm_rpow_add_smul (dualE E) _ _ t
  have e2 : ∀ t : ℝ, ∫ x, |W1p0.fnL (U + t • V) x| ^ p ∂(μ.restrict Ω) =
      ∫ x, ‖W1p0.fnL U x + t • W1p0.fnL V x‖ ^ p ∂(μ.restrict Ω) := fun t => by
    simp_rw [← Real.norm_eq_abs]
    rw [map_add, map_smul]
    simpa using integral_norm_rpow_add_smul (LinearIsometryEquiv.refl ℝ ℝ) (W1p0.fnL U)
      (W1p0.fnL V) t
  have key := (h1.const_mul (1 / p)).add (h2.const_mul (c / p))
  have hfun : (fun t : ℝ => pEnergy c (U + t • V)) = fun t : ℝ =>
      1 / p * ∫ x, ‖dualE E (W1p0.gradL U x) + t • dualE E (W1p0.gradL V x)‖ ^ p
        ∂(μ.restrict Ω) + c / p * ∫ x, ‖W1p0.fnL U x + t • W1p0.fnL V x‖ ^ p ∂(μ.restrict Ω) := by
    funext t
    unfold pEnergy
    exact congrArg₂ (· + ·) (congrArg (1 / p * ·) (e1 t)) (congrArg (c / p * ·) (e2 t))
  rw [hfun]
  refine HasDerivAt.congr_deriv key ?_
  rw [← pOp_apply hp c U V]
  simp only [pOp, add_apply, ContinuousLinearMap.comp_apply, smul_apply,
    pairCLM_apply, smul_eq_mul, LinearIsometryEquiv.coe_refl, id_eq,
    LinearIsometryEquiv.norm_map]
  field_simp

omit [FiniteDimensional ℝ E] in
lemma ext_W1p0 {U W : W1p0 (ENNReal.ofReal p) μ Ω} (hf : W1p0.fnL U = W1p0.fnL W)
    (hg : W1p0.gradL U = W1p0.gradL W) : U = W := by
  apply Subtype.ext
  apply WithLp.ofLp_injective
  exact Prod.ext hf hg

omit [FiniteDimensional ℝ E] in
lemma gradL_norm_rpow_le (hp : 1 < p) (U W : W1p0 (ENNReal.ofReal p) μ Ω) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ‖W1p0.gradL (a • U + b • W)‖ ^ p ≤ a * ‖W1p0.gradL U‖ ^ p + b * ‖W1p0.gradL W‖ ^ p := by
  have h := norm_rpow_combo_le hp.le (W1p0.gradL U) (W1p0.gradL W) ha hb hab
  rwa [← map_smul, ← map_smul, ← map_add] at h

omit [FiniteDimensional ℝ E] in
lemma fnL_norm_rpow_le (hp : 1 < p) (U W : W1p0 (ENNReal.ofReal p) μ Ω) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ‖W1p0.fnL (a • U + b • W)‖ ^ p ≤ a * ‖W1p0.fnL U‖ ^ p + b * ‖W1p0.fnL W‖ ^ p := by
  have h := norm_rpow_combo_le hp.le (W1p0.fnL U) (W1p0.fnL W) ha hb hab
  rwa [← map_smul, ← map_smul, ← map_add] at h

lemma gradL_norm_rpow_lt (hp : 1 < p) {U W : W1p0 (ENNReal.ofReal p) μ Ω}
    (hg : W1p0.gradL U ≠ W1p0.gradL W) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    ‖W1p0.gradL (a • U + b • W)‖ ^ p < a * ‖W1p0.gradL U‖ ^ p + b * ‖W1p0.gradL W‖ ^ p := by
  have h := lp_norm_rpow_combo_lt (dualE E) hp hg ha hb hab
  rwa [← map_smul, ← map_smul, ← map_add] at h

omit [FiniteDimensional ℝ E] in
lemma fnL_norm_rpow_lt (hp : 1 < p) {U W : W1p0 (ENNReal.ofReal p) μ Ω}
    (hf : W1p0.fnL U ≠ W1p0.fnL W) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    ‖W1p0.fnL (a • U + b • W)‖ ^ p < a * ‖W1p0.fnL U‖ ^ p + b * ‖W1p0.fnL W‖ ^ p := by
  have h := lp_norm_rpow_combo_lt (LinearIsometryEquiv.refl ℝ ℝ) hp hf ha hb hab
  rwa [← map_smul, ← map_smul, ← map_add] at h

/-- The energy is strictly convex for a positive screening coefficient. -/
theorem pEnergy_strictConvex (hp : 1 < p) {c : ℝ} (hc : 0 < c) :
    StrictConvexOn ℝ Set.univ (pEnergy (p := p) (μ := μ) (Ω := Ω) c) := by
  have hp0 : 0 < p := by linarith
  refine ⟨convex_univ, fun U _ W _ hUW a b ha hb hab => ?_⟩
  rw [pEnergy_eq hp, pEnergy_eq hp, pEnergy_eq hp]
  have h1 := gradL_norm_rpow_le hp U W ha.le hb.le hab
  have h2 := fnL_norm_rpow_le hp U W ha.le hb.le hab
  simp only [smul_eq_mul]
  have k1 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 / p by positivity)
  have k2 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ c / p by positivity)
  by_cases hg : W1p0.gradL U = W1p0.gradL W
  · have hf : W1p0.fnL U ≠ W1p0.fnL W := fun hf => hUW (ext_W1p0 hf hg)
    have k2' := mul_lt_mul_of_pos_left (fnL_norm_rpow_lt hp hf ha hb hab)
      (show 0 < c / p by positivity)
    linarith [k1, k2']
  · have k1' := mul_lt_mul_of_pos_left (gradL_norm_rpow_lt hp hg ha hb hab)
      (show 0 < 1 / p by positivity)
    linarith [k1', k2]

omit [Fact (1 ≤ ENNReal.ofReal p)] in
lemma rpow_sub_two_mul_sq (hp : 0 < p) {y : ℝ} (hy : 0 ≤ y) : y ^ (p - 2) * y ^ 2 = y ^ p := by
  rcases hy.eq_or_lt with h | h
  · rw [← h]
    simp [Real.zero_rpow hp.ne']
  · rw [← Real.rpow_natCast, ← Real.rpow_add h]
    congr 1
    push_cast
    ring

omit [FiniteDimensional ℝ E] in
/-- The exponent `p` of the norm of an element of `W₀^{1,p}` splits over the parts. -/
lemma norm_rpow_eq_parts (hp : 1 < p) (U : W1p0 (ENNReal.ofReal p) μ Ω) :
    ‖U‖ ^ p = ‖W1p0.fnL U‖ ^ p + ‖W1p0.gradL U‖ ^ p := by
  have hp0 : 0 < p := by linarith
  have h := WithLp.prod_norm_eq_add (p := ENNReal.ofReal p)
    (by rw [ofReal_toReal_aux hp]; exact hp0) (U : W1pGraph (ENNReal.ofReal p) μ Ω)
  rw [ofReal_toReal_aux hp] at h
  have e : ‖U‖ = ‖(U : W1pGraph (ENNReal.ofReal p) μ Ω)‖ := rfl
  rw [e, h, ← Real.rpow_mul (by positivity), one_div_mul_cancel hp0.ne', Real.rpow_one]
  rfl

lemma pOp_self (hp : 1 < p) (c : ℝ) (U : W1p0 (ENNReal.ofReal p) μ Ω) :
    pOp hp c U U = ‖W1p0.gradL U‖ ^ p + c * ‖W1p0.fnL U‖ ^ p := by
  have hp0 : 0 < p := by linarith
  rw [pOp_apply, pForm]
  congr 1
  · rw [← integral_norm_rpow_eq hp (W1p0.gradL U)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map]
    exact rpow_sub_two_mul_sq hp0 (norm_nonneg _)
  · congr 1
    have : ∫ x, |W1p0.fnL U x| ^ p ∂(μ.restrict Ω) = ‖W1p0.fnL U‖ ^ p := by
      simp_rw [← Real.norm_eq_abs]
      exact integral_norm_rpow_eq hp _
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [mul_assoc, ← sq, ← sq_abs]
    exact rpow_sub_two_mul_sq hp0 (abs_nonneg _)

lemma pOp_zero (hp : 1 < p) (c : ℝ) :
    pOp hp c (0 : W1p0 (ENNReal.ofReal p) μ Ω) = 0 := by
  ext V
  rw [pOp_apply, pForm]
  have hg : ∀ᵐ x ∂(μ.restrict Ω), W1p0.gradL (0 : W1p0 (ENNReal.ofReal p) μ Ω) x = 0 := by
    rw [map_zero]
    exact Lp.coeFn_zero _ _ _
  have hf : ∀ᵐ x ∂(μ.restrict Ω), W1p0.fnL (0 : W1p0 (ENNReal.ofReal p) μ Ω) x = 0 := by
    rw [map_zero]
    exact Lp.coeFn_zero _ _ _
  have h1 : ∫ x, ‖W1p0.gradL (0 : W1p0 (ENNReal.ofReal p) μ Ω) x‖ ^ (p - 2) *
      inner ℝ (dualE E (W1p0.gradL (0 : W1p0 (ENNReal.ofReal p) μ Ω) x))
        (dualE E (W1p0.gradL V x)) ∂(μ.restrict Ω) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hg] with x hx
    rw [hx]
    simp
  have h2 : ∫ x, |W1p0.fnL (0 : W1p0 (ENNReal.ofReal p) μ Ω) x| ^ (p - 2) *
      W1p0.fnL (0 : W1p0 (ENNReal.ofReal p) μ Ω) x * W1p0.fnL V x ∂(μ.restrict Ω) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hf] with x hx
    rw [hx]
    simp
  rw [h1, h2]
  simp

/-- The operator `pOp` is coercive for a positive screening coefficient: `⟨A v, v⟩` is bounded
below by `min 1 c · ‖v‖^p`, and `p > 1`. -/
theorem isCoerciveOp_pOp (hp : 1 < p) {c : ℝ} (hc : 0 < c) :
    IsCoerciveOp Set.univ (pOp (p := p) (μ := μ) (Ω := Ω) hp c) := by
  have hp0 : 0 < p := by linarith
  refine ⟨0, Set.mem_univ _, ?_⟩
  simp only [pOp_zero, sub_zero]
  rw [principal_univ, inf_top_eq]
  set m : ℝ := min 1 c with hm
  have hm0 : 0 < m := lt_min one_pos hc
  have hlim : Tendsto (fun v : W1p0 (ENNReal.ofReal p) μ Ω => m * ‖v‖ ^ (p - 1))
      (Bornology.cobounded _) atTop :=
    ((tendsto_rpow_atTop (by linarith : 0 < p - 1)).comp
      tendsto_norm_cobounded_atTop).const_mul_atTop hm0
  refine tendsto_atTop_mono' _ ?_ hlim
  filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with v hv
  rw [le_div_iff₀ hv, pOp_self]
  have e : ‖v‖ ^ (p - 1) * ‖v‖ = ‖v‖ ^ p := by
    rw [← Real.rpow_add_one hv.ne']
    congr 1
    ring
  have hn := norm_rpow_eq_parts hp v
  have a1 : 0 ≤ ‖W1p0.fnL v‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
  have a2 : 0 ≤ ‖W1p0.gradL v‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
  have m1 : m ≤ 1 := min_le_left _ _
  have m2 : m ≤ c := min_le_right _ _
  calc m * ‖v‖ ^ (p - 1) * ‖v‖ = m * (‖W1p0.fnL v‖ ^ p + ‖W1p0.gradL v‖ ^ p) := by
        rw [mul_assoc, e, hn]
    _ ≤ ‖W1p0.gradL v‖ ^ p + c * ‖W1p0.fnL v‖ ^ p := by
      have q1 := mul_nonneg a1 (sub_nonneg.2 m2)
      have q2 := mul_nonneg a2 (sub_nonneg.2 m1)
      nlinarith [q1, q2]

theorem hasDerivAt_pOp (hp : 1 < p) (c : ℝ) (U V : W1p0 (ENNReal.ofReal p) μ Ω) :
    HasDerivAt (fun t : ℝ => pEnergy c (U + t • V)) (pOp hp c U V) 0 := by
  rw [pOp_apply]
  exact pEnergy_gateaux hp c U V

/-- **Existence for the screened `p`-Laplacian.** Let `E` be a finite-dimensional real
inner-product space with an additive Haar measure `μ`, `Ω` a set of finite measure, `1 < p < ∞`
and `0 < c`. For every `f` in the dual of `W₀^{1,p}(Ω)` there is `u` with
`∫ ‖∇u‖^{p-2} ⟪∇u, ∇v⟫ + c ∫ |u|^{p-2} u v = f v` for all `v`, where `∇u` is the gradient part
of `u` read in `E` through the Riesz isometry `dualE` (this is the pairing `∇u(∇v)`). The
energy `pEnergy` is a convex, continuous, coercive potential of this operator on the reflexive
space `W₀^{1,p}(Ω)`, so the direct method applies (Evans, §8.1.2 for `p = 2`; Brezis,
Corollary 3.23, p. 71 for the direct method). The screening coefficient `c = 0` would need a
`p`-Poincaré inequality on `W₀^{1,p}` for coercivity, which the library does not yet have. The
inner-product structure on `E` is needed because `‖·‖^p` on `E*` is differentiable only when
the norm is smooth. -/
theorem exists_weakSolution_pLaplacian (hΩ : μ Ω ≠ ∞) (hp : 1 < p) {c : ℝ} (hc : 0 < c)
    (f : StrongDual ℝ (W1p0 (ENNReal.ofReal p) μ Ω)) :
    ∃ u : W1p0 (ENNReal.ofReal p) μ Ω, ∀ v : W1p0 (ENNReal.ofReal p) μ Ω,
      pForm c u v = f v := by
  have hX := isReflexive_W1p0 (p := ENNReal.ofReal p) (μ := μ) (Ω := Ω) hΩ
    (ENNReal.one_lt_ofReal.2 hp) ENNReal.ofReal_ne_top
  obtain ⟨u, hu⟩ := exists_eq_of_potential hX (pEnergy_convex hp hc.le)
    (pEnergy_continuous hp c).lowerSemicontinuous (hasDerivAt_pOp hp c)
    (isCoerciveOp_pOp hp hc) f
  exact ⟨u, fun v => by rw [← pOp_apply hp c u v, hu]⟩

/-- **Uniqueness for the screened `p`-Laplacian.** The weak solution of
`exists_weakSolution_pLaplacian` is unique. The energy is strictly convex for `c > 0` and
`p > 1`, since `‖·‖^p` is strictly convex pointwise and the graph norm sees both parts, so its
derivative is strictly monotone. -/
theorem existsUnique_weakSolution_pLaplacian (hΩ : μ Ω ≠ ∞) (hp : 1 < p) {c : ℝ} (hc : 0 < c)
    (f : StrongDual ℝ (W1p0 (ENNReal.ofReal p) μ Ω)) :
    ∃! u : W1p0 (ENNReal.ofReal p) μ Ω, ∀ v : W1p0 (ENNReal.ofReal p) μ Ω,
      pForm c u v = f v := by
  have hX := isReflexive_W1p0 (p := ENNReal.ofReal p) (μ := μ) (Ω := Ω) hΩ
    (ENNReal.one_lt_ofReal.2 hp) ENNReal.ofReal_ne_top
  obtain ⟨u, hu, huniq⟩ := existsUnique_eq_of_potential hX (pEnergy_convex hp hc.le)
    (pEnergy_continuous hp c).lowerSemicontinuous (hasDerivAt_pOp hp c)
    (isCoerciveOp_pOp hp hc)
    (isStrictlyMonotoneOp_of_strictConvex_gateaux (pEnergy_strictConvex hp hc)
      (hasDerivAt_pOp hp c)) f
  refine ⟨u, fun v => by rw [← pOp_apply hp c u v, hu], fun w hw => huniq w ?_⟩
  ext v
  rw [pOp_apply]
  exact hw v

end Main

end EllipticPdes
