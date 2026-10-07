/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.Convolution
public import EllipticPdes.Sobolev.WeakDerivClassical

/-!
# Chain rule for weak Fréchet derivatives

On a finite-dimensional real normed space `E` with an additive Haar measure `μ`, a `C¹`
function `f : ℝ → ℝ` with bounded derivative, composed with a function `u` that has a weak
Fréchet derivative `G` on an open set `Ω`, has the weak Fréchet derivative `f'(u) G` there.

The proof mollifies `u` and `G` inside a compact neighbourhood of the support of the test
function. For each mollification the classical chain rule and integration by parts apply, and
both sides pass to the limit: the function side through the Lipschitz bound on `f` and `L¹`
convergence, the derivative side through an almost everywhere convergent subsequence and
dominated convergence for the continuous, bounded `f'`.

## Main declarations

* `EllipticPdes.HasWeakFDerivOn.comp_contDiff`: the chain rule.
* `EllipticPdes.integral_comp_mul_fderiv_eq_neg`: the chain rule identity for compactly
  supported integrable data whose mollifications satisfy the classical identity.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology TopologicalSpace
open scoped NNReal ENNReal Convolution

noncomputable section

namespace EllipticPdes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Product of two bounded factors and an integrable one.** -/
theorem integrable_bdd_mul_mul_bdd {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {a b c : α → ℝ} (ha : AEStronglyMeasurable a μ) {A : ℝ} (hA : ∀ x, ‖a x‖ ≤ A)
    (hb : Integrable b μ) (hc : AEStronglyMeasurable c μ) {C : ℝ}
    (hC : ∀ x, ‖c x‖ ≤ C) : Integrable (fun x => a x * b x * c x) μ := by
  refine Integrable.mono' (hb.norm.const_mul (A * C)) ((ha.mul hb.1).mul hc) ?_
  filter_upwards with x
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA x)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC x)
  rw [norm_mul, norm_mul]
  calc ‖a x‖ * ‖b x‖ * ‖c x‖ ≤ A * ‖b x‖ * C := by gcongr <;> apply_assumption
    _ = A * C * ‖b x‖ := by ring

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **A Lipschitz function of an integrable function against a test factor.** The product with
a continuous compactly supported factor is integrable. -/
theorem integrable_comp_mul_of_lipschitz {w : E → ℝ} (hw : Integrable w μ) {f : ℝ → ℝ} {M : ℝ≥0}
    (hf : LipschitzWith M f) {h : E → ℝ} (hc : Continuous h) (hcs : HasCompactSupport h) :
    Integrable (fun x => f (w x) * h x) μ := by
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
  have hint1 : Integrable (fun x => ‖h x‖ * ‖w x‖) μ :=
    hw.norm.bdd_mul hc.norm.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [norm_norm]; exact hC x)
  refine Integrable.mono' ((hint1.const_mul (M : ℝ)).add
    ((hc.norm.integrable_of_hasCompactSupport hcs.norm).const_mul |f 0|))
    ((hf.continuous.comp_aestronglyMeasurable hw.1).mul hc.aestronglyMeasurable) ?_
  filter_upwards with x
  have h2 : |f (w x)| ≤ (M : ℝ) * |w x| + |f 0| := by
    have := hf.dist_le_mul (w x) 0
    simp only [Real.dist_eq, sub_zero] at this
    linarith [abs_sub_abs_le_abs_sub (f (w x)) (f 0)]
  simp only [Pi.add_apply, norm_mul, Real.norm_eq_abs]
  calc |f (w x)| * |h x| ≤ ((M : ℝ) * |w x| + |f 0|) * |h x| := by gcongr
    _ = (M : ℝ) * (|h x| * |w x|) + |f 0| * |h x| := by ring

/-- **The classical chain rule against a test function.** For `f` and `v` of class `C¹` and a
smooth compactly supported `φ`, integration by parts gives
`∫ f(v) ∂_wφ = -∫ f'(v) ∂_w v φ`. -/
theorem integral_comp_mul_fderiv_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {v φ : E → ℝ}
    (hv : ContDiff ℝ 1 v) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcs : HasCompactSupport φ) (w : E) :
    ∫ x, f (v x) * fderiv ℝ φ x w ∂μ = -∫ x, deriv f (v x) * fderiv ℝ v x w * φ x ∂μ := by
  have hfv : ContDiff ℝ 1 (f ∘ v) := hf.comp hv
  have hpc : Continuous (fun x => fderiv ℝ φ x w) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpcs : HasCompactSupport (fun x => fderiv ℝ φ x w) := hφcs.fderiv_apply (𝕜 := ℝ) w
  have hfderiv : ∀ x, fderiv ℝ (f ∘ v) x w = deriv f (v x) * fderiv ℝ v x w := fun x => by
    have h := ((hf.differentiable one_ne_zero) (v x)).hasDerivAt.comp_hasFDerivAt x
      (hv.differentiable one_ne_zero x).hasFDerivAt
    rw [h.fderiv, _root_.smul_apply, smul_eq_mul]
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ)
    (f := f ∘ v) (g := φ) (v := w)
    (((hfv.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
      hφ.continuous |>.integrable_of_hasCompactSupport hφcs.mul_left)
    ((hfv.continuous.mul hpc).integrable_of_hasCompactSupport hpcs.mul_left)
    ((hfv.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφcs.mul_left)
    (fun x _ => (hfv.differentiable one_ne_zero) x) (fun x _ => (hφ.differentiable (by simp)) x)
  simpa [hfderiv] using key

/-- **The function side of the chain rule.** If `f` is `M`-Lipschitz, `ψ` is bounded and
`vₙ → U` in `L¹`, then `∫ f(vₙ) ψ → ∫ f(U) ψ`. -/
theorem tendsto_integral_comp_mul {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : ℝ → ℝ} {M : ℝ≥0} (hf : LipschitzWith M f) {ψ : α → ℝ} {C : ℝ} (hψ : ∀ x, ‖ψ x‖ ≤ C)
    {v : ℕ → α → ℝ} {U : α → ℝ} (hv : ∀ n, Integrable (v n) μ) (hU : Integrable U μ)
    (hint : ∀ n, Integrable (fun x => f (v n x) * ψ x) μ)
    (hintU : Integrable (fun x => f (U x) * ψ x) μ)
    (hconv : Tendsto (fun n => eLpNorm (v n - U) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f (v n x) * ψ x ∂μ) atTop (𝓝 (∫ x, f (U x) * ψ x ∂μ)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have hto : Tendsto (fun n => (M : ℝ) * C * (eLpNorm (v n - U) 1 μ).toReal) atTop (𝓝 0) := by
    simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv).const_mul
      ((M : ℝ) * C)
  refine squeeze_zero_norm (fun n => ?_) hto
  rw [← integral_sub (hint n) hintU]
  have hbd : Integrable (fun x => (M : ℝ) * C * ‖(v n - U) x‖) μ :=
    ((hv n).sub hU).norm.const_mul _
  refine (norm_integral_le_of_norm_le hbd (Eventually.of_forall fun x => ?_)).trans_eq ?_
  · rw [Pi.sub_apply, ← sub_mul, norm_mul]
    have h1 : ‖f (v n x) - f (U x)‖ ≤ (M : ℝ) * ‖v n x - U x‖ := by
      simpa [dist_eq_norm] using hf.dist_le_mul (v n x) (U x)
    calc ‖f (v n x) - f (U x)‖ * ‖ψ x‖ ≤ ((M : ℝ) * ‖v n x - U x‖) * C := by gcongr; exact hψ x
      _ = (M : ℝ) * C * ‖v n x - U x‖ := by ring
  · have hm : AEStronglyMeasurable (v n - U) μ := ((hv n).sub hU).aestronglyMeasurable
    rw [integral_const_mul, integral_norm_eq_lintegral_enorm hm, eLpNorm_one_eq_lintegral_enorm hm]

/-- **The gradient side of the chain rule.** If `f'` is continuous and bounded by `M`, `ψ` is
bounded, `vₙ → U` almost everywhere and `wₙ → G` in `L¹`, then
`∫ f'(vₙ) wₙ ψ → ∫ f'(U) G ψ`. -/
theorem tendsto_integral_deriv_comp_mul {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : ℝ → ℝ} {M : ℝ≥0} (hfc : Continuous (deriv f)) (hM : ∀ t, ‖deriv f t‖ ≤ M)
    {ψ : α → ℝ} {C : ℝ} (hψm : AEStronglyMeasurable ψ μ) (hψ : ∀ x, ‖ψ x‖ ≤ C)
    {v : ℕ → α → ℝ} {U : α → ℝ} (hvm : ∀ n, AEStronglyMeasurable (v n) μ)
    {w : ℕ → α → ℝ} {G : α → ℝ} (hw : ∀ n, Integrable (w n) μ) (hG : Integrable G μ)
    (hconv : Tendsto (fun n => eLpNorm (w n - G) 1 μ) atTop (𝓝 0))
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => v n x) atTop (𝓝 (U x))) :
    Tendsto (fun n => ∫ x, deriv f (v n x) * w n x * ψ x ∂μ) atTop
      (𝓝 (∫ x, deriv f (U x) * G x * ψ x ∂μ)) := by
  have hA : ∀ n, Integrable (fun x => deriv f (v n x) * (w n x - G x) * ψ x) μ := fun n =>
    integrable_bdd_mul_mul_bdd (hfc.comp_aestronglyMeasurable (hvm n)) (fun x => hM _)
      ((hw n).sub hG) hψm hψ
  have hB : ∀ n, Integrable (fun x => deriv f (v n x) * G x * ψ x) μ := fun n =>
    integrable_bdd_mul_mul_bdd (hfc.comp_aestronglyMeasurable (hvm n)) (fun x => hM _) hG hψm hψ
  have hsplit : ∀ n, ∫ x, deriv f (v n x) * w n x * ψ x ∂μ
      = (∫ x, deriv f (v n x) * (w n x - G x) * ψ x ∂μ)
        + ∫ x, deriv f (v n x) * G x * ψ x ∂μ := fun n => by
    rw [← integral_add (hA n) (hB n)]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hpiece1 : Tendsto (fun n => ∫ x, deriv f (v n x) * (w n x - G x) * ψ x ∂μ) atTop (𝓝 0) := by
    have hto : Tendsto (fun n => (M : ℝ) * C * (eLpNorm (w n - G) 1 μ).toReal) atTop (𝓝 0) := by
      simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv).const_mul
        ((M : ℝ) * C)
    refine squeeze_zero_norm (fun n => ?_) hto
    have hbd : Integrable (fun x => (M : ℝ) * C * ‖(w n - G) x‖) μ :=
      ((hw n).sub hG).norm.const_mul _
    refine (norm_integral_le_of_norm_le hbd (Eventually.of_forall fun x => ?_)).trans_eq ?_
    · rw [Pi.sub_apply, norm_mul, norm_mul]
      calc ‖deriv f (v n x)‖ * ‖w n x - G x‖ * ‖ψ x‖ ≤ (M : ℝ) * ‖w n x - G x‖ * C := by
            gcongr
            · exact hM _
            · exact hψ x
        _ = (M : ℝ) * C * ‖w n x - G x‖ := by ring
    · have hm : AEStronglyMeasurable (w n - G) μ := ((hw n).sub hG).aestronglyMeasurable
      rw [integral_const_mul, integral_norm_eq_lintegral_enorm hm,
        eLpNorm_one_eq_lintegral_enorm hm]
  have hpiece2 : Tendsto (fun n => ∫ x, deriv f (v n x) * G x * ψ x ∂μ) atTop
      (𝓝 (∫ x, deriv f (U x) * G x * ψ x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => (M : ℝ) * C * ‖G x‖)
      (fun n => (hB n).1) (hG.norm.const_mul _) (fun n => Eventually.of_forall fun x => ?_) ?_
    · rw [norm_mul, norm_mul]
      calc ‖deriv f (v n x)‖ * ‖G x‖ * ‖ψ x‖ ≤ (M : ℝ) * ‖G x‖ * C := by
            gcongr
            · exact hM _
            · exact hψ x
        _ = (M : ℝ) * C * ‖G x‖ := by ring
    · filter_upwards [hae] with x hx
      exact (((hfc.tendsto (U x)).comp hx).mul_const (G x)).mul_const (ψ x)
  simpa [hsplit] using hpiece1.add hpiece2

/-- **The mollifications of an integrable function converge in `L¹`.** -/
theorem tendsto_eLpNorm_one_mollifier_sub {δ : ℝ} (hδ : 0 < δ) {h : E → ℝ}
    (hh : Integrable h μ) :
    Tendsto (fun n => eLpNorm ((mollifier hδ n : ContDiffBump (0 : E)).normed μ
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h - h) 1 μ) atTop (𝓝 0) := by
  simpa using Embedding.tendsto_eLpNorm_normed_convolution_sub le_rfl ENNReal.one_ne_top
    (memLp_one_iff_integrable.2 hh) (tendsto_rOut_mollifier (E := E) hδ)

/-- **The chain rule identity for compactly supported integrable data.** Let `U` and `g` be
integrable with compact support, `f` of class `C¹` with bounded derivative, `φ` a test function,
and suppose that on the support of `φ` the derivative along `w` of every standard mollification
of `U` is the mollification of `g`. Then `∫ f(U) ∂_wφ = -∫ f'(U) g φ`. -/
theorem integral_comp_mul_fderiv_eq_neg {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ≥0}
    (hM : ∀ t, ‖deriv f t‖₊ ≤ M) {U g φ : E → ℝ} (w : E) (hUint : Integrable U μ)
    (hUcs : HasCompactSupport U) (hgint : Integrable g μ) (hgcs : HasCompactSupport g)
    (hφc : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcs : HasCompactSupport φ) {δ : ℝ} (hδ : 0 < δ)
    (hpartial : ∀ n x, fderiv ℝ ((mollifier hδ n : ContDiffBump (0 : E)).normed μ
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U) x w * φ x
      = ((mollifier hδ n : ContDiffBump (0 : E)).normed μ
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) x * φ x) :
    ∫ x, f (U x) * fderiv ℝ φ x w ∂μ = -∫ x, deriv f (U x) * g x * φ x ∂μ := by
  set ρ : ℕ → ContDiffBump (0 : E) := mollifier hδ with hρ
  set v : ℕ → E → ℝ := fun n => (ρ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U
  set w' : ℕ → E → ℝ := fun n => (ρ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g
  have hfl : LipschitzWith M f :=
    lipschitzWith_of_nnnorm_deriv_le (hf.differentiable one_ne_zero) hM
  have hMr : ∀ t, ‖deriv f t‖ ≤ (M : ℝ) := fun t => by exact_mod_cast hM t
  have hpc : Continuous (fun x => fderiv ℝ φ x w) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpcs : HasCompactSupport (fun x => fderiv ℝ φ x w) := hφcs.fderiv_apply (𝕜 := ℝ) w
  obtain ⟨Cφ, hCφ⟩ := hφcs.exists_bound_of_continuous hφc.continuous
  obtain ⟨Cp, hCp⟩ := hpcs.exists_bound_of_continuous hpc
  have hvsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n) := fun n =>
    contDiff_normed_convolution (ρ n) hUint.locallyIntegrable
  have hwint : ∀ n, Integrable (w' n) μ := fun n =>
    (contDiff_normed_convolution (ρ n) hgint.locallyIntegrable
      ).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_normed_convolution (ρ n) hgcs)
  have hvint : ∀ n, Integrable (v n) μ := fun n =>
    (hvsmooth n).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_normed_convolution (ρ n) hUcs)
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    (tendsto_eLpNorm_one_mollifier_sub hδ hUint)).exists_seq_tendsto_ae
  have hclassical : ∀ n, ∫ x, f (v n x) * fderiv ℝ φ x w ∂μ
      = -∫ x, deriv f (v n x) * w' n x * φ x ∂μ := fun n => by
    rw [integral_comp_mul_fderiv_eq hf ((hvsmooth n).of_le (WithTop.coe_le_coe.mpr le_top))
      hφc hφcs w]
    exact congrArg Neg.neg (integral_congr_ae (Eventually.of_forall fun x => by
      dsimp only; rw [mul_assoc, hpartial n x, ← mul_assoc]))
  have hlimL := (tendsto_integral_comp_mul hfl hCp hvint hUint (fun n =>
    ((hfl.continuous.comp (hvsmooth n).continuous).mul hpc).integrable_of_hasCompactSupport
      hpcs.mul_left) (integrable_comp_mul_of_lipschitz hUint hfl hpc hpcs)
    (tendsto_eLpNorm_one_mollifier_sub hδ hUint)).comp hns.tendsto_atTop
  have hlimR := (tendsto_integral_deriv_comp_mul hf.continuous_deriv_one hMr
    hφc.continuous.aestronglyMeasurable hCφ
    (fun n => (hvsmooth (ns n)).continuous.aestronglyMeasurable) (fun n => hwint (ns n)) hgint
    ((tendsto_eLpNorm_one_mollifier_sub hδ hgint).comp hns.tendsto_atTop) hae).neg
  exact tendsto_nhds_unique hlimL (hlimR.congr fun i => (hclassical (ns i)).symm)

/-- **Evaluation commutes with mollification.** The mollification of an operator-valued locally
integrable function, evaluated at a vector `w`, is the mollification of the function evaluated
at `w`. -/
theorem convolution_normed_apply (ρ : ContDiffBump (0 : E)) {g : E → E →L[ℝ] ℝ}
    (hg : LocallyIntegrable g μ) (x w : E) :
    (ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) x w
      = (ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] fun y => g y w) x := by
  have hex := ρ.hasCompactSupport_normed.convolutionExists_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (ρ.continuous_normed (μ := μ)) hg x
  rw [convolution_def, convolution_def, ContinuousLinearMap.integral_apply hex]
  simp

variable {Ω : Opens E}

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- **Local integrability by domination.** -/
theorem locallyIntegrableOn_of_norm_le {f g : E → ℝ} (hg : LocallyIntegrableOn g Ω μ)
    (hf : AEStronglyMeasurable f (μ.restrict Ω)) (h : ∀ x, ‖f x‖ ≤ ‖g x‖) :
    LocallyIntegrableOn f Ω μ :=
  (locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed).mpr fun _ hK hKc =>
    (hg.integrableOn_compact_subset hK hKc).norm.mono'
      (hf.mono_measure (Measure.restrict_mono hK le_rfl)) (Eventually.of_forall h)

/-- **Chain rule for weak Fréchet derivatives.** A `C¹` function `f : ℝ → ℝ` with bounded
derivative, composed with a function `u` that has the weak Fréchet derivative `G` on the open
set `Ω`, has the weak Fréchet derivative `x ↦ f'(u x) G x` there. -/
theorem HasWeakFDerivOn.comp_contDiff {u : E → ℝ} {G : E → E →L[ℝ] ℝ}
    (hw : HasWeakFDerivOn Ω u G μ) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ≥0}
    (hM : ∀ t, ‖deriv f t‖₊ ≤ M) :
    HasWeakFDerivOn Ω (fun x => f (u x)) (fun x => deriv f (u x) • G x) μ := by
  intro w
  have hfl : LipschitzWith M f :=
    lipschitzWith_of_nnnorm_deriv_le (hf.differentiable one_ne_zero) hM
  have hu : LocallyIntegrableOn u Ω μ := (hw 0).locallyIntegrableOn_fun
  have hGw : LocallyIntegrableOn (fun x => G x w) Ω μ := (hw w).locallyIntegrableOn
  have hum : AEStronglyMeasurable u (μ.restrict Ω) := hu.aestronglyMeasurable
  refine hasWeakLineDerivOn_iff.2 ⟨?_, ?_, fun φ hφ hφcs hφΩ => ?_⟩
  · refine locallyIntegrableOn_of_norm_le (g := fun x => |f 0| + M * ‖u x‖)
      ((locallyIntegrableOn_const _).add (hu.norm.smul (M : ℝ)))
      (hf.continuous.comp_aestronglyMeasurable hum) fun x => ?_
    have := hfl.dist_le_mul (u x) 0
    simp only [Real.dist_eq, sub_zero] at this
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity : 0 ≤ |f 0| + M * |u x|)]
    linarith [abs_sub_abs_le_abs_sub (f (u x)) (f 0)]
  · refine locallyIntegrableOn_of_norm_le (g := fun x => (M : ℝ) * G x w)
      (hGw.smul (M : ℝ)) ((hf.continuous_deriv_one.comp_aestronglyMeasurable hum).mul
        hGw.aestronglyMeasurable) fun x => ?_
    change ‖deriv f (u x) * G x w‖ ≤ ‖(M : ℝ) * G x w‖
    rw [norm_mul, norm_mul, NNReal.norm_eq]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hM (u x)) (norm_nonneg _)
  · obtain ⟨δ, hδ, hK'⟩ := IsCompact.exists_cthickening_subset_open hφcs Ω.isOpen hφΩ
    set K' := cthickening δ (tsupport φ) with hK'def
    have hK'c : IsCompact K' := hφcs.cthickening
    have hK'm : MeasurableSet K' := hK'c.isClosed.measurableSet
    have huK : IntegrableOn u K' μ := hu.integrableOn_compact_subset hK' hK'c
    have hGK : IntegrableOn G K' μ := hw.locallyIntegrableOn.integrableOn_compact_subset hK' hK'c
    have hgK : IntegrableOn (fun x => G x w) K' μ := hGw.integrableOn_compact_subset hK' hK'c
    have hcs : ∀ h : E → ℝ, HasCompactSupport (K'.indicator h) := fun h =>
      hK'c.of_isClosed_subset isClosed_closure
        (closure_minimal support_indicator_subset hK'c.isClosed)
    have hpartial : ∀ n x, fderiv ℝ ((mollifier hδ n : ContDiffBump (0 : E)).normed μ
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] K'.indicator u) x w * φ x
        = ((mollifier hδ n : ContDiffBump (0 : E)).normed μ
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] K'.indicator fun y => G y w) x * φ x :=
      fun n x => by
      by_cases hx : x ∈ tsupport φ
      · have hfd := hw.hasFDerivAt_convolution hK'm hK' huK hGK (mollifier hδ n) (y := x)
          ((closedBall_subset_closedBall (rOut_mollifier_le hδ n)).trans
            (closedBall_subset_cthickening hx δ))
        rw [hfd.fderiv, convolution_normed_apply _
          (IntegrableOn.integrable_indicator (ε' := E →L[ℝ] ℝ) hGK hK'm).locallyIntegrable]
        congr 2
        funext y
        by_cases hy : y ∈ K' <;> simp [indicator, hy]
      · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]
    have hwhole := integral_comp_mul_fderiv_eq_neg hf hM w
      ((integrable_indicator_iff hK'm).mpr huK) (hcs u)
      ((integrable_indicator_iff hK'm).mpr hgK) (hcs _) hφ hφcs hδ hpartial
    have hzero : ∀ x ∉ K', fderiv ℝ φ x w = 0 ∧ φ x = 0 := fun x hx =>
      ⟨image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ φ x w) fun hc =>
        hx (self_subset_cthickening _ (tsupport_fderiv_apply_subset ℝ w hc)),
        image_eq_zero_of_notMem_tsupport fun hc => hx (self_subset_cthickening _ hc)⟩
    change ∫ x, (fderiv ℝ φ x) w * f (u x) ∂μ = -∫ x, φ x * (deriv f (u x) * (G x) w) ∂μ
    have e1 : ∀ x, (fderiv ℝ φ x) w * f (u x)
        = f (K'.indicator u x) * (fderiv ℝ φ x) w := fun x => by
      by_cases hx : x ∈ K'
      · rw [indicator_of_mem hx, mul_comm]
      · rw [(hzero x hx).1]; simp
    have e2 : ∀ x, φ x * (deriv f (u x) * (G x) w)
        = deriv f (K'.indicator u x) * K'.indicator (fun x => (G x) w) x * φ x := fun x => by
      by_cases hx : x ∈ K'
      · rw [indicator_of_mem hx, indicator_of_mem hx, mul_comm]
      · rw [(hzero x hx).2]; simp
    simp only [e1, e2]
    exact hwhole

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

/-- **Measurability of a truncation.** -/
theorem aestronglyMeasurable_ite_lt {α : Type*} {m : MeasurableSpace α} {ν : Measure α}
    {u w : α → ℝ} (hu : AEStronglyMeasurable u ν) (hw : AEStronglyMeasurable w ν) (c : ℝ) :
    AEStronglyMeasurable (fun x => if c < u x then w x else 0) ν := by
  refine ⟨fun x => if c < hu.mk u x then hw.mk w x else 0, ?_, ?_⟩
  · exact StronglyMeasurable.ite
      (measurableSet_lt measurable_const hu.stronglyMeasurable_mk.measurable)
      hw.stronglyMeasurable_mk stronglyMeasurable_const
  · filter_upwards [hu.ae_eq_mk, hw.ae_eq_mk] with x h1 h2
    simp only [h1, h2]

/-- **Weak derivative of the positive part** (Gilbarg and Trudinger Lemma 7.6, Evans §5.10
Problem 18). On an open set, `u⁺ = max u 0` has the weak Fréchet derivative `G` where `u > 0`
and `0` elsewhere. -/
theorem HasWeakFDerivOn.posPart {u : E → ℝ} {G : E → E →L[ℝ] ℝ} (hw : HasWeakFDerivOn Ω u G μ) :
    HasWeakFDerivOn Ω (fun x => max (u x) 0) (fun x => if 0 < u x then G x else 0) μ := by
  intro w
  have hu : LocallyIntegrableOn u Ω μ := (hw 0).locallyIntegrableOn_fun
  have hGw : LocallyIntegrableOn (fun x => G x w) Ω μ := (hw w).locallyIntegrableOn
  have hum : AEStronglyMeasurable u (μ.restrict Ω) := hu.aestronglyMeasurable
  have hite : (fun x => (if 0 < u x then G x else 0) w) = fun x => if 0 < u x then G x w else 0 :=
    funext fun x => by split_ifs <;> simp
  have hind : LocallyIntegrableOn (fun x => if 0 < u x then G x w else 0) Ω μ :=
    locallyIntegrableOn_of_norm_le hGw (aestronglyMeasurable_ite_lt hum hGw.aestronglyMeasurable 0)
      fun x => by split_ifs <;> simp
  refine hasWeakLineDerivOn_iff.2 ⟨?_, hite ▸ hind, fun φ hφ hφcs hφΩ => ?_⟩
  · refine locallyIntegrableOn_of_norm_le hu.norm
      ((continuous_id.max continuous_const).comp_aestronglyMeasurable hum) fun x => ?_
    simp only [Real.norm_eq_abs, abs_abs]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  set ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ) with hεdef
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hpc : Continuous (fun x => fderiv ℝ φ x w) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpcs : HasCompactSupport (fun x => fderiv ℝ φ x w) := hφcs.fderiv_apply (𝕜 := ℝ) w
  have hps : tsupport (fun x => fderiv ℝ φ x w) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ w).trans hφΩ
  have hset : ∀ F : E → ℝ, (∀ x ∉ (Ω : Set E), F x = 0) → ∫ x, F x ∂μ = ∫ x in Ω, F x ∂μ :=
    fun F hF => (setIntegral_eq_integral_of_forall_compl_eq_zero hF).symm
  have hz1 : ∀ x ∉ (Ω : Set E), fderiv ℝ φ x w = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ φ x w) fun hc => hx (hps hc)
  have hz2 : ∀ x ∉ (Ω : Set E), φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hc => hx (hφΩ hc)
  have hn : ∀ n, ∫ x in Ω, fderiv ℝ φ x w • posPartApprox (ε n) (u x) ∂μ
      = -∫ x in Ω, φ x • (deriv (posPartApprox (ε n)) (u x) * G x w) ∂μ := fun n => by
    have := ((hw.comp_contDiff (contDiff_posPartApprox (hεpos n).ne') (M := 1)
      (nnnorm_deriv_posPartApprox_le (hεpos n).ne')) w).integral_eq hφ hφcs hφΩ
    rwa [hset _ fun x hx => by simp [hz1 x hx], hset _ fun x hx => by simp [hz2 x hx]] at this
  have hL : Tendsto (fun n => ∫ x in Ω, fderiv ℝ φ x w • posPartApprox (ε n) (u x) ∂μ) atTop
      (𝓝 (∫ x in Ω, fderiv ℝ φ x w • max (u x) 0 ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖fderiv ℝ φ x w • u x‖)
      (fun n => hpc.aestronglyMeasurable.smul
        ((contDiff_posPartApprox (hεpos n).ne').continuous.comp_aestronglyMeasurable hum))
      (hu.integrable_smul_of_tsupport_subset hpc hpcs hps).norm.integrableOn
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · obtain ⟨h0, h1⟩ := posPartApprox_mem (hεpos n).le (u x)
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0]
      gcongr
      exact h1.trans (max_le (le_abs_self _) (abs_nonneg _))
    · exact ((tendsto_posPartApprox (u x)).comp hε0).const_smul _
  have hR : Tendsto (fun n => ∫ x in Ω, φ x • (deriv (posPartApprox (ε n)) (u x) * G x w) ∂μ)
      atTop (𝓝 (∫ x in Ω, φ x • ((if 0 < u x then 1 else 0) * G x w) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖φ x • G x w‖)
      (fun n => hφ.continuous.aestronglyMeasurable.smul
        ((((contDiff_posPartApprox (hεpos n).ne').continuous_deriv_one
          |>.comp_aestronglyMeasurable hum)).mul hGw.aestronglyMeasurable))
      (hGw.integrable_smul_of_tsupport_subset hφ.continuous hφcs hφΩ).norm.integrableOn
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · obtain ⟨h0, h1⟩ := deriv_posPartApprox_mem (hεpos n).ne' (u x)
      rw [norm_smul, norm_smul, norm_mul, Real.norm_eq_abs (deriv _ _), abs_of_nonneg h0]
      calc ‖φ x‖ * (deriv (posPartApprox (ε n)) (u x) * ‖G x w‖)
          ≤ ‖φ x‖ * (1 * ‖G x w‖) := by gcongr
        _ = ‖φ x‖ * ‖G x w‖ := by ring
    · exact (((tendsto_deriv_posPartApprox (u x)).mul_const _).const_smul _)
  have hlim := tendsto_nhds_unique hL (by simp only [hn]; exact hR.neg)
  rw [hset _ fun x hx => by simp [hz1 x hx], hlim,
    hset (fun x => φ x • (if 0 < u x then G x else 0) w) fun x hx => by simp [hz2 x hx]]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  split_ifs <;> simp

/-- **A constant shift** leaves the weak Fréchet derivative unchanged. -/
theorem HasWeakFDerivOn.sub_const {u : E → ℝ} {G : E → E →L[ℝ] ℝ} (hw : HasWeakFDerivOn Ω u G μ)
    (c : ℝ) : HasWeakFDerivOn Ω (fun x => u x - c) G μ :=
  (hw.sub (hasWeakFDerivOn_fderiv (u := fun _ => c) contDiffOn_const)).congr_ae
    (Eventually.of_forall fun _ => rfl) (Eventually.of_forall fun x => by simp)

/-- **Weak derivative of the negative part.** `min u 0` has the weak Fréchet derivative `G`
where `u < 0` and `0` elsewhere. -/
theorem HasWeakFDerivOn.negPart {u : E → ℝ} {G : E → E →L[ℝ] ℝ} (hw : HasWeakFDerivOn Ω u G μ) :
    HasWeakFDerivOn Ω (fun x => min (u x) 0) (fun x => if u x < 0 then G x else 0) μ := by
  refine hw.neg.posPart.neg.congr_ae (Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_)
  · simp only [Pi.neg_apply]
    rcases le_or_gt (u x) 0 with hx | hx
    · rw [min_eq_left hx, max_eq_left (by linarith), neg_neg]
    · rw [min_eq_right hx.le, max_eq_right (by linarith), neg_zero]
  · simp only [Pi.neg_apply, neg_pos]
    split_ifs <;> simp

/-- **Weak derivative of the absolute value.** `|u|` has the weak Fréchet derivative `G` where
`u > 0`, `-G` where `u < 0`, and `0` elsewhere. -/
theorem HasWeakFDerivOn.abs {u : E → ℝ} {G : E → E →L[ℝ] ℝ} (hw : HasWeakFDerivOn Ω u G μ) :
    HasWeakFDerivOn Ω (fun x => |u x|)
      (fun x => if 0 < u x then G x else if u x < 0 then -G x else 0) μ := by
  refine (hw.posPart.add hw.neg.posPart).congr_ae (Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_)
  · simp only [Pi.add_apply, Pi.neg_apply]
    exact max_zero_add_max_neg_zero_eq_abs_self (u x)
  · simp only [Pi.add_apply, Pi.neg_apply, neg_pos]
    rcases lt_trichotomy (u x) 0 with h | h | h
    · simp [h, not_lt.mpr h.le]
    · simp [h]
    · simp [h, not_lt.mpr h.le]

/-- **The weak derivative vanishes on level sets** (Gilbarg and Trudinger Lemma 7.7). On an
open set, the weak Fréchet derivative of `u` is zero almost everywhere on `{u = c}`. -/
theorem HasWeakFDerivOn.ae_eq_zero_of_eq_const {u : E → ℝ} {G : E → E →L[ℝ] ℝ}
    (hw : HasWeakFDerivOn Ω u G μ) (c : ℝ) : ∀ᵐ x ∂(μ.restrict Ω), u x = c → G x = 0 := by
  have hP := (hw.sub_const c).posPart
  have hN := (hw.neg.sub_const (-c)).posPart
  have h := ((hP.sub hN).congr_ae (u := fun x => max (u x - c) 0 - max ((-u) x - -c) 0)
    (u' := fun x => u x - c) (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun _ => rfl))
  · filter_upwards [h.ae_eq (hw.sub_const c)] with x hx hxc
    rw [← hx]
    simp [hxc]
  · simp only [Pi.neg_apply, neg_sub_neg]
    rw [← neg_sub (u x) c, max_zero_sub_max_neg_zero_eq_self]

end EllipticPdes
