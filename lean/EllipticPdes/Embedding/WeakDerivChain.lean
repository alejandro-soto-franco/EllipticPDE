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

end EllipticPdes
