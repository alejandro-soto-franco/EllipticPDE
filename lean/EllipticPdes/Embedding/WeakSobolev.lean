/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.Convolution
public import EllipticPdes.Sobolev.WeakDerivClassical
public import EllipticPdes.Analysis.SmoothCutoff
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

/-!
# The Gagliardo-Nirenberg-Sobolev inequality for weak derivatives

On a finite-dimensional real normed space `E` of dimension `d` with an additive Haar measure
`μ`, a compactly supported function `w : E → F` into a finite-dimensional normed space whose weak
Fréchet derivative `G` lies in `Lᵖ` (with `1 ≤ p`, `0 < d`) lies in `Lᵖ'` for `1/p' = 1/p - 1/d`,
and `‖w‖_{Lᵖ'} ≤ K ‖G‖_{Lᵖ}` with a constant depending only on `E`, `F`, `μ` and `p`.

Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` asks for `ContDiff ℝ 1`. A weak
derivative reaches it through mollification: the derivative of `ρₙ ⋆ w` is `ρₙ ⋆ G`, Young's
inequality keeps its `Lᵖ` seminorm below that of `G`, and Fatou's lemma passes the bound to the
almost everywhere limit.

## Main declarations

* `EllipticPdes.Embedding.exists_eLpNorm_le_of_hasWeakFDerivOn_top`: the inequality for a
  compactly supported function on the whole space.
-/

@[expose] public section

open MeasureTheory Set Metric Filter Topology TopologicalSpace Module
open scoped NNReal ENNReal Convolution

noncomputable section

namespace EllipticPdes.Embedding

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Gagliardo-Nirenberg-Sobolev inequality for a compactly supported weak derivative.** If
`w : E → F` has compact support and a weak Fréchet derivative `G` on the whole space with `G` in
`Lᵖ`, then `w` lies in `Lᵖ'` for `1/p' = 1/p - 1/d`, with `‖w‖_{Lᵖ'} ≤ K ‖G‖_{Lᵖ}` for a
constant `K` independent of `w` and `G`. -/
theorem exists_eLpNorm_le_of_hasWeakFDerivOn_top {d : ℕ} (hE : finrank ℝ E = d) (hd : 0 < d)
    {p p' : ℝ≥0} (hp : 1 ≤ p) (hpp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹) :
    ∃ K : ℝ≥0, ∀ (w : E → F) (G : E → E →L[ℝ] F), HasCompactSupport w →
      MemLp G p μ → HasWeakFDerivOn ⊤ w G μ →
      MemLp w p' μ ∧ eLpNorm w p' μ ≤ (K : ℝ≥0∞) * eLpNorm G p μ := by
  refine ⟨SNormLESNormFDerivOfEqConst F μ p, fun w G hwcs hGL hw => ?_⟩
  have hp1 : (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by exact_mod_cast hp
  have hwli : LocallyIntegrable w μ := locallyIntegrableOn_univ.1 (hw 0).locallyIntegrableOn_fun
  have hGli : LocallyIntegrable G μ := locallyIntegrableOn_univ.1 hw.locallyIntegrableOn
  set ρ : ℕ → ContDiffBump (0 : E) := mollifier one_pos with hρ
  set W : ℕ → E → F := fun n => (ρ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] w with hW
  have hWsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (W n) := fun n =>
    contDiff_normed_convolution (ρ n) hwli
  have hWfd : ∀ n x, fderiv ℝ (W n) x
      = ((ρ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] G) x := fun n x => by
    have := (hasFDerivAt_convolution_of_forall_integral_eq (K := univ) (u := w) (G := G)
      (by rwa [indicator_univ]) (by rwa [indicator_univ])
      (fun v ψ hψ hψc hψs => (hw v).integral_eq hψ hψc hψs) (ρ n) (y := x) (subset_univ _))
    simpa only [indicator_univ] using this.fderiv
  have hbound : ∀ n, eLpNorm (W n) p' μ
      ≤ (SNormLESNormFDerivOfEqConst F μ p : ℝ≥0∞) * eLpNorm G p μ := fun n => by
    refine (eLpNorm_le_eLpNorm_fderiv_of_eq (μ := μ) ((hWsmooth n).of_le (by exact_mod_cast le_top))
      (hasCompactSupport_normed_convolution (ρ n) hwcs) hp (hE ▸ hd) (by rw [hE]; exact hpp')).trans
      (mul_le_mul' le_rfl ?_)
    rw [show fderiv ℝ (W n) = _ from funext (hWfd n)]
    exact eLpNorm_convolution_le_of_integral_eq_one hp1 ENNReal.coe_ne_top
      (fun x => (ρ n).nonneg_normed x) (ρ n).continuous_normed.aestronglyMeasurable
      (ρ n).integral_normed hGL.aestronglyMeasurable
  have hae : ∀ᵐ x ∂μ, Tendsto (fun n => W n x) atTop (𝓝 (w x)) := by
    filter_upwards [ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := μ) (g := w) (tendsto_rOut_mollifier (E := E) one_pos)
      (Eventually.of_forall (rOut_mollifier_le_two_mul_rIn one_pos)) hwli] with x hx using hx
  have hwsix : eLpNorm w p' μ ≤ (SNormLESNormFDerivOfEqConst F μ p : ℝ≥0∞) * eLpNorm G p μ :=
    Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hbound)
      (fun n => (hWsmooth n).continuous.aestronglyMeasurable) hwli.aestronglyMeasurable hae
  exact ⟨memLp_iff.2 (hwsix.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hGL.eLpNorm_lt_top)),
    hwsix⟩

omit [μ.IsAddHaarMeasure] [FiniteDimensional ℝ F] in
/-- **The cut-off weak derivative in `Lᵖ`.** For a cutoff `η` with `|η| ≤ 1`, `‖Dη‖ ≤ M` and
support in a measurable set `B`, the weak derivative `η G + Dη ⊗ v` of `η v`, which vanishes off
`B`, has `Lᵖ` seminorm at most `‖G‖_{Lᵖ(B)} + M ‖v‖_{Lᵖ(B)}`. -/
theorem eLpNorm_cutoff_deriv_le {B : Set E} (hB : MeasurableSet B) {η : E → ℝ} {M : ℝ≥0}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη1 : ∀ x, ‖η x‖ ≤ 1) (hM : ∀ x, ‖fderiv ℝ η x‖ ≤ M)
    (hηB : tsupport η ⊆ B) {p : ℝ≥0∞} (hp : 1 ≤ p) {v : E → F} {G : E → E →L[ℝ] F}
    (hv : AEStronglyMeasurable v (μ.restrict B)) (hG : AEStronglyMeasurable G (μ.restrict B)) :
    eLpNorm (fun x => η x • G x + (fderiv ℝ η x).smulRight (v x)) p μ
      ≤ eLpNorm G p (μ.restrict B) + M * eLpNorm v p (μ.restrict B) := by
  have hsupp : Function.support (fun x => η x • G x + (fderiv ℝ η x).smulRight (v x)) ⊆ B :=
    fun x hx => hηB (by
      by_contra h
      exact hx (by simp [image_eq_zero_of_notMem_tsupport h,
        image_eq_zero_of_notMem_tsupport (f := fderiv ℝ η)
          fun h' => h (tsupport_fderiv_subset ℝ h')]))
  have hind := eLpNorm_indicator_eq_eLpNorm_restrict (μ := μ) (p := p) hB
    (f := fun x => η x • G x + (fderiv ℝ η x).smulRight (v x))
  rw [indicator_eq_self.2 hsupp] at hind
  rw [hind]
  have hadd := eLpNorm_add_le (μ := μ.restrict B) (p := p)
    (f := fun x => η x • G x) (g := fun x => (fderiv ℝ η x).smulRight (v x)) hp
  refine le_trans hadd (add_le_add ?_ ?_)
  · calc eLpNorm (fun x => η x • G x) p (μ.restrict B)
        ≤ ENNReal.ofReal 1 * eLpNorm G p (μ.restrict B) :=
          eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hη.continuous.aestronglyMeasurable.smul hG)
            (Filter.Eventually.of_forall fun x => by
              simpa [norm_smul] using mul_le_of_le_one_left (norm_nonneg _) (hη1 x)) p
      _ = eLpNorm G p (μ.restrict B) := by simp
  · calc eLpNorm (fun x => (fderiv ℝ η x).smulRight (v x)) p (μ.restrict B)
        ≤ ENNReal.ofReal (M : ℝ) * eLpNorm v p (μ.restrict B) :=
          eLpNorm_le_mul_eLpNorm_of_ae_le_mul
            ((ContinuousLinearMap.smulRightL ℝ E F).aestronglyMeasurable_comp₂
              (hη.continuous_fderiv (by simp)).aestronglyMeasurable hv)
            (Filter.Eventually.of_forall fun x => by
              change ‖(fderiv ℝ η x).smulRight (v x)‖ ≤ _
              rw [ContinuousLinearMap.norm_smulRight_apply]
              exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)) p
      _ = M * eLpNorm v p (μ.restrict B) := by rw [ENNReal.ofReal_coe_nnreal]

/-- **The Sobolev conjugate bound on a ball.** Let `v : E → F` and `G` lie in `Lᵖ` of the ball
`ball c R`, with `G` the weak Fréchet derivative of `v` there. Then for `r < R`, `v` lies in `Lᵖ'`
of the smaller ball `ball c r`, `1/p' = 1/p - 1/d`, and
`‖v‖_{Lᵖ'(ball c r)} ≤ K (‖v‖_{Lᵖ(ball c R)} + ‖G‖_{Lᵖ(ball c R)})` for a constant `K`
independent of `v` and `G`. -/
theorem exists_eLpNorm_le_of_hasWeakFDerivOn_ball {d : ℕ} (hE : finrank ℝ E = d) (hd : 0 < d)
    (c : E) {p p' : ℝ≥0} (hp : 1 ≤ p) (hpp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹) {r R : ℝ}
    (hrR : r < R) :
    ∃ K : ℝ≥0, ∀ (v : E → F) (G : E → E →L[ℝ] F),
      MemLp v p (μ.restrict (ball c R)) → MemLp G p (μ.restrict (ball c R)) →
      HasWeakFDerivOn ⟨ball c R, isOpen_ball⟩ v G μ →
      MemLp v p' (μ.restrict (ball c r)) ∧ eLpNorm v p' (μ.restrict (ball c r))
        ≤ (K : ℝ≥0∞) * (eLpNorm v p (μ.restrict (ball c R))
          + eLpNorm G p (μ.restrict (ball c R))) := by
  obtain ⟨η, hηsm, hηcs, hηs, hη1, hηI⟩ := exists_contDiff_one_on_compact
    (isCompact_closedBall c r) isOpen_ball (closedBall_subset_ball hrR)
  obtain ⟨M, hM⟩ := (hηcs.fderiv ℝ).exists_bound_of_continuous
    (hηsm.continuous_fderiv (by simp) : Continuous fun x => fderiv ℝ η x)
  obtain ⟨Kg, hKg⟩ := exists_eLpNorm_le_of_hasWeakFDerivOn_top (μ := μ) (F := F) hE hd hp hpp'
  refine ⟨Kg * (1 + M.toNNReal), fun v G hv hG hw => ?_⟩
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp
  have hz : ∀ x ∉ tsupport η, η x = 0 ∧ fderiv ℝ η x = 0 := fun x hx =>
    ⟨image_eq_zero_of_notMem_tsupport hx,
      image_eq_zero_of_notMem_tsupport (f := fderiv ℝ η) fun h => hx (tsupport_fderiv_subset ℝ h)⟩
  have hM' : ∀ x, ‖fderiv ℝ η x‖ ≤ M.toNNReal := fun x => (hM x).trans (Real.le_coe_toNNReal M)
  have hη1' : ∀ x, ‖η x‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hηI x).1]; exact (hηI x).2
  have hw' : HasWeakFDerivOn ⊤ (fun x => η x • v x)
      (fun x => η x • G x + (fderiv ℝ η x).smulRight (v x)) μ :=
    (hw.smul_left hηsm).top_of_forall_notMem_eq_zero (K := tsupport η) hηcs hηs
      (fun x hx => by simp [(hz x hx).1])
      (fun x hx => by simp [(hz x hx).1, (hz x hx).2])
  have hwcs : HasCompactSupport fun x => η x • v x :=
    HasCompactSupport.intro hηcs fun x hx => by simp [(hz x hx).1]
  have hcut := eLpNorm_cutoff_deriv_le measurableSet_ball hηsm hη1' hM' hηs hp1
    hv.aestronglyMeasurable hG.aestronglyMeasurable
  have hGL : MemLp (fun x => η x • G x + (fderiv ℝ η x).smulRight (v x)) p μ :=
    memLp_iff.2 (hcut.trans_lt (ENNReal.add_lt_top.2 ⟨hG.eLpNorm_lt_top,
      ENNReal.mul_lt_top ENNReal.coe_lt_top hv.eLpNorm_lt_top⟩))
  obtain ⟨hmem, hbd⟩ := hKg _ _ hwcs hGL hw'
  have hinner : eLpNorm v p' (μ.restrict (ball c r))
      = eLpNorm (fun x => η x • v x) p' (μ.restrict (ball c r)) :=
    eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun x hx => by
      simp [hη1 x (ball_subset_closedBall hx)]))
  have hfin : eLpNorm v p' (μ.restrict (ball c r))
      ≤ (Kg * (1 + M.toNNReal) : ℝ≥0) * (eLpNorm v p (μ.restrict (ball c R))
        + eLpNorm G p (μ.restrict (ball c R))) := by
    rw [hinner]
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hbd.trans ?_)
    rw [ENNReal.coe_mul, mul_assoc]
    refine mul_le_mul' le_rfl (hcut.trans ?_)
    calc eLpNorm G p (μ.restrict (ball c R)) + M.toNNReal * eLpNorm v p (μ.restrict (ball c R))
        ≤ (eLpNorm v p (μ.restrict (ball c R)) + eLpNorm G p (μ.restrict (ball c R)))
          + M.toNNReal * (eLpNorm v p (μ.restrict (ball c R))
            + eLpNorm G p (μ.restrict (ball c R))) :=
          add_le_add le_add_self (mul_le_mul' le_rfl le_self_add)
      _ = _ := by push_cast; ring
  exact ⟨memLp_iff.2 (hfin.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
    (ENNReal.add_lt_top.2 ⟨hv.eLpNorm_lt_top, hG.eLpNorm_lt_top⟩))), hfin⟩

end EllipticPdes.Embedding
