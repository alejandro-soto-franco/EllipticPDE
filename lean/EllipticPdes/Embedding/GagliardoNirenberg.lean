/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Embedding.Morrey
import EllipticPdes.Embedding.Convolution
import EllipticPdes.Regularity.CutoffTower
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

/-!
# The `L²`-to-`L⁶` bootstrap in dimension three

`morrey_ball` needs a gradient in `Lᵖ` with `p > d`, and the interior `H²` estimate delivers one
in `L²`, so the two compose directly only when `d = 1`. In dimension three the
Gagliardo-Nirenberg-Sobolev inequality closes the gap: at `p = 2` and `n = 3` the conjugate
exponent is `p' = 6 > 3`, so an `L²` weak gradient upgrades to `L⁶` and Morrey applies with
Hölder exponent `1 - 3/6 = 1/2`.

Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` asks for `ContDiff ℝ 1` and compact
support, neither of which an `L²` class with weak derivatives has. Two devices bridge that.

* A smooth cutoff `η` supported in the ball turns a weak gradient on the ball into a compactly
  supported weak gradient on the whole space, at the cost of the product-rule term `v ∂ₖη`
  (`hasWeakGradOn_univ_mul_cutoff`).
* Mollification turns that into a smooth compactly supported function whose classical partials
  are the mollified weak gradient (`partialD_convolution_eq_of_hasWeakGradOn` at `Set.univ`),
  whose `L²` seminorms Young's inequality (`eLpNorm_convolution_le`) keeps bounded uniformly in
  the mollifier radius, and which converges almost everywhere to the original function, so Fatou
  (`MeasureTheory.eLpNorm_le_of_ae_tendsto`) passes the `L⁶` bound to the limit.

## Main declarations

* `HasWeakGradOn.mono`: a weak gradient restricts to a subset.
* `hasWeakGradOn_univ_mul_cutoff`: the product rule against a smooth cutoff.
* `exists_eLpNorm_six_le`: the bootstrap, with a constant independent of the function.
-/

open MeasureTheory Set Metric
open scoped NNReal ENNReal Convolution Topology

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD tsupport_partialD_subset)

variable {d : ℕ}

/-! ### Restriction of a weak gradient -/

/-- **A weak gradient restricts to a subset.** Both integration-by-parts integrals localise to
the support of the test function, which lies in the smaller set, so the identity over the larger
set transfers verbatim. No measurability of either set is needed: each integrand vanishes off
`tsupport φ`, and `setIntegral_eq_integral_of_forall_compl_eq_zero` collapses both set integrals
to the same whole-space integral. -/
theorem HasWeakGradOn.mono {B B' : Set (EuclideanSpace ℝ (Fin d))} (hsub : B' ⊆ B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (h : HasWeakGradOn B u g) : HasWeakGradOn B' u g := by
  intro φ hφc hφcs hφB' k
  have key := h φ hφc hφcs (hφB'.trans hsub) k
  have hdk : ∀ x ∉ B', u x * partialD k φ x = 0 := by
    intro x hx
    rw [show partialD k φ x = 0 from image_eq_zero_of_notMem_tsupport
      (fun hc => hx (hφB' (tsupport_partialD_subset k φ hc))), mul_zero]
  have hphi : ∀ x ∉ B', g k x * φ x = 0 := by
    intro x hx
    rw [show φ x = 0 from image_eq_zero_of_notMem_tsupport (fun hc => hx (hφB' hc)), mul_zero]
  have hdkB : ∀ x ∉ B, u x * partialD k φ x = 0 := fun x hx => hdk x fun hc => hx (hsub hc)
  have hphiB : ∀ x ∉ B, g k x * φ x = 0 := fun x hx => hphi x fun hc => hx (hsub hc)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hdk,
    setIntegral_eq_integral_of_forall_compl_eq_zero hphi]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hdkB,
    setIntegral_eq_integral_of_forall_compl_eq_zero hphiB] at key
  exact key

/-- **A weak gradient depends only on the almost-everywhere classes.** Replacing `u` and `g` by
functions agreeing with them almost everywhere on `B` leaves the integration-by-parts identity
untouched. This moves a statement about a restricted `Lp` class onto whichever representative is
convenient, in particular onto the extension by zero, which is shared across every set. -/
theorem HasWeakGradOn.congr_ae {B : Set (EuclideanSpace ℝ (Fin d))}
    {u u' : EuclideanSpace ℝ (Fin d) → ℝ} {g g' : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (h : HasWeakGradOn B u g) (hu : u =ᵐ[volume.restrict B] u')
    (hg : ∀ k, g k =ᵐ[volume.restrict B] g' k) : HasWeakGradOn B u' g' := by
  intro φ hφc hφcs hφB k
  rw [← integral_congr_ae (hu.mono fun x hx => by simp only; rw [hx] :
      (fun x => u x * partialD k φ x) =ᵐ[volume.restrict B] fun x => u' x * partialD k φ x),
    ← integral_congr_ae ((hg k).mono fun x hx => by simp only; rw [hx] :
      (fun x => g k x * φ x) =ᵐ[volume.restrict B] fun x => g' k x * φ x)]
  exact h φ hφc hφcs hφB k

/-! ### The product rule against a smooth cutoff -/

/-- The product rule for the coordinate partial derivative. -/
theorem partialD_mul {η φ : EuclideanSpace ℝ (Fin d) → ℝ} (k : Fin d)
    {y : EuclideanSpace ℝ (Fin d)} (hη : DifferentiableAt ℝ η y)
    (hφ : DifferentiableAt ℝ φ y) :
    partialD k (fun x => η x * φ x) y = partialD k η y * φ y + η y * partialD k φ y := by
  have hfd : HasFDerivAt (fun x => η x * φ x)
      (η y • fderiv ℝ φ y + φ y • fderiv ℝ η y) y := hη.hasFDerivAt.mul hφ.hasFDerivAt
  rw [partialD, hfd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul, partialD]
  ring

/-- **Cutting a weak gradient off.** If `g` is the weak gradient of `u` on `B` and `η` is a
smooth compactly supported function with `tsupport η ⊆ B`, then the extension by zero of `η u`
has a weak gradient on the whole space, namely `η gₖ + u ∂ₖη`. Testing against `φ` reduces to
testing the hypothesis against `η φ`, which is again a test function supported in `B`, and the
product rule supplies the extra term. This is what makes the mollification argument reach a
compactly supported function without a boundary contribution from `∂B`. -/
theorem hasWeakGradOn_univ_mul_cutoff {B : Set (EuclideanSpace ℝ (Fin d))}
    (hB : MeasurableSet B) {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hηc : ContDiff ℝ (⊤ : ℕ∞) η) (hηcs : HasCompactSupport η) (hηs : tsupport η ⊆ B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u B volume) (hgi : ∀ k, IntegrableOn (g k) B volume)
    (h : HasWeakGradOn B u g) :
    HasWeakGradOn Set.univ (fun x => η x * B.indicator u x)
      (fun k x => η x * B.indicator (g k) x + partialD k η x * B.indicator u x) := by
  intro φ hφc hφcs _ k
  have hηd : Differentiable ℝ η := hηc.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφc.differentiable (by simp)
  -- The multipliers are continuous with compact support, hence bounded.
  have hηpc : Continuous (partialD k η) :=
    (hηc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hηpcs : HasCompactSupport (partialD k η) :=
    hηcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  have hφpc : Continuous (partialD k φ) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨Cη, hCη⟩ := hηcs.exists_bound_of_continuous hηc.continuous
  obtain ⟨Cηp, hCηp⟩ := hηpcs.exists_bound_of_continuous hηpc
  obtain ⟨Cφ, hCφ⟩ := hφcs.exists_bound_of_continuous hφc.continuous
  obtain ⟨Cφp, hCφp⟩ :=
    (hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))).exists_bound_of_continuous hφpc
  -- The hypothesis applied to the test function `η φ`.
  have hψs : tsupport (fun x => η x * φ x) ⊆ B :=
    (closure_mono (Function.support_mul_subset_left η φ)).trans hηs
  have key := h (fun x => η x * φ x) (hηc.mul hφc) hφcs.mul_left hψs k
  have hprod : ∀ x, partialD k (fun z => η z * φ z) x
      = partialD k η x * φ x + η x * partialD k φ x :=
    fun x => partialD_mul k (hηd x) (hφd x)
  -- Integrability of the four products against the bounded smooth multipliers.
  have hi1 : IntegrableOn (fun x => u x * (partialD k η x * φ x)) B volume :=
    hu.mul_bdd ((hηpc.mul hφc.continuous).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        calc ‖partialD k η x * φ x‖ = ‖partialD k η x‖ * ‖φ x‖ := norm_mul _ _
          _ ≤ Cηp * Cφ := mul_le_mul (hCηp x) (hCφ x) (norm_nonneg _)
              ((norm_nonneg _).trans (hCηp x)))
  have hi2 : IntegrableOn (fun x => u x * (η x * partialD k φ x)) B volume :=
    hu.mul_bdd ((hηc.continuous.mul hφpc).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        calc ‖η x * partialD k φ x‖ = ‖η x‖ * ‖partialD k φ x‖ := norm_mul _ _
          _ ≤ Cη * Cφp := mul_le_mul (hCη x) (hCφp x) (norm_nonneg _)
              ((norm_nonneg _).trans (hCη x)))
  have hi3 : IntegrableOn (fun x => (η x * g k x) * φ x) B volume := by
    have := (hgi k).mul_bdd ((hηc.continuous.mul hφc.continuous).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        calc ‖η x * φ x‖ = ‖η x‖ * ‖φ x‖ := norm_mul _ _
          _ ≤ Cη * Cφ := mul_le_mul (hCη x) (hCφ x) (norm_nonneg _)
              ((norm_nonneg _).trans (hCη x)))
    exact this.congr (Filter.Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  have hi4 : IntegrableOn (fun x => (partialD k η x * u x) * φ x) B volume :=
    hi1.congr (Filter.Eventually.of_forall fun x => by ring)
  -- Split the hypothesis by the product rule.
  have hsplit : (∫ x in B, u x * (partialD k η x * φ x))
      + ∫ x in B, u x * (η x * partialD k φ x)
      = - ∫ x in B, (η x * g k x) * φ x := by
    have hlhs : (∫ x in B, u x * (partialD k η x * φ x))
        + ∫ x in B, u x * (η x * partialD k φ x)
        = ∫ x in B, u x * partialD k (fun z => η z * φ z) x := by
      rw [← integral_add hi1 hi2]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [hprod]; ring)
    rw [hlhs, key]
    exact congrArg Neg.neg
      (integral_congr_ae (Filter.Eventually.of_forall fun x => by ring))
  -- Collapse the two whole-space integrals of the goal onto `B`.
  have hzeroL : ∀ x ∉ B, (η x * B.indicator u x) * partialD k φ x = 0 := by
    intro x hx
    rw [Set.indicator_of_notMem hx, mul_zero, zero_mul]
  have hzeroR : ∀ x ∉ B,
      (η x * B.indicator (g k) x + partialD k η x * B.indicator u x) * φ x = 0 := by
    intro x hx
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero, mul_zero, add_zero,
      zero_mul]
  have hL : ∫ x, (η x * B.indicator u x) * partialD k φ x
      = ∫ x in B, u x * (η x * partialD k φ x) := by
    rw [(setIntegral_eq_integral_of_forall_compl_eq_zero hzeroL).symm]
    exact setIntegral_congr_fun hB fun x hx => by
      rw [Set.indicator_of_mem hx]; ring
  have hR : ∫ x, (η x * B.indicator (g k) x + partialD k η x * B.indicator u x) * φ x
      = (∫ x in B, (η x * g k x) * φ x) + ∫ x in B, (partialD k η x * u x) * φ x := by
    rw [(setIntegral_eq_integral_of_forall_compl_eq_zero hzeroR).symm, ← integral_add hi3 hi4]
    exact setIntegral_congr_fun hB fun x hx => by
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
  have hswap : ∫ x in B, (partialD k η x * u x) * φ x
      = ∫ x in B, u x * (partialD k η x * φ x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [Measure.restrict_univ, hL, hR, hswap]
  linarith [hsplit]

/-! ### The bootstrap -/

section Three

open EllipticPdes.Regularity (exists_isTestFn_one_nhdsSet_of_isCompact)

/-- **From `L²` to `L⁶` in dimension three.** On a ball `Metric.ball c R`, a function `v` with an
`L²` weak gradient `g` lies in `L⁶` of the smaller ball `Metric.ball c r`, with a bound linear in
`‖v‖_{L²} + ∑ₖ ‖gₖ‖_{L²}` and a constant depending only on `c`, `r` and `R`. This is the
Gagliardo-Nirenberg-Sobolev inequality `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` at `p = 2`
and `n = 3`, where the conjugate exponent is `6`, transported from its smooth compactly supported
setting to a weak gradient by a cutoff and a mollification. -/
theorem exists_eLpNorm_six_le (c : EuclideanSpace ℝ (Fin 3)) {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) :
    ∃ K : ℝ≥0, ∀ (v : EuclideanSpace ℝ (Fin 3) → ℝ)
        (g : Fin 3 → EuclideanSpace ℝ (Fin 3) → ℝ),
      MemLp v 2 (volume.restrict (Metric.ball c R)) →
      (∀ k, MemLp (g k) 2 (volume.restrict (Metric.ball c R))) →
      HasWeakGradOn (Metric.ball c R) v g →
      MemLp v 6 (volume.restrict (Metric.ball c r)) ∧
        eLpNorm v 6 (volume.restrict (Metric.ball c r))
          ≤ (K : ℝ≥0∞) * (eLpNorm v 2 (volume.restrict (Metric.ball c R))
              + ∑ k, eLpNorm (g k) 2 (volume.restrict (Metric.ball c R))) := by
  classical
  set B : Set (EuclideanSpace ℝ (Fin 3)) := Metric.ball c R with hBdef
  have hBm : MeasurableSet B := measurableSet_ball
  have hR : 0 < R := hr.trans hrR
  haveI : IsFiniteMeasure (volume.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  -- The cutoff, equal to `1` on the inner ball and supported in the outer one.
  obtain ⟨η, hηtest, hη1, hηIcc⟩ := exists_isTestFn_one_nhdsSet_of_isCompact
    (K := Metric.closedBall c r) (U := B) (isCompact_closedBall c r) Metric.isOpen_ball
    (Metric.closedBall_subset_ball hrR)
  obtain ⟨hηc, hηcs, hηs⟩ := hηtest
  have hηone : ∀ x ∈ Metric.closedBall c r, η x = 1 := hη1.self_of_nhdsSet
  have hηnorm : ∀ x, ‖η x‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hηIcc x).1]; exact (hηIcc x).2
  -- A uniform bound on the cutoff's partial derivatives.
  have hfdc : Continuous (fun x => fderiv ℝ η x) := hηc.continuous_fderiv (by simp)
  obtain ⟨M, hM⟩ := (hηcs.fderiv ℝ).exists_bound_of_continuous hfdc
  have hM0 : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0)
  have hMk : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), ‖partialD k η x‖ ≤ M := by
    intro k x
    calc ‖partialD k η x‖ ≤ ‖fderiv ℝ η x‖ * ‖EuclideanSpace.single k (1 : ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ η x‖ := by simp
      _ ≤ M := hM x
  set Kg : ℝ≥0 :=
    SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 3))) 2 with hKgdef
  set Mn : ℝ≥0 := max 1 (Real.toNNReal (3 * M)) with hMndef
  refine ⟨Kg * Mn, fun v g hv hg hwg => ?_⟩
  -- The cut-off function and its whole-space weak gradient.
  set w : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => η x * B.indicator v x with hwdef
  set G : Fin 3 → EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun k x => η x * B.indicator (g k) x + partialD k η x * B.indicator v x with hGdef
  have hvint : IntegrableOn v B volume := hv.integrable (by norm_num)
  have hgint : ∀ k, IntegrableOn (g k) B volume := fun k => (hg k).integrable (by norm_num)
  have hwg' : HasWeakGradOn Set.univ w G :=
    hasWeakGradOn_univ_mul_cutoff hBm hηc hηcs hηs hvint hgint hwg
  -- `w` is compactly supported and integrable, and both `w` and `G` lie in `L²`.
  have hvB : MemLp (B.indicator v) 2 volume := (memLp_indicator_iff_restrict hBm).mpr hv
  have hgB : ∀ k, MemLp (B.indicator (g k)) 2 volume :=
    fun k => (memLp_indicator_iff_restrict hBm).mpr (hg k)
  have hwmeas : AEStronglyMeasurable w volume :=
    hηc.continuous.aestronglyMeasurable.mul hvB.aestronglyMeasurable
  have hwL2 : MemLp w 2 volume := by
    refine ⟨hwmeas, lt_of_le_of_lt (eLpNorm_mono (g := B.indicator v) fun x => ?_) hvB.2⟩
    rw [hwdef, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hηnorm x)
  have hwcs : HasCompactSupport w := hηcs.mul_right
  have hwint : Integrable w volume :=
    (hvint.integrable_indicator hBm).bdd_mul hηc.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hηnorm)
  have hGmeas : ∀ k, AEStronglyMeasurable (G k) volume := fun k =>
    (hηc.continuous.aestronglyMeasurable.mul (hgB k).aestronglyMeasurable).add
      (((hηc.continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable.mul hvB.aestronglyMeasurable)
  have hGbound : ∀ k, eLpNorm (G k) 2 volume
      ≤ eLpNorm (g k) 2 (volume.restrict B)
        + ENNReal.ofReal M * eLpNorm v 2 (volume.restrict B) := by
    intro k
    have h1 : eLpNorm (fun x => η x * B.indicator (g k) x) 2 volume
        ≤ eLpNorm (g k) 2 (volume.restrict B) := by
      refine (eLpNorm_mono (g := B.indicator (g k)) fun x => ?_).trans_eq
        (eLpNorm_indicator_eq_eLpNorm_restrict hBm)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hηnorm x)
    have h2 : eLpNorm (fun x => partialD k η x * B.indicator v x) 2 volume
        ≤ ENNReal.ofReal M * eLpNorm v 2 (volume.restrict B) := by
      have hstep : eLpNorm (fun x => partialD k η x * B.indicator v x) 2 volume
          ≤ eLpNorm (fun x => M * B.indicator v x) 2 volume := by
        refine eLpNorm_mono fun x => ?_
        rw [norm_mul, norm_mul, Real.norm_eq_abs M, abs_of_nonneg hM0]
        exact mul_le_mul_of_nonneg_right (hMk k x) (norm_nonneg _)
      refine hstep.trans (le_of_eq ?_)
      rw [show (fun x => M * B.indicator v x) = M • (B.indicator v) from rfl,
        eLpNorm_const_smul, eLpNorm_indicator_eq_eLpNorm_restrict hBm]
      congr 1
      rw [Real.enorm_eq_ofReal hM0]
    refine (eLpNorm_add_le (hηc.continuous.aestronglyMeasurable.mul (hgB k).aestronglyMeasurable)
      (((hηc.continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable.mul hvB.aestronglyMeasurable)
      (by norm_num)).trans (add_le_add h1 h2)
  have hGL2 : ∀ k, MemLp (G k) (ENNReal.ofReal 2) volume := by
    intro k
    refine ⟨hGmeas k, ?_⟩
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by simp]
    refine lt_of_le_of_lt (hGbound k) ?_
    exact ENNReal.add_lt_top.mpr ⟨(hg k).2, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hv.2⟩
  -- The shrinking mollifier family.
  set L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ) with hLdef
  have hLflip : L.flip = L := by
    refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
    simp only [hLdef, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
      smul_eq_mul]
    exact mul_comm b a
  let φb : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) := fun n =>
    { rIn := 1 / (n + 1 : ℝ) / 2
      rOut := 1 / (n + 1 : ℝ)
      rIn_pos := half_pos (by positivity)
      rIn_lt_rOut := half_lt_self (by positivity) }
  have hrOut : ∀ n : ℕ, (φb n).rOut = 1 / (n + 1 : ℝ) := fun _ => rfl
  have hrIn : ∀ n : ℕ, (φb n).rIn = 1 / (n + 1 : ℝ) / 2 := fun _ => rfl
  have hφrOut : Filter.Tendsto (fun n => (φb n).rOut) Filter.atTop (𝓝 0) := by
    simp only [hrOut]; exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hφratio : ∀ᶠ n in Filter.atTop, (φb n).rOut ≤ 2 * (φb n).rIn :=
    Filter.Eventually.of_forall fun n => le_of_eq (by rw [hrOut, hrIn]; ring)
  set W : ℕ → EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun n => w ⋆[L, volume] (φb n).normed volume with hWdef
  have hρ0 : ∀ n, (0 : EuclideanSpace ℝ (Fin 3) → ℝ) ≤ (φb n).normed volume :=
    fun n x => (φb n).nonneg_normed x
  have hρcont : ∀ n, Continuous ((φb n).normed volume) :=
    fun n => ((φb n).contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) _).continuous
  have hρm : ∀ n, AEStronglyMeasurable ((φb n).normed volume) volume :=
    fun n => (hρcont n).aestronglyMeasurable
  have hρ1 : ∀ n, ∫ y, (φb n).normed volume y ∂volume = 1 := fun n => (φb n).integral_normed
  have hwli : LocallyIntegrable w volume := hwint.locallyIntegrable
  have hWsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (W n) :=
    fun n => (φb n).hasCompactSupport_normed.contDiff_convolution_right (L := L) hwli
      (φb n).contDiff_normed
  have hWcs : ∀ n, HasCompactSupport (W n) :=
    fun n => HasCompactSupport.convolution (L := L) hwcs (φb n).hasCompactSupport_normed
  have hWpartialCont : ∀ n k, Continuous (partialD k (W n)) :=
    fun n k => ((hWsmooth n).continuous_fderiv (by simp)).clm_apply continuous_const
  -- The classical partials of a mollification are the mollified weak gradient.
  have hpartial : ∀ (n : ℕ) (k : Fin 3),
      partialD k (W n) = (G k ⋆[L, volume] (φb n).normed volume) := by
    intro n k
    funext x
    have hbridge := partialD_convolution_eq_of_hasWeakGradOn (B := Set.univ) MeasurableSet.univ
      (u := w) (g := G) (by rwa [IntegrableOn, Measure.restrict_univ]) hwg' (φb n) k
      (x := x) (subset_univ _)
    simpa only [Set.indicator_univ, hWdef] using hbridge
  -- Gagliardo-Nirenberg-Sobolev on each mollification, with Young keeping the bound uniform.
  have hbound : ∀ n, eLpNorm (W n) 6 volume ≤ (Kg : ℝ≥0∞) * ∑ k, eLpNorm (G k) 2 volume := by
    intro n
    have hgns : eLpNorm (W n) 6 volume ≤ (Kg : ℝ≥0∞) * eLpNorm (fderiv ℝ (W n)) 2 volume := by
      have h := MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq (F := ℝ)
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3)))) (u := W n)
        ((hWsmooth n).of_le (by exact_mod_cast le_top)) (hWcs n) (p := 2) (p' := 6)
        one_le_two (by simp) (by rw [finrank_euclideanSpace_fin]; norm_num)
      simpa [hKgdef] using h
    have hfd : eLpNorm (fderiv ℝ (W n)) 2 volume
        ≤ ∑ k, eLpNorm (partialD k (W n)) 2 volume := by
      calc eLpNorm (fderiv ℝ (W n)) 2 volume
          = eLpNorm (fun y => ‖fderiv ℝ (W n) y‖) 2 volume := (eLpNorm_norm _).symm
        _ ≤ eLpNorm (fun y => ∑ k, ‖partialD k (W n) y‖) 2 volume := by
            refine eLpNorm_mono fun y => ?_
            rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Real.norm_eq_abs,
              abs_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _)]
            exact norm_fderiv_le_sum_partialD (W n) y
        _ ≤ ∑ k, eLpNorm (partialD k (W n)) 2 volume := by
            rw [show (fun y => ∑ k, ‖partialD k (W n) y‖)
                = ∑ k, (fun y => ‖partialD k (W n) y‖) from by funext y; rw [Finset.sum_apply]]
            refine (eLpNorm_sum_le (fun k _ => ?_) (by norm_num)).trans_eq ?_
            · exact (hWpartialCont n k).aestronglyMeasurable.norm
            · exact Finset.sum_congr rfl fun k _ => eLpNorm_norm _
    have hyoung : ∀ k, eLpNorm (partialD k (W n)) 2 volume ≤ eLpNorm (G k) 2 volume := by
      intro k
      rw [hpartial n k]
      have h := eLpNorm_convolution_le (p := 2) (by norm_num) (hρ0 n) (hρm n) (hρ1 n) (hGL2 k)
      simpa [show ENNReal.ofReal (2 : ℝ) = 2 by simp] using h
    exact hgns.trans (mul_le_mul' le_rfl
      (hfd.trans (Finset.sum_le_sum fun k _ => hyoung k)))
  -- The mollifications converge to `w` almost everywhere, so Fatou passes the bound to `w`.
  have hae : ∀ᵐ x ∂volume, Filter.Tendsto (fun n => W n x) Filter.atTop (𝓝 (w x)) := by
    have hflip : ∀ n : ℕ,
        ((φb n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) = W n := by
      intro n
      change ((φb n).normed volume ⋆[L, volume] w) = w ⋆[L, volume] (φb n).normed volume
      conv_lhs => rw [← hLflip]
      exact convolution_flip (L := L)
    have h0 := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := volume) (g := w) hφrOut hφratio hwli
    filter_upwards [h0] with x hx
    exact hx.congr fun n => congrFun (hflip n) x
  have hwsix : eLpNorm w 6 volume ≤ (Kg : ℝ≥0∞) * ∑ k, eLpNorm (G k) 2 volume :=
    MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hbound)
      (fun n => (hWsmooth n).continuous.aestronglyMeasurable) hae
  -- Bound the whole-space gradient terms by the data on the outer ball.
  have hMn1 : (1 : ℝ≥0∞) ≤ (Mn : ℝ≥0∞) := by
    rw [← ENNReal.coe_one]; exact ENNReal.coe_le_coe.mpr (le_max_left _ _)
  have hMn3 : (3 : ℝ≥0∞) * ENNReal.ofReal M ≤ (Mn : ℝ≥0∞) := by
    have h3 : (3 : ℝ≥0∞) * ENNReal.ofReal M = ENNReal.ofReal (3 * M) := by
      rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
    rw [h3]
    exact ENNReal.coe_le_coe.mpr (le_max_right _ _)
  have hsum : ∑ k, eLpNorm (G k) 2 volume
      ≤ (Mn : ℝ≥0∞) * (eLpNorm v 2 (volume.restrict B)
          + ∑ k, eLpNorm (g k) 2 (volume.restrict B)) := by
    calc ∑ k, eLpNorm (G k) 2 volume
        ≤ ∑ k : Fin 3, (eLpNorm (g k) 2 (volume.restrict B)
            + ENNReal.ofReal M * eLpNorm v 2 (volume.restrict B)) :=
          Finset.sum_le_sum fun k _ => hGbound k
      _ = (∑ k, eLpNorm (g k) 2 (volume.restrict B))
            + 3 * ENNReal.ofReal M * eLpNorm v 2 (volume.restrict B) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring
      _ ≤ (Mn : ℝ≥0∞) * (∑ k, eLpNorm (g k) 2 (volume.restrict B))
            + (Mn : ℝ≥0∞) * eLpNorm v 2 (volume.restrict B) := by
          exact add_le_add (le_mul_of_one_le_left' hMn1)
            (mul_le_mul' hMn3 le_rfl)
      _ = (Mn : ℝ≥0∞) * (eLpNorm v 2 (volume.restrict B)
            + ∑ k, eLpNorm (g k) 2 (volume.restrict B)) := by ring
  -- On the inner ball the cutoff is `1`, so `w` and `v` agree there.
  have heq : ∀ x ∈ Metric.ball c r, w x = v x := by
    intro x hx
    rw [hwdef]
    simp only
    rw [hηone x (Metric.ball_subset_closedBall hx),
      Set.indicator_of_mem (hBdef ▸ Metric.ball_subset_ball hrR.le hx), one_mul]
  have hcongr : eLpNorm v 6 (volume.restrict (Metric.ball c r))
      = eLpNorm w 6 (volume.restrict (Metric.ball c r)) :=
    (eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_ball).mpr
      (Filter.Eventually.of_forall heq))).symm
  have hfinal : eLpNorm v 6 (volume.restrict (Metric.ball c r))
      ≤ ((Kg * Mn : ℝ≥0) : ℝ≥0∞) * (eLpNorm v 2 (volume.restrict B)
          + ∑ k, eLpNorm (g k) 2 (volume.restrict B)) := by
    rw [hcongr, ENNReal.coe_mul, mul_assoc]
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
      (hwsix.trans (mul_le_mul' le_rfl hsum))
  refine ⟨⟨?_, ?_⟩, hfinal⟩
  · exact hv.1.mono_measure (Measure.restrict_mono (Metric.ball_subset_ball hrR.le) le_rfl)
  · refine lt_of_le_of_lt hfinal (ENNReal.mul_lt_top ENNReal.coe_lt_top ?_)
    exact ENNReal.add_lt_top.mpr ⟨hv.2, ENNReal.sum_lt_top.mpr fun k _ => (hg k).2⟩

end Three

end EllipticPdes.Embedding
