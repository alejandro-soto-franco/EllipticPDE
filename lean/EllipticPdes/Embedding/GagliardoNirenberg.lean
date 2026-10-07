/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.Morrey
public import EllipticPdes.Embedding.Convolution
public import EllipticPdes.Embedding.WeakSobolev
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

/-!
# Sobolev bootstrap from `Lᵖ` to the conjugate exponent

`morrey_ball` needs a gradient in `Lᵖ` with `p > d`, and the interior `H²` estimate delivers one
in `L²`, so the two compose directly only when `d = 1`. The Gagliardo-Nirenberg-Sobolev
inequality closes the gap in low dimension: an `Lᵖ` weak gradient with `1 ≤ p < d` upgrades to
`Lᵖ'` at the Sobolev conjugate `1/p' = 1/p - 1/d`, and Morrey then applies whenever `p' > d`.

## Dimensions the chain reaches

`p' > d` is equivalent to `p > d/2`, and `L²` data on a ball of finite measure is `Lᵖ` data
exactly when `p ≤ 2`, so a single Sobolev step feeds Morrey precisely when the window
`d/2 < p ≤ min 2 d` is inhabited.

* `d = 1`: Morrey applies to the first-order gradient at `p = 2 > 1`, so no bootstrap is needed.
* `d = 2`: `p = 4/3` has conjugate `4 > 2` (`exists_eLpNorm_four_le`).
* `d = 3`: `p = 2` has conjugate `6 > 3` (`exists_eLpNorm_six_le`).
* `d ≥ 4`: the window is empty, since `d/2 ≥ 2`, so one Sobolev step never reaches `p' > d`.

The bootstrap itself holds in every dimension. Only its composition with Morrey out of `L²` data
is limited, and `EllipticPdes.Embedding.memLp_of_gradClosed` lifts that limit by iterating the
step, at the price of a weak derivative per rung.

Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` asks for `ContDiff ℝ 1` and compact
support, neither of which an `Lᵖ` class with weak derivatives has. Two devices bridge that.

* A smooth cutoff `η` supported in the ball turns a weak gradient on the ball into a compactly
  supported weak gradient on the whole space, with the product-rule term `v ∂ₖη`
  (`hasWeakGradOn_univ_mul_cutoff`).
* Mollification turns that into a smooth compactly supported function whose classical partials
  are the mollified weak gradient (`partialD_convolution_eq_of_hasWeakGradOn` at `Set.univ`),
  whose `Lᵖ` seminorms Young's inequality (`eLpNorm_convolution_le`) keeps bounded uniformly in
  the mollifier radius, and which converges almost everywhere to the original function, so Fatou
  (`MeasureTheory.eLpNorm_le_of_ae_tendsto`) passes the `Lᵖ'` bound to the limit.

## Main declarations

* `HasWeakGradOn.mono`: a weak gradient restricts to a subset.
* `hasWeakGradOn_univ_mul_cutoff`: the product rule against a smooth cutoff.
* `exists_eLpNorm_sobolevConj_le`: the bootstrap in general dimension and at a general exponent
  pair, with a constant independent of the function.
* `exists_eLpNorm_sobolevConj_le_of_le`: the same, fed by data at a higher exponent.
* `exists_eLpNorm_six_le` and `exists_eLpNorm_four_le`: the `d = 3` and `d = 2` specialisations.

## References

Evans, *Partial Differential Equations* (2nd ed.), §5.6.1 Thm 1.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal Convolution Topology

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD tsupport_partialD_subset)

variable {d : ℕ}

/-! ### Restriction of a weak gradient -/

/-- **Restriction of a weak gradient to a subset.** Both integration-by-parts integrals localise to
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

/-- **Dependence of a weak gradient on the almost-everywhere classes alone.** Replacing `u` and
`g` by functions agreeing with them almost everywhere on `B` leaves the integration-by-parts
identity untouched. This moves a statement about a restricted `Lp` class onto whichever
representative is convenient, in particular onto the extension by zero, which is shared across
every set. -/
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

/-! ### Product rule against a smooth cutoff -/

/-- The product rule for the coordinate partial derivative. -/
theorem partialD_mul {η φ : EuclideanSpace ℝ (Fin d) → ℝ} (k : Fin d)
    {y : EuclideanSpace ℝ (Fin d)} (hη : DifferentiableAt ℝ η y)
    (hφ : DifferentiableAt ℝ φ y) :
    partialD k (fun x => η x * φ x) y = partialD k η y * φ y + η y * partialD k φ y := by
  have hfd : HasFDerivAt (fun x => η x * φ x)
      (η y • fderiv ℝ φ y + φ y • fderiv ℝ η y) y := hη.hasFDerivAt.mul hφ.hasFDerivAt
  rw [partialD, hfd.fderiv]
  simp only [_root_.add_apply, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul, partialD]
  ring

/-- A function integrable on a set stays integrable after multiplication by a continuous
function of compact support. -/
theorem integrableOn_mul_of_hasCompactSupport {α : Type*} [TopologicalSpace α]
    {m : MeasurableSpace α} [OpensMeasurableSpace α] {μ : Measure α} {B : Set α} {f ψ : α → ℝ}
    (hf : IntegrableOn f B μ) (hψ : Continuous ψ) (hψs : HasCompactSupport ψ) :
    IntegrableOn (fun x => f x * ψ x) B μ := by
  obtain ⟨C, hC⟩ := hψs.exists_bound_of_continuous hψ
  exact hf.mul_bdd hψ.aestronglyMeasurable (Filter.Eventually.of_forall hC)

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
  -- The hypothesis applied to the test function `η φ`.
  have hψs : tsupport (fun x => η x * φ x) ⊆ B :=
    (closure_mono (Function.support_mul_subset_left η φ)).trans hηs
  have key := h (fun x => η x * φ x) (hηc.mul hφc) hφcs.mul_left hψs k
  have hprod : ∀ x, partialD k (fun z => η z * φ z) x
      = partialD k η x * φ x + η x * partialD k φ x :=
    fun x => partialD_mul k (hηd x) (hφd x)
  -- Integrability of the four products against the compactly supported smooth multipliers.
  have hi1 : IntegrableOn (fun x => u x * (partialD k η x * φ x)) B volume :=
    integrableOn_mul_of_hasCompactSupport hu (hηpc.mul hφc.continuous) hηpcs.mul_right
  have hi2 : IntegrableOn (fun x => u x * (η x * partialD k φ x)) B volume :=
    integrableOn_mul_of_hasCompactSupport hu (hηc.continuous.mul hφpc) hηcs.mul_right
  have hi3 : IntegrableOn (fun x => (η x * g k x) * φ x) B volume :=
    (integrableOn_mul_of_hasCompactSupport (hgi k) (hηc.continuous.mul hφc.continuous)
      hηcs.mul_right).congr (Filter.Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
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

/-! ### Bootstrap -/

section Bootstrap

/-- **Gagliardo-Nirenberg-Sobolev for a compactly supported weak gradient.** A compactly
supported `w` on `ℝᵈ` whose weak gradient `G` lies in `Lᵖ` lies in `Lᵖ'`, where
`1/p' = 1/p - 1/d`, bounded by the gradient alone with a constant depending only on `d` and
`p`. This is the coordinate form of `exists_eLpNorm_le_of_hasWeakFDerivOn_top`. -/
theorem exists_eLpNorm_sobolevConj_le_compactSupport (hd : 0 < d)
    {p p' : ℝ≥0} (hp : 1 ≤ p) (hpp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹) :
    ∃ K : ℝ≥0, ∀ (w : EuclideanSpace ℝ (Fin d) → ℝ)
        (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      HasCompactSupport w → Integrable w volume → MemLp w p volume →
      (∀ k, MemLp (G k) p volume) → HasWeakGradOn Set.univ w G →
      MemLp w p' volume ∧
        eLpNorm w p' volume ≤ (K : ℝ≥0∞) * ∑ k, eLpNorm (G k) p volume := by
  obtain ⟨K, hK⟩ := exists_eLpNorm_le_of_hasWeakFDerivOn_top (E := EuclideanSpace ℝ (Fin d))
    (F := ℝ) (μ := volume) finrank_euclideanSpace_fin hd hp hpp'
  refine ⟨K, fun w G hwcs hwint _ hGL hwg => ?_⟩
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp
  have hgi : ∀ k, LocallyIntegrableOn (G k) Set.univ volume := fun k =>
    ((hGL k).locallyIntegrable hp1).locallyIntegrableOn _
  have hw := (hasWeakGradOn_iff_hasWeakFDerivOn isOpen_univ
    (hwint.locallyIntegrable.locallyIntegrableOn _) hgi).1 hwg
  obtain ⟨hGp, hGb⟩ := memLp_gradCLM_of_forall hp1 hGL
  obtain ⟨hmem, hbd⟩ := hK w (gradCLM G) hwcs hGp hw
  exact ⟨hmem, hbd.trans (mul_le_mul' le_rfl hGb)⟩

/-- The extension by zero of a function in `Lᵖ(B)`, cut off by a function bounded by one, has
`Lᵖ` seminorm at most that of the function over `B`. -/
theorem eLpNorm_cutoff_mul_le {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [OpensMeasurableSpace α] {μ : Measure α} {B : Set α} (hB : MeasurableSet B)
    {η f : α → ℝ} (hη : Continuous η)
    (hη1 : ∀ x, ‖η x‖ ≤ 1) {p : ℝ≥0∞} (hf : AEStronglyMeasurable f (μ.restrict B)) :
    eLpNorm (fun x => η x * B.indicator f x) p μ ≤ eLpNorm f p (μ.restrict B) :=
  (eLpNorm_mono (g := B.indicator f)
    (show AEStronglyMeasurable (fun x => η x * B.indicator f x) μ from
      hη.aestronglyMeasurable.mul ((aestronglyMeasurable_indicator_iff hB).mpr hf))
    fun x => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hη1 x)).trans_eq
    (eLpNorm_indicator_eq_eLpNorm_restrict hB)

/-- **From `Lᵖ` to the Sobolev conjugate `Lᵖ'` (Evans, *Partial Differential Equations*
(2nd ed.), §5.6.1 Thm 1).** On a ball `Metric.ball c R` of `ℝᵈ` with `d ≥ 1`, a function `v` with
an `Lᵖ` weak gradient `g` lies in `Lᵖ'` of the smaller ball `Metric.ball c r`, where the exponents
satisfy `1/p' = 1/p - 1/d`, with a bound linear in `‖v‖_{Lᵖ} + ∑ₖ ‖gₖ‖_{Lᵖ}` and a constant
depending only on `d`, `p`, `c`, `r` and `R`.

The inequality itself is Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`, which asks
for `ContDiff ℝ 1` and compact support. Two devices transport it to a weak gradient on a ball: a
smooth cutoff supported in `Metric.ball c R` and equal to `1` on `Metric.closedBall c r`, and a
mollification, whose classical partials are the mollified weak gradient and whose `Lᵖ` seminorms
Young's inequality keeps bounded uniformly in the mollifier radius. Fatou passes the resulting
`Lᵖ'` bound to the almost-everywhere limit.

Outside the range `1 ≤ p < d`, which is the range Evans' statement takes, the hypothesis
`1/p' = 1/p - 1/d` says nothing about a Sobolev conjugate. At `p = d` it forces `p' = 0` and
the conclusion degenerates, `eLpNorm` at exponent zero being zero; above `p = d` its right
side is negative while the left is a reciprocal of a nonnegative number, so no `p'` meets it
and the statement is vacuous. -/
theorem exists_eLpNorm_sobolevConj_le (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d))
    {p p' : ℝ≥0} (hp : 1 ≤ p) (hpp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹)
    {r R : ℝ} (_hr : 0 < r) (hrR : r < R) :
    ∃ K : ℝ≥0, ∀ (v : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      MemLp v p (volume.restrict (Metric.ball c R)) →
      (∀ k, MemLp (g k) p (volume.restrict (Metric.ball c R))) →
      HasWeakGradOn (Metric.ball c R) v g →
      MemLp v p' (volume.restrict (Metric.ball c r)) ∧
        eLpNorm v p' (volume.restrict (Metric.ball c r))
          ≤ (K : ℝ≥0∞) * (eLpNorm v p (volume.restrict (Metric.ball c R))
              + ∑ k, eLpNorm (g k) p (volume.restrict (Metric.ball c R))) := by
  obtain ⟨K, hK⟩ := exists_eLpNorm_le_of_hasWeakFDerivOn_ball (E := EuclideanSpace ℝ (Fin d))
    (F := ℝ) (μ := volume) finrank_euclideanSpace_fin hd c hp hpp' hrR
  refine ⟨K, fun v g hv hg hwg => ?_⟩
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp
  have hgi : ∀ k, LocallyIntegrableOn (g k) (Metric.ball c R) volume := fun k => by
    have h : IntegrableOn (g k) (Metric.ball c R) volume := (hg k).integrable hp1
    exact h.locallyIntegrableOn
  have hvi : LocallyIntegrableOn v (Metric.ball c R) volume := by
    have h : IntegrableOn v (Metric.ball c R) volume := hv.integrable hp1
    exact h.locallyIntegrableOn
  have hw := (hasWeakGradOn_iff_hasWeakFDerivOn Metric.isOpen_ball hvi hgi).1 hwg
  obtain ⟨hGp, hGb⟩ := memLp_gradCLM_of_forall hp1 hg
  obtain ⟨hmem, hbd⟩ := hK v (gradCLM g) hv hGp hw
  exact ⟨hmem, hbd.trans (mul_le_mul' le_rfl (add_le_add le_rfl hGb))⟩

/-- **A Gagliardo-Nirenberg-Sobolev rung with its constant.** On the domains `D` and `D'`, a
function in `Lq(D)` whose weak gradient is in `Lq(D)` lies in `L^{p'}(D')`, bounded by `K` times
the sum of the `Lq(D)` seminorms of the function and its gradient. -/
def RungBound (D D' : Set (EuclideanSpace ℝ (Fin d))) (q p' K : ℝ≥0) : Prop :=
  ∀ (v : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
    MemLp v q (volume.restrict D) → (∀ k, MemLp (g k) q (volume.restrict D)) →
    HasWeakGradOn D v g →
    MemLp v p' (volume.restrict D') ∧
      eLpNorm v p' (volume.restrict D') ≤ (K : ℝ≥0∞) * (eLpNorm v q (volume.restrict D)
        + ∑ k, eLpNorm (g k) q (volume.restrict D))

/-- **A rung fed by a higher exponent.** On a domain of finite measure, `Lq` data with `p ≤ q` is
`Lᵖ` data at the price of a factor `|D|^{1/p - 1/q}` which the constant absorbs. -/
theorem RungBound.mono_exponent {D D' : Set (EuclideanSpace ℝ (Fin d))}
    [IsFiniteMeasure (volume.restrict D)] {p q p' K : ℝ≥0} (hp : 0 < p) (hpq : p ≤ q)
    (h : RungBound D D' p p' K) : ∃ K' : ℝ≥0, RungBound D D' q p' K' := by
  have hpqE : (p : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by exact_mod_cast hpq
  obtain ⟨A, hA⟩ := exists_const_eLpNorm_le_of_le (μ := volume.restrict D) (E := ℝ)
    (by exact_mod_cast hp.ne') hpqE
  refine ⟨K * A, fun v g hv hg hwg => ?_⟩
  obtain ⟨hmem, hbd⟩ := h v g (hv.mono_exponent hpqE) (fun k => (hg k).mono_exponent hpqE) hwg
  refine ⟨hmem, hbd.trans ?_⟩
  calc (K : ℝ≥0∞) * (eLpNorm v (p : ℝ≥0∞) (volume.restrict D)
          + ∑ k, eLpNorm (g k) (p : ℝ≥0∞) (volume.restrict D))
      ≤ (K : ℝ≥0∞) * (A * eLpNorm v (q : ℝ≥0∞) (volume.restrict D)
          + ∑ k, A * eLpNorm (g k) (q : ℝ≥0∞) (volume.restrict D)) :=
        mul_le_mul' le_rfl (add_le_add (hA v hv.aestronglyMeasurable)
          (Finset.sum_le_sum fun k _ => hA (g k) (hg k).aestronglyMeasurable))
    _ = ((K * A : ℝ≥0) : ℝ≥0∞) * (eLpNorm v (q : ℝ≥0∞) (volume.restrict D)
          + ∑ k, eLpNorm (g k) (q : ℝ≥0∞) (volume.restrict D)) := by
        rw [← Finset.mul_sum, ← mul_add, ENNReal.coe_mul, mul_assoc]

/-- **Bootstrap fed by a higher exponent.** The ball has finite measure, so `Lq` data with
`p ≤ q` is `Lᵖ` data, at the price of a factor `|B|^{1/p - 1/q}` which the constant absorbs.
This is the form the dimension-two chain uses: the interior `H²` estimate delivers `L²` data,
while the exponent that reaches Morrey through `1/p' = 1/p - 1/d` is `p = 4/3`. -/
theorem exists_eLpNorm_sobolevConj_le_of_le (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d))
    {p q p' : ℝ≥0} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hpp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ K : ℝ≥0, ∀ (v : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      MemLp v q (volume.restrict (Metric.ball c R)) →
      (∀ k, MemLp (g k) q (volume.restrict (Metric.ball c R))) →
      HasWeakGradOn (Metric.ball c R) v g →
      MemLp v p' (volume.restrict (Metric.ball c r)) ∧
        eLpNorm v p' (volume.restrict (Metric.ball c r))
          ≤ (K : ℝ≥0∞) * (eLpNorm v q (volume.restrict (Metric.ball c R))
              + ∑ k, eLpNorm (g k) q (volume.restrict (Metric.ball c R))) := by
  obtain ⟨K, hK⟩ := exists_eLpNorm_sobolevConj_le hd c hp hpp' hr hrR
  exact RungBound.mono_exponent (hp.trans_lt' one_pos) hpq (K := K) hK

/-- **From `L²` to `L⁶` in dimension three.** The Sobolev conjugate of `2` in dimension `3` is
`2·3/(3-2) = 6`, so a function with an `L²` weak gradient on `Metric.ball c R` lies in `L⁶` of
`Metric.ball c r`. Since `6 > 3`, this single step feeds `morrey_ball`. -/
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
  have h := exists_eLpNorm_sobolevConj_le (d := 3) (by norm_num) c (p := 2) (p' := 6)
    (by norm_num) (by push_cast; norm_num) hr hrR
  simpa using h

/-- **From `L²` to `L⁴` in dimension two.** At `d = 2` the Sobolev conjugate of `2` degenerates,
so the step is taken at `p = 4/3`, whose conjugate is `4`. The ball has finite measure, so the
`L²` data of the interior `H²` estimate is `L^{4/3}` data. Since `4 > 2`, the result feeds
`morrey_ball`, with Hölder exponent `1 - 2/4 = 1/2`. -/
theorem exists_eLpNorm_four_le (c : EuclideanSpace ℝ (Fin 2)) {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) :
    ∃ K : ℝ≥0, ∀ (v : EuclideanSpace ℝ (Fin 2) → ℝ)
        (g : Fin 2 → EuclideanSpace ℝ (Fin 2) → ℝ),
      MemLp v 2 (volume.restrict (Metric.ball c R)) →
      (∀ k, MemLp (g k) 2 (volume.restrict (Metric.ball c R))) →
      HasWeakGradOn (Metric.ball c R) v g →
      MemLp v 4 (volume.restrict (Metric.ball c r)) ∧
        eLpNorm v 4 (volume.restrict (Metric.ball c r))
          ≤ (K : ℝ≥0∞) * (eLpNorm v 2 (volume.restrict (Metric.ball c R))
              + ∑ k, eLpNorm (g k) 2 (volume.restrict (Metric.ball c R))) := by
  have h := exists_eLpNorm_sobolevConj_le_of_le (d := 2) (by norm_num) c
    (p := 4 / 3) (q := 2) (p' := 4) (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    (by rw [← NNReal.coe_le_coe]; push_cast; norm_num) (by push_cast; norm_num) hr hrR
  simpa using h

end Bootstrap

end EllipticPdes.Embedding
