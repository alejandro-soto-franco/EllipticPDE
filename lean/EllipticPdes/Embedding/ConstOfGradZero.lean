/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.Morrey
public import EllipticPdes.Analysis.EuclideanFunctionalNorm

/-!
# Constancy of a class with zero weak gradient on a connected open set

Evans states this as Problem 11 of Chapter 5 and uses it in the proof of the Poincaré
inequality of §5.8.1, where the limit of the renormalised sequence has zero weak gradient and
must be constant to contradict its unit norm. Guo's Poincaré inequality is the `W_0^{1,p}`
form and does not need it.

The proof runs in three steps. On a ball whose double lies in the set, the mollifications of
the class have zero classical gradient, since the mollified weak gradient is the gradient of
the mollification, so each is constant on the ball, and an `L¹` limit of constants on a set of
positive finite measure is constant, the constants spanning a closed line in `L¹`. The constant
attached to each ball is locally constant in the centre, two overlapping balls sharing it on
their intersection, so on a preconnected set it is one constant. A countable subcover of the
set by such balls then puts the class equal to that constant almost everywhere.

## Main declarations

* `EllipticPdes.Embedding.ae_const_of_tendsto_ae_const`: an `L¹` limit of almost-everywhere
  constant functions is almost-everywhere constant.
* `EllipticPdes.Embedding.ae_const_on_ball_of_hasWeakGradOn_zero`: the class is constant
  on every ball whose double lies in the set.
* `EllipticPdes.Embedding.ae_const_of_hasWeakGradOn_zero`: the class is constant on a
  preconnected open set.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.8.1 Theorem 1 (p. 290) and
Chapter 5 Problem 11.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal Convolution

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-! ### The limit of constants -/

/-- **Constancy of an `L¹` limit of constants.** On a set of positive finite measure the
constants span a line in `L¹`, which is closed, so a limit of almost-everywhere constant
functions is almost-everywhere constant. -/
theorem ae_const_of_tendsto_ae_const {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : MemLp f 1 μ) {fn : ℕ → α → ℝ} {c : ℕ → ℝ}
    (hfn : ∀ n, fn n =ᵐ[μ] fun _ => c n)
    (htend : Tendsto (fun n => eLpNorm (fn n - f) 1 μ) atTop (𝓝 0)) :
    ∃ c₀ : ℝ, f =ᵐ[μ] fun _ => c₀ := by
  -- the constant class
  set one : Lp ℝ 1 μ := (memLp_const (1 : ℝ)).toLp _ with hone
  have hfnmem : ∀ n, MemLp (fn n) 1 μ := fun n =>
    (memLp_const (c n)).ae_eq (hfn n).symm
  have hfn_eq : ∀ n, (hfnmem n).toLp (fn n) = c n • one := by
    intro n
    apply Lp.ext
    filter_upwards [(hfnmem n).coeFn_toLp, Lp.coeFn_smul (c n) one,
      (memLp_const (1 : ℝ)).coeFn_toLp (p := 1) (μ := μ), hfn n] with x h1 h2 h3 h4
    rw [h1, h4, h2, Pi.smul_apply]
    simp only [hone] at h3 ⊢
    rw [h3, smul_eq_mul, mul_one]
  have htend' : Tendsto (fun n => (hfnmem n).toLp (fn n)) atTop (𝓝 (hf.toLp f)) := by
    rw [tendsto_iff_edist_tendsto_0]
    refine htend.congr fun n => ?_
    rw [Lp.edist_toLp_toLp]
  have hclosed : IsClosed ((Submodule.span ℝ {one} : Submodule ℝ (Lp ℝ 1 μ)) : Set (Lp ℝ 1 μ)) :=
    (Submodule.span ℝ {one}).closed_of_finiteDimensional
  have hmem : hf.toLp f ∈ Submodule.span ℝ {one} := by
    refine hclosed.mem_of_tendsto htend' (Eventually.of_forall fun n => ?_)
    rw [hfn_eq n]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self one)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨a, ?_⟩
  have h1 : (hf.toLp f : α → ℝ) =ᵐ[μ] f := hf.coeFn_toLp
  rw [← ha] at h1
  filter_upwards [h1, Lp.coeFn_smul a one,
    (memLp_const (1 : ℝ)).coeFn_toLp (p := 1) (μ := μ)] with x h1 h2 h3
  rw [← h1, h2, Pi.smul_apply]
  simp only [hone] at h3 ⊢
  rw [h3, smul_eq_mul, mul_one]

/-! ### Constancy on a ball -/

/-- **A mollification of a class with zero weak gradient has zero derivative.** Where the
mollifier's ball lies in `Ω`, the partial derivatives of the mollification of the extension by
zero are the mollified weak gradient, which is zero. -/
theorem fderiv_convolution_eq_zero_of_hasWeakGradOn_zero {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : IntegrableOn u Ω volume)
    (hwg : HasWeakGradOn Ω u fun _ _ => 0) (ρ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    {y : EuclideanSpace ℝ (Fin d)} (hsub : closedBall y ρ.rOut ⊆ Ω) :
    fderiv ℝ (Ω.indicator u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ.normed volume) y = 0 := by
  have hpart : ∀ k, partialD k
      (Ω.indicator u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ.normed volume) y = 0 := fun k => by
    have h := partialD_convolution_eq_of_hasWeakGradOn hΩm hu hwg ρ k hsub
    rw [show Ω.indicator (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) = 0 from
      indicator_zero ℝ Ω] at h
    rw [h]
    simp [convolution]
  rw [← norm_eq_zero, ← sq_eq_zero_iff, norm_sq_clm_eq_sum_apply_single]
  exact Finset.sum_eq_zero fun k _ => by
    have := hpart k
    simp only [partialD] at this
    rw [this]; ring

/-- **Constancy on a ball whose double lies in the set.** The mollifications of the class
have zero gradient on the ball, since the mollified weak gradient is the classical gradient of
the mollification, so each is constant there; they converge to the class in `L¹`, and the limit
of constants is constant. -/
theorem ae_const_on_ball_of_hasWeakGradOn_zero {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : IntegrableOn u Ω volume)
    (hwg : HasWeakGradOn Ω u fun _ _ => 0) {x : EuclideanSpace ℝ (Fin d)} {r : ℝ}
    (hr : 0 < r) (hx : closedBall x (2 * r) ⊆ Ω) :
    ∃ c : ℝ, u =ᵐ[volume.restrict (ball x r)] fun _ => c := by
  set L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ) with hL
  set φb : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := stdBump r hr with hφb
  have hφle : ∀ n, (φb n).rOut ≤ r := rOut_stdBump_le_self hr
  set uΩ : EuclideanSpace ℝ (Fin d) → ℝ := Ω.indicator u with huΩ
  set v : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun n => uΩ ⋆[L, volume] (φb n).normed volume with hvdef
  have huΩint : Integrable uΩ volume := hu.integrable_indicator hΩm
  have hvsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n) := fun n =>
    contDiff_convolution_normed (φb n) huΩint.locallyIntegrable
  -- each mollification is constant on the ball
  have hconst : ∀ n, ∀ y ∈ ball x r, v n y = v n x := fun n y hy =>
    isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball x r).isPreconnected
      ((hvsmooth n).differentiable (by simp)).differentiableOn
      (fun z hz => fderiv_convolution_eq_zero_of_hasWeakGradOn_zero hΩm hu hwg (φb n)
        (subset_trans (fun w hw => by
          rw [mem_closedBall] at hw ⊢
          linarith [hφle n, mem_ball.mp hz, dist_triangle w z x]) hx))
      hy (mem_ball_self hr)
  -- the mollifications converge to the class in `L¹` on the ball
  have hconv := tendsto_eLpNorm_one_stdBump_convolution_sub hr huΩint
  have hball : ball x r ⊆ Ω := fun z hz => hx (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith)) hz)
  have hue : u =ᵐ[volume.restrict (ball x r)] uΩ :=
    (ae_restrict_iff' measurableSet_ball).mpr
      (Eventually.of_forall fun y hy => (indicator_of_mem (hball hy) u).symm)
  have htend : Tendsto (fun n => eLpNorm (v n - u) 1 (volume.restrict (ball x r))) atTop
      (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
      (fun _ => zero_le) fun n => ?_
    calc eLpNorm (v n - u) 1 (volume.restrict (ball x r))
        = eLpNorm (v n - uΩ) 1 (volume.restrict (ball x r)) := by
          refine eLpNorm_congr_ae ?_
          filter_upwards [hue] with y hy
          simp only [Pi.sub_apply, hy]
      _ ≤ eLpNorm (v n - uΩ) 1 volume := eLpNorm_mono_measure _ Measure.restrict_le_self
  refine ae_const_of_tendsto_ae_const (c := fun n => v n x)
    (memLp_one_iff_integrable.mpr (hu.mono_set hball)) (fun n => ?_) htend
  exact (ae_restrict_iff' measurableSet_ball).mpr
    (Eventually.of_forall fun y hy => hconst n y hy)

/-! ### Constancy on a preconnected open set -/

/-- **Constancy of a class with zero weak gradient on a preconnected open set** (Evans,
Chapter 5 Problem 11). The constant attached to each ball whose double lies in the set is
locally constant in the centre, two overlapping balls sharing it on their intersection, so it
is one constant on the set; a countable subcover by such balls then puts the class equal to it
almost everywhere. -/
theorem ae_const_of_hasWeakGradOn_zero {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩopen : IsOpen Ω) (hΩconn : IsPreconnected Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u Ω volume) (hwg : HasWeakGradOn Ω u fun _ _ => 0) :
    ∃ c : ℝ, u =ᵐ[volume.restrict Ω] fun _ => c := by
  classical
  rcases Ω.eq_empty_or_nonempty with hΩe | ⟨x₀, hx₀⟩
  · refine ⟨0, ?_⟩
    rw [hΩe, Measure.restrict_empty]
    simp only [Filter.EventuallyEq, ae_zero]
    exact Filter.eventually_bot
  -- a ball with its double inside the set, and the constant on it, at every point
  have key : ∀ x, x ∈ Ω → ∃ r : ℝ, 0 < r ∧ closedBall x (2 * r) ⊆ Ω ∧
      ∃ c : ℝ, u =ᵐ[volume.restrict (ball x r)] fun _ => c := by
    intro x hx
    obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.mp hΩopen x hx
    have hsub : closedBall x (2 * (ε / 3)) ⊆ Ω :=
      (closedBall_subset_ball (by linarith)).trans hεΩ
    exact ⟨ε / 3, by positivity, hsub,
      ae_const_on_ball_of_hasWeakGradOn_zero hΩopen.measurableSet hu hwg (by positivity) hsub⟩
  choose! r hr hrΩ c hc using key
  -- two points of the set, one in the other's ball, share the constant
  have hshare : ∀ x ∈ Ω, ∀ y ∈ Ω, y ∈ ball x (r x) → c y = c x := by
    intro x hx y hy hyx
    by_contra hne
    have hpos : 0 < volume (ball x (r x) ∩ ball y (r y)) :=
      (isOpen_ball.inter isOpen_ball).measure_pos volume
        ⟨y, hyx, mem_ball_self (hr y hy)⟩
    have h1 : u =ᵐ[volume.restrict (ball x (r x) ∩ ball y (r y))] fun _ => c x :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hc x hx)
    have h2 : u =ᵐ[volume.restrict (ball x (r x) ∩ ball y (r y))] fun _ => c y :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hc y hy)
    have h3 : ∀ᵐ z ∂(volume.restrict (ball x (r x) ∩ ball y (r y))), c y = c x := by
      filter_upwards [h1, h2] with z hz1 hz2
      rw [← hz1, ← hz2]
    rw [ae_iff] at h3
    have : {z : EuclideanSpace ℝ (Fin d) | ¬ c y = c x} = univ := by
      ext z; simp [hne]
    rw [this, Measure.restrict_apply_univ] at h3
    exact hpos.ne' h3
  -- the constant is one value on the set, by preconnectedness
  have hloc : ∀ y ∈ Ω, c y = c x₀ := by
    intro y hy
    let b : EuclideanSpace ℝ (Fin d) → Bool := fun z => decide (c z = c x₀)
    have hcont : ContinuousOn b Ω := by
      intro x hx
      refine (continuousWithinAt_const (b := b x)).congr_of_eventuallyEq ?_ rfl
      have hball : ball x (r x) ∈ 𝓝[Ω] x :=
        mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr x hx))
      filter_upwards [hball, self_mem_nhdsWithin] with z hz hzΩ
      simp only [b]
      rw [hshare x hx z hzΩ hz]
    have := hΩconn.constant hcont hx₀ hy
    simp only [b, decide_true, eq_comm (a := true), decide_eq_true_eq] at this
    exact this
  -- a countable subcover of the set by the balls
  obtain ⟨t, htΩ, htc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun x => ball x (r x)) (s := Ω) fun x hx =>
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr x hx))
  refine ⟨c x₀, ?_⟩
  refine ae_restrict_of_ae_restrict_of_subset hcover ?_
  rw [ae_restrict_biUnion_iff _ htc]
  intro x hx
  filter_upwards [hc x (htΩ hx)] with z hz
  rw [hz, hloc x (htΩ hx)]

end EllipticPdes.Embedding
