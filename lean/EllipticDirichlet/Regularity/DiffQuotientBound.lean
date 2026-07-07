/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticDirichlet.Regularity.DifferenceQuotient
import EllipticDirichlet.Sobolev.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.CompactOpen

/-!
# Difference-quotient norm bounds

The two-directional bound of the difference-quotient method: a function with an
`L²` weak derivative has `L²`-bounded difference quotients (direction i), and a
uniform bound on the difference quotients yields a weak derivative (direction ii).
See Evans, *Partial Differential Equations* (2nd ed.), §5.8.2.

The direction-i bound is proved here for a smooth, compactly supported
representative `φ`, by the fundamental theorem of calculus along the segment
`t ↦ x + t • (h eₖ)`, a one-variable Cauchy-Schwarz bound on `[0, 1]`
(`MeasureTheory.sq_intervalIntegral_le`), a Tonelli swap of the order of
integration, and translation invariance of the Lebesgue integral.
-/

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticDirichlet.Regularity

open EllipticDirichlet.Sobolev (partialD)

variable {d : ℕ}

/-- `g` has whole-space weak `k`-derivative `g'` in `L²`: for every smooth compactly
supported test function `φ`, `∫ g ∂ₖφ = -∫ g' φ`. -/
def HasWeakDeriv (k : Fin d) (g g' : EucL2 d) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∫ x, (g x) * (partialD k φ x) = - ∫ x, (g' x) * (φ x)

/-! ### The smooth compactly supported case -/

/-- The segment path `t ↦ φ (x + t • v)` has derivative `(fderiv ℝ φ (x + t • v)) v`
at every `t`, for `φ` smooth. -/
private theorem hasDerivAt_comp_segment {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x v : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (x + s • v)) ((fderiv ℝ φ (x + t • v)) v) t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hφ' : HasFDerivAt φ (fderiv ℝ φ (x + t • v)) (x + t • v) :=
    (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt
  exact hφ'.comp_hasDerivAt t hline

/-- Continuity of the segment derivative `t ↦ (fderiv ℝ φ (x + t • v)) v`. -/
private theorem continuous_segment_deriv {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x v : EuclideanSpace ℝ (Fin d)) :
    Continuous (fun t : ℝ => (fderiv ℝ φ (x + t • v)) v) :=
  ((hφ.continuous_fderiv (by simp)).comp (by fun_prop)).clm_apply continuous_const

/-- Joint continuity of `(x, t) ↦ ((fderiv ℝ φ (x + t • v)) v) ^ 2`. -/
private theorem continuous_uncurry_segment {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (v : EuclideanSpace ℝ (Fin d)) :
    Continuous (Function.uncurry fun (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) =>
        ((fderiv ℝ φ (x + t • v)) v) ^ 2) :=
  (((hφ.continuous_fderiv (by simp)).comp (by fun_prop : Continuous
    fun p : EuclideanSpace ℝ (Fin d) × ℝ => p.1 + p.2 • v)).clm_apply continuous_const).pow 2

/-- Fundamental theorem of calculus along the segment from `x` to `x + v`. -/
private theorem sub_translation_eq_integral {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x v : EuclideanSpace ℝ (Fin d)) :
    φ (x + v) - φ x = ∫ t in (0 : ℝ)..1, (fderiv ℝ φ (x + t • v)) v := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hasDerivAt_comp_segment hφ x v t)
        (continuous_segment_deriv hφ x v).continuousOn.intervalIntegrable]
  simp

/-- Pointwise square estimate: `(φ (x + v) - φ x) ^ 2` is at most the `[0, 1]`
integral of the squared segment derivative. -/
private theorem sq_sub_translation_le {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x v : EuclideanSpace ℝ (Fin d)) :
    (φ (x + v) - φ x) ^ 2 ≤ ∫ t in (0 : ℝ)..1, ((fderiv ℝ φ (x + t • v)) v) ^ 2 := by
  rw [sub_translation_eq_integral hφ x v]
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have := MeasureTheory.sq_intervalIntegral_le h01
    (continuous_segment_deriv hφ x v).continuousOn
  simpa using this

/-- The integrand `(x, t) ↦ ((fderiv ℝ φ (x + t • v)) v) ^ 2` is integrable for the
product of Lebesgue measure with the unit-interval slice. -/
private theorem integrable_uncurry_segment {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) (v : EuclideanSpace ℝ (Fin d)) :
    Integrable (Function.uncurry fun (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) =>
        ((fderiv ℝ φ (x + t • v)) v) ^ 2)
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  set g : EuclideanSpace ℝ (Fin d) × ℝ → ℝ :=
    Function.uncurry fun (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) =>
      ((fderiv ℝ φ (x + t • v)) v) ^ 2 with hg
  set ρ : Measure (EuclideanSpace ℝ (Fin d) × ℝ) :=
    volume.prod (volume.restrict (Ioc (0 : ℝ) 1)) with hρ
  have hcont : Continuous g := continuous_uncurry_segment hφ v
  obtain ⟨R, hR⟩ := (hcs.fderiv ℝ).isCompact.isBounded.subset_closedBall 0
  -- The joint support sits inside the compact slab `C`.
  set C : Set (EuclideanSpace ℝ (Fin d) × ℝ) := closedBall 0 (R + ‖v‖) ×ˢ Icc 0 1 with hC
  have hCcomp : IsCompact C := (isCompact_closedBall _ _).prod isCompact_Icc
  have hIntOn : IntegrableOn g C ρ := hcont.locallyIntegrable.integrableOn_isCompact hCcomp
  -- `g` vanishes off `C` on the support of `ρ` (where `t ∈ Ioc 0 1`).
  have hzero : ∀ p : EuclideanSpace ℝ (Fin d) × ℝ, p.2 ∈ Ioc (0 : ℝ) 1 → p ∉ C → g p = 0 := by
    rintro ⟨x, t⟩ ht hpC
    have hxball : x ∉ closedBall (0 : EuclideanSpace ℝ (Fin d)) (R + ‖v‖) := by
      intro hx; exact hpC ⟨hx, ⟨le_of_lt ht.1, ht.2⟩⟩
    have hxt : x + t • v ∉ tsupport (fderiv ℝ φ) := by
      intro hmem
      apply hxball
      have hxK : ‖x + t • v‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hR hmem
      have htnorm : ‖t • v‖ ≤ ‖v‖ := by
        rw [norm_smul]
        have htle : ‖t‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_pos ht.1]; exact ht.2
        nlinarith [norm_nonneg v, htle]
      have hxle : ‖x‖ ≤ R + ‖v‖ := by
        calc ‖x‖ = ‖(x + t • v) - t • v‖ := by congr 1; abel
          _ ≤ ‖x + t • v‖ + ‖t • v‖ := norm_sub_le _ _
          _ ≤ R + ‖v‖ := by linarith
      simpa [mem_closedBall, dist_eq_norm] using hxle
    simp only [hg, Function.uncurry_apply_pair,
      image_eq_zero_of_notMem_tsupport hxt, ContinuousLinearMap.zero_apply]
    norm_num
  -- Almost everywhere `t ∈ Ioc 0 1`, so `g =ᵐ[ρ] C.indicator g`.
  have htioc : ∀ᵐ p ∂ρ, p.2 ∈ Ioc (0 : ℝ) 1 := by
    rw [ae_iff]
    -- The bad set is a product with the (Lebesgue-null) complement of `Ioc 0 1`.
    have hset : {p : EuclideanSpace ℝ (Fin d) × ℝ | p.2 ∉ Ioc (0 : ℝ) 1}
        = univ ×ˢ (Ioc (0 : ℝ) 1)ᶜ := by ext p; simp
    rw [hset, hρ, Measure.prod_prod, Measure.restrict_apply' measurableSet_Ioc,
      compl_inter_self, measure_empty, mul_zero]
  have hae : g =ᵐ[ρ] C.indicator g := by
    filter_upwards [htioc] with p hp
    by_cases hpC : p ∈ C
    · rw [indicator_of_mem hpC]
    · rw [indicator_of_notMem hpC, hzero p hp hpC]
  rw [integrable_congr hae]
  exact (integrable_indicator_iff hCcomp.measurableSet).mpr hIntOn

/-- Squaring the pointwise identity `(fderiv ℝ φ x) (hshift k h) = h * ∂ₖφ x`, obtained
from linearity of `fderiv` and `hshift k h = h • single k 1`. -/
private theorem sq_fderiv_hshift {φ : EuclideanSpace ℝ (Fin d) → ℝ} (k : Fin d) (h : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ((fderiv ℝ φ x) (hshift k h)) ^ 2 = h ^ 2 * (partialD k φ x) ^ 2 := by
  have hfv : (fderiv ℝ φ x) (hshift k h) = h * partialD k φ x := by
    simp [hshift, partialD]
  rw [hfv]; ring

/-- **Difference-quotient bound, smooth compactly supported case.** For `φ` smooth with
compact support, the `L²` norm of the difference quotient `Dₖʰφ` is bounded by the `L²`
norm of the `k`-th classical partial derivative: `‖Dₖʰφ‖ ≤ ‖∂ₖφ‖`. The argument is the
fundamental-theorem-of-calculus proof of Evans, *Partial Differential Equations* (2nd
ed.), §5.8.2, specialised to the single coordinate direction `k`, so no operator-norm
loss to the full gradient is incurred. -/
theorem norm_diffQuot_le_of_contDiff (k : Fin d) (h : ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ)
    (hL2 : MemLp φ 2 volume) (hL2' : MemLp (partialD k φ) 2 volume) :
    ‖diffQuot k h (hL2.toLp φ)‖ ≤ ‖hL2'.toLp (partialD k φ)‖ := by
  rcases eq_or_ne h 0 with rfl | hh
  · rw [diffQuot_zero, ContinuousLinearMap.zero_apply, norm_zero]
    exact norm_nonneg _
  set v : EuclideanSpace ℝ (Fin d) := hshift k h with hv
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hInt := integrable_uncurry_segment hφ hcs v
  -- The two sides of the pointwise square bound are integrable in `x`.
  have hLHS_int : Integrable (fun x => (φ (x + v) - φ x) ^ 2) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hφ.continuous.comp (by fun_prop)).sub hφ.continuous).pow 2
    · exact (((hcs.comp_homeomorph (Homeomorph.addRight v)).sub hcs).comp_left
        (g := fun r : ℝ => r ^ 2) (by simp))
  have hRHS_int : Integrable (fun x => ∫ t in (0 : ℝ)..1, ((fderiv ℝ φ (x + t • v)) v) ^ 2) := by
    simp_rw [intervalIntegral.integral_of_le h01]
    exact hInt.integral_prod_left
  -- Step A: integrate the pointwise square bound.
  have stepA : ∫ x, (φ (x + v) - φ x) ^ 2
      ≤ ∫ x, ∫ t in (0 : ℝ)..1, ((fderiv ℝ φ (x + t • v)) v) ^ 2 :=
    integral_mono hLHS_int hRHS_int (fun x => sq_sub_translation_le hφ x v)
  -- Step B: swap the order of integration (Tonelli).
  have stepB : (∫ x, ∫ t in (0 : ℝ)..1, ((fderiv ℝ φ (x + t • v)) v) ^ 2)
      = ∫ t in (0 : ℝ)..1, ∫ x, ((fderiv ℝ φ (x + t • v)) v) ^ 2 := by
    simp_rw [intervalIntegral.integral_of_le h01]
    exact integral_integral_swap hInt
  -- Step C: translation invariance collapses the inner integral, constant in `t`.
  have stepC : (∫ t in (0 : ℝ)..1, ∫ x, ((fderiv ℝ φ (x + t • v)) v) ^ 2)
      = ∫ x, ((fderiv ℝ φ x) v) ^ 2 := by
    have hI0 : ∀ t : ℝ, (∫ x, ((fderiv ℝ φ (x + t • v)) v) ^ 2) = ∫ x, ((fderiv ℝ φ x) v) ^ 2 :=
      fun t => integral_add_right_eq_self (fun x => ((fderiv ℝ φ x) v) ^ 2) (t • v)
    rw [intervalIntegral.integral_congr (g := fun _ => ∫ x, ((fderiv ℝ φ x) v) ^ 2)
        (fun t _ => hI0 t)]
    simp
  -- Step D: the exact (not lossy) collapse to the single partial derivative `∂ₖφ`.
  have stepD : (∫ x, ((fderiv ℝ φ x) v) ^ 2) = h ^ 2 * ∫ x, (partialD k φ x) ^ 2 := by
    rw [show (fun x => ((fderiv ℝ φ x) v) ^ 2)
          = fun x => h ^ 2 * (partialD k φ x) ^ 2 from funext fun x => sq_fderiv_hshift k h x]
    exact integral_const_mul _ _
  have hmain : ∫ x, (φ (x + v) - φ x) ^ 2 ≤ h ^ 2 * ∫ x, (partialD k φ x) ^ 2 := by
    rw [← stepD, ← stepC, ← stepB]; exact stepA
  -- Transport `hmain` back to the `L²` classes via the a.e. representative formulas.
  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving (· + v) volume volume :=
    (measurePreserving_add_right volume v).quasiMeasurePreserving
  have hshiftAE : (fun x => (hL2.toLp φ) (x + v)) =ᵐ[volume] (fun x => φ (x + v)) :=
    hqmp.ae_eq hL2.coeFn_toLp
  have hcombine : (diffQuot k h (hL2.toLp φ) : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume] fun x => (φ (x + v) - φ x) / h := by
    filter_upwards [coeFn_diffQuot k h (hL2.toLp φ), hL2.coeFn_toLp, hshiftAE]
      with x hx1 hx2 hx3
    rw [hx1, hx2, hx3]
  have hsq : ‖diffQuot k h (hL2.toLp φ)‖ ^ 2 ≤ ‖hL2'.toLp (partialD k φ)‖ ^ 2 := by
    rw [norm_sq_eq_integral_sq, norm_sq_eq_integral_sq]
    have hlhs : (∫ x, (diffQuot k h (hL2.toLp φ) x) ^ 2)
        = ∫ x, ((φ (x + v) - φ x) / h) ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [hcombine] with x hx
      rw [hx]
    have hrhs : (∫ x, (hL2'.toLp (partialD k φ) x) ^ 2) = ∫ x, (partialD k φ x) ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [hL2'.coeFn_toLp] with x hx
      rw [hx]
    rw [hlhs, hrhs]
    have hdiv : ∀ x, ((φ (x + v) - φ x) / h) ^ 2 = (φ (x + v) - φ x) ^ 2 / h ^ 2 := by
      intro x; rw [div_pow]
    rw [integral_congr_ae (Filter.Eventually.of_forall hdiv), integral_div]
    rw [div_le_iff₀ (by positivity)]
    calc (∫ x, (partialD k φ x) ^ 2) * h ^ 2 = h ^ 2 * ∫ x, (partialD k φ x) ^ 2 := by ring
      _ ≥ ∫ x, (φ (x + v) - φ x) ^ 2 := hmain
  have hnorm := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hnorm

/-! ### Strong `L²` convergence of the difference quotient to the derivative -/

/-- **Continuity of translation in `L²`.** As the shift `w → 0`, the translated function
`τ_w ψ` converges to `ψ` in `L²`. This is the strong continuity of the translation group on
`L²(ℝⁿ)`, obtained from joint continuity of composition with a measure-preserving family
(Evans, *Partial Differential Equations* (2nd ed.), §5.8.2). -/
theorem tendsto_transL2_zero (ψ : EucL2 d) :
    Filter.Tendsto (fun w : EuclideanSpace ℝ (Fin d) => transL2 w ψ)
      (nhds 0) (nhds ψ) := by
  set X := EuclideanSpace ℝ (Fin d) with hX
  -- The curried translation family `w ↦ (· + w)` is a continuous map into `C(X, X)`.
  have hcont : Continuous (fun p : X × X => p.2 + p.1) := by fun_prop
  set F : C(X × X, X) := ⟨fun p => p.2 + p.1, hcont⟩ with hF
  set G : C(X, C(X, X)) := F.curry with hG
  have hGw : ∀ w : X, (⇑(G w) : X → X) = fun x => x + w := fun w => rfl
  have hgm : ∀ w : X, MeasurePreserving (⇑(G w)) volume volume := by
    intro w
    rw [hGw w]; exact measurePreserving_add_right volume w
  have hgm0 : MeasurePreserving (⇑(G 0)) volume volume := hgm 0
  have hkey := Filter.Tendsto.compMeasurePreservingLp (μ := (volume : Measure X))
    (ν := (volume : Measure X)) (E := ℝ) (p := 2)
    (f := fun _ : X => ψ) (f₀ := ψ) (g := fun w => G w) (g₀ := G 0)
    tendsto_const_nhds (G.continuous.tendsto 0) hgm hgm0 (by norm_num)
  -- Identify each term with `transL2 w ψ` and the limit with `ψ`.
  have hterm : ∀ w : X, Lp.compMeasurePreserving (⇑(G w)) (hgm w) ψ = transL2 w ψ := by
    intro w
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_compMeasurePreserving ψ (hgm w), coeFn_transL2 w ψ]
      with x hx1 hx2
    rw [hx1, hx2, hGw w]; rfl
  have hlim : Lp.compMeasurePreserving (⇑(G 0)) hgm0 ψ = ψ := by
    rw [hterm 0]
    refine Lp.ext ?_
    filter_upwards [coeFn_transL2 (0 : X) ψ] with x hx
    rw [hx]; simp
  rw [hlim] at hkey
  refine hkey.congr' ?_
  filter_upwards with w using hterm w

end EllipticDirichlet.Regularity
