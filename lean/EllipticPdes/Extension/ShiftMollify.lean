/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Analysis.LpTranslationContinuity
public import EllipticPdes.Embedding.Convolution

/-!
# Shifting before mollifying

Mollifying a function near the boundary of its domain asks for values the function does not
have. The global approximation theorem answers by shifting first: the function is translated
into the domain far enough that the mollifier of the shift only ever sees points where the
function is defined, and then the shift and the mollifier radius are sent to zero together.

This file proves that the two limits compose, so that a shifted mollification converges to the
function it started from. The identity that makes it work is that convolution commutes with
translation, so the mollification error of the shift is the shift of the mollification error,
which has the same norm.

## Main declarations

* `EllipticPdes.Extension.convolution_comp_translate`: convolution commutes with translation.
* `EllipticPdes.Extension.tendsto_eLpNorm_translate_convolution_sub`: a shifted mollification
  converges in `Lᵖ` to the function, as the shift and the radius go to zero together.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.3.3, Theorem 3.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Topology Convolution

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Analysis EllipticPdes.Embedding

variable {d : ℕ}

/-- **Convolution commutes with translation.** Convolving a translate is translating the
convolution, by the change of variables `t ↦ t + h` in the defining integral. -/
theorem convolution_comp_translate (f ρ : EuclideanSpace ℝ (Fin d) → ℝ)
    (h x : EuclideanSpace ℝ (Fin d)) :
    ((fun y => f (y + h)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x
      = (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) (x + h) := by
  simp only [convolution]
  rw [← integral_add_right_eq_self
    (fun t => (ContinuousLinearMap.lsmul ℝ ℝ) (f t) (ρ (x + h - t))) h]
  have harg : ∀ t : EuclideanSpace ℝ (Fin d), x + h - (t + h) = x - t := fun t => by abel
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  simp only [harg]

/-- **Convergence of a shifted mollification.** For `f` in `Lᵖ`, translating by `hᵢ` and
mollifying at radius `(φ i).rOut` gives a family converging to `f` in `Lᵖ`, as soon as both the
shift and the radius tend to zero.

The error splits into the mollification error of the shift and the shift error. The first is the
shift of the mollification error, by `convolution_comp_translate`, and translation is an `Lᵖ`
isometry, so it has the norm of the mollification error of `f` itself. -/
theorem tendsto_eLpNorm_translate_convolution_sub {p : ℝ} (hp : 1 ≤ p)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : MemLp f (ENNReal.ofReal p) volume)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin d))} {K : ℝ}
    {hv : ι → EuclideanSpace ℝ (Fin d)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hK : ∀ᶠ i in l, (φ i).rOut ≤ K * (φ i).rIn)
    (hh : Tendsto hv l (𝓝 0)) :
    Tendsto (fun i => eLpNorm
        ((fun y => f (y + hv i)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            ((φ i).normed volume) - f)
        (ENNReal.ofReal p) volume) l (𝓝 0) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hconv := tendsto_eLpNorm_convolution_sub (h := f) hp hf hφ hK
  have htrans := (tendsto_eLpNorm_translate_sub hp1 ENNReal.ofReal_ne_top hf).comp hh
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hconv.add htrans) (fun _ => zero_le) fun i => ?_
  set g := f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (φ i).normed volume with hg
  have hgc : Continuous g :=
    ((φ i).hasCompactSupport_normed).continuous_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) (hf.locallyIntegrable hp1) (φ i).continuous_normed
  -- the error is the shift of the mollification error, plus the shift error
  have hsplit : ((fun y => f (y + hv i)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (φ i).normed volume - f)
      = (fun z => g z - f z) ∘ (fun y => y + hv i) + fun y => f (y + hv i) - f y := by
    funext y
    simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply, hg,
      convolution_comp_translate f _ (hv i) y]
    ring
  rw [hsplit]
  refine (eLpNorm_add_le hp1).trans (add_le_add (le_of_eq ?_) le_rfl)
  exact eLpNorm_comp_translate (hgc.aestronglyMeasurable.sub hf.aestronglyMeasurable) (hv i) _

end EllipticPdes.Extension
