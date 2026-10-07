/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.WeakDerivChain
public import EllipticPdes.Embedding.WeakGradUnique

/-!
# Chain rule for weak gradients

The statements are the coordinate forms, on `EuclideanSpace ℝ (Fin d)`, of the results for a
weak Fréchet derivative on any finite-dimensional normed space proved in
`EllipticPdes.Embedding.WeakDerivChain`: the chain rule, the positive and negative parts, the
absolute value and the vanishing of the weak gradient on level sets. A weak gradient on an open
set is a weak Fréchet derivative with the gradient functional `gradCLM`, and the results transfer
through that bridge.

Integrability is asked for locally on the domain throughout, which is the class the sources
state the results for, and the domain is open.

## Main declarations

* `EllipticPdes.Embedding.hasWeakGradOn_comp`: the chain rule for a `C¹` function with bounded
  derivative.
* `EllipticPdes.Embedding.hasWeakGradOn_posPart`: the weak gradient of the positive part.
* `EllipticPdes.Embedding.hasWeakGradOn_negPart`, `EllipticPdes.Embedding.hasWeakGradOn_abs`:
  the weak gradients of `min u 0` and `|u|`.
* `EllipticPdes.Embedding.ae_eq_zero_of_eq_const_of_hasWeakGradOn`: the weak gradient vanishes
  almost everywhere on a level set.

## References

D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§7.4 Lemma 7.5 (p. 151), Lemma 7.6 and Lemma 7.7 (p. 152);
L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.10 Problems 17 and 18 (p. 308).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal Convolution

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD tsupport_partialD_subset)

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### Elementary closure properties with local integrability -/

/-- **Negation of a weak gradient.** -/
theorem HasWeakGradOn.neg {B : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (h : HasWeakGradOn B u g) : HasWeakGradOn B (fun x => -u x) (fun k x => -g k x) := by
  intro φ hφc hφcs hφB k
  have key := h φ hφc hφcs hφB k
  simp only [neg_mul, integral_neg, key, neg_neg]

/-- **Additivity of a weak gradient**, with local integrability on an open set. -/
theorem HasWeakGradOn.add_of_locallyIntegrableOn
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} {g h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : LocallyIntegrableOn u Ω volume) (hv : LocallyIntegrableOn v Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hh : ∀ k, LocallyIntegrableOn (h k) Ω volume)
    (hU : HasWeakGradOn Ω u g) (hV : HasWeakGradOn Ω v h) :
    HasWeakGradOn Ω (fun x => u x + v x) (fun k x => g k x + h k x) := by
  intro φ hφc hφcs hφs k
  have hφcont : Continuous φ := hφc.continuous
  have hφpc : Continuous (partialD k φ) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφpcs : HasCompactSupport (partialD k φ) :=
    hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  have hps : tsupport (partialD k φ) ⊆ Ω := (tsupport_partialD_subset k φ).trans hφs
  have hL : ∫ x in Ω, (u x + v x) * partialD k φ x
      = (∫ x in Ω, u x * partialD k φ x) + ∫ x in Ω, v x * partialD k φ x := by
    rw [← integral_add (integrable_mul_of_locallyIntegrableOn hu hφpc hφpcs hps).integrableOn
      (integrable_mul_of_locallyIntegrableOn hv hφpc hφpcs hps).integrableOn]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hR : ∫ x in Ω, (g k x + h k x) * φ x
      = (∫ x in Ω, g k x * φ x) + ∫ x in Ω, h k x * φ x := by
    rw [← integral_add (integrable_mul_of_locallyIntegrableOn (hg k) hφcont hφcs hφs).integrableOn
      (integrable_mul_of_locallyIntegrableOn (hh k) hφcont hφcs hφs).integrableOn]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [hL, hR, hU φ hφc hφcs hφs k, hV φ hφc hφcs hφs k]
  ring

/-- A weak Fréchet derivative equal to the gradient functional of a family `g` is a weak gradient
with components `g`. -/
theorem hasWeakGradOn_of_hasWeakFDerivOn {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {v : EuclideanSpace ℝ (Fin d) → ℝ}
    {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (h : HasWeakFDerivOn Ω v G volume)
    (hG : G = gradCLM g) : HasWeakGradOn Ω v g := by
  subst hG
  exact (hasWeakGradOn_iff_hasWeakFDerivOn Ω.isOpen (h 0).locallyIntegrableOn_fun fun k => by
    simpa using (h (EuclideanSpace.single k 1)).locallyIntegrableOn).2 h

/-- **Chain rule for weak gradients** (Gilbarg and Trudinger Lemma 7.5, Evans §5.10 Problem
17). A `C¹` function with bounded derivative, composed with a class with a locally integrable
weak gradient on an open set, has the weak gradient `f'(u) ∇u` there. This is the coordinate
form of `HasWeakFDerivOn.comp_contDiff`. -/
theorem hasWeakGradOn_comp (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hwg : HasWeakGradOn Ω u g)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ≥0} (hM : ∀ t, ‖deriv f t‖₊ ≤ M) :
    HasWeakGradOn Ω (fun x => f (u x)) (fun k x => deriv f (u x) * g k x) :=
  hasWeakGradOn_of_hasWeakFDerivOn (Ω := ⟨Ω, hΩ⟩)
    (((hasWeakGradOn_iff_hasWeakFDerivOn hΩ hu hg).1 hwg).comp_contDiff hf hM)
    (funext fun x => ContinuousLinearMap.ext fun v => by
      simp only [gradCLM, sum_apply, smul_apply, smul_eq_mul, Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp; ring)

/-- **Weak gradient of the positive part** (Gilbarg and Trudinger Lemma 7.6, Evans §5.10
Problem 18). On an open set, `u⁺ = max u 0` has the weak gradient `∇u` where `u > 0` and `0`
elsewhere. -/
theorem hasWeakGradOn_posPart (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hwg : HasWeakGradOn Ω u g) :
    HasWeakGradOn Ω (fun x => max (u x) 0) (fun k x => if 0 < u x then g k x else 0) :=
  hasWeakGradOn_of_hasWeakFDerivOn (Ω := ⟨Ω, hΩ⟩)
    ((hasWeakGradOn_iff_hasWeakFDerivOn hΩ hu hg).1 hwg).posPart
    (funext fun x => by by_cases h : 0 < u x <;> simp [gradCLM, h])

/-- **Weak gradient of `(u - c)⁺`.** -/
theorem hasWeakGradOn_posPart_sub_const (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hwg : HasWeakGradOn Ω u g) (c : ℝ) :
    HasWeakGradOn Ω (fun x => max (u x - c) 0) (fun k x => if c < u x then g k x else 0) :=
  hasWeakGradOn_of_hasWeakFDerivOn (Ω := ⟨Ω, hΩ⟩)
    (((hasWeakGradOn_iff_hasWeakFDerivOn hΩ hu hg).1 hwg).sub_const c).posPart
    (funext fun x => by by_cases h : c < u x <;> simp [gradCLM, h, sub_pos])

/-- **Weak gradient of the negative part** (Gilbarg and Trudinger Lemma 7.6, second clause).
`u⁻ = min u 0` has the weak gradient `∇u` where `u < 0` and `0` elsewhere. -/
theorem hasWeakGradOn_negPart (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hwg : HasWeakGradOn Ω u g) :
    HasWeakGradOn Ω (fun x => min (u x) 0) (fun k x => if u x < 0 then g k x else 0) :=
  hasWeakGradOn_of_hasWeakFDerivOn (Ω := ⟨Ω, hΩ⟩)
    ((hasWeakGradOn_iff_hasWeakFDerivOn hΩ hu hg).1 hwg).negPart
    (funext fun x => by by_cases h : u x < 0 <;> simp [gradCLM, h])

/-- **Weak gradient of the absolute value** (Gilbarg and Trudinger Lemma 7.6, third clause).
`|u|` has the weak gradient `∇u` where `u > 0`, `-∇u` where `u < 0`, and `0` elsewhere. -/
theorem hasWeakGradOn_abs (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hwg : HasWeakGradOn Ω u g) :
    HasWeakGradOn Ω (fun x => |u x|)
      fun k x => if 0 < u x then g k x else if u x < 0 then -g k x else 0 :=
  hasWeakGradOn_of_hasWeakFDerivOn (Ω := ⟨Ω, hΩ⟩)
    ((hasWeakGradOn_iff_hasWeakFDerivOn hΩ hu hg).1 hwg).abs
    (funext fun x => by
      rcases lt_trichotomy (u x) 0 with h | h | h
      · simp [gradCLM, h, not_lt.2 h.le, Finset.sum_neg_distrib]
      · simp [gradCLM, h]
      · simp [gradCLM, h])

/-- **Vanishing of the weak gradient on level sets** (Gilbarg and Trudinger Lemma 7.7). On an
open set, the weak gradient of `u` is zero almost everywhere on `{u = c}`. -/
theorem ae_eq_zero_of_eq_const_of_hasWeakGradOn (hΩ : IsOpen Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : LocallyIntegrableOn u Ω volume) (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume)
    (hwg : HasWeakGradOn Ω u g) (c : ℝ) (k : Fin d) :
    ∀ᵐ x ∂(volume.restrict Ω), u x = c → g k x = 0 := by
  filter_upwards [((hasWeakGradOn_iff_hasWeakFDerivOn hΩ hu hg).1 hwg).ae_eq_zero_of_eq_const c]
    with x hx hxc
  simpa using congrArg (fun L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ => L (EuclideanSpace.single k 1))
    (hx hxc)

end EllipticPdes.Embedding
