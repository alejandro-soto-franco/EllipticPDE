/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.WeakGradient
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Uniqueness of the weak gradient on an open set

Two weak gradients of one function differ by a function orthogonal to every test function, and
on an open set the fundamental lemma of the calculus of variations kills it. Mathlib has the
lemma as `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`.

Uniqueness is what lets separate structures be assembled into one family. Higher interior
regularity is proved order by order, so a solution with derivatives of every order arrives as one
family per order, with nothing relating them; uniqueness identifies the entries they share, and
a single family closed under differentiation follows.

## Main declarations

* `EllipticPdes.Embedding.hasWeakGradOn_unique_ae_of_locallyIntegrableOn`: two locally
  integrable weak gradients of one function agree almost everywhere on an open set.
* `EllipticPdes.Embedding.hasWeakGradOn_unique_ae`: the same for gradients integrable on a ball.
-/

@[expose] public section

open MeasureTheory Set Metric

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- **Integrability against a test factor.** A locally integrable class on a set, times a
continuous function with compact support inside the set, is integrable on the whole space. -/
theorem integrable_mul_of_locallyIntegrableOn {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : LocallyIntegrableOn u Ω volume) {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : Continuous h) (hcs : HasCompactSupport h) (hs : tsupport h ⊆ Ω) :
    Integrable (fun x => u x * h x) volume := by
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
  have hK : IntegrableOn u (tsupport h) volume := hu.integrableOn_compact_subset hs hcs
  have hprod : IntegrableOn (fun x => u x * h x) (tsupport h) volume :=
    integrableOn_mul_bounded hK hc hC
  exact (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right u h).trans (subset_tsupport h))).mp hprod

/-- **Uniqueness of the weak gradient on an open set**, with local integrability. -/
theorem hasWeakGradOn_unique_ae_of_locallyIntegrableOn
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g g' : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume)
    (hg' : ∀ k, LocallyIntegrableOn (g' k) Ω volume)
    (h : HasWeakGradOn Ω u g) (h' : HasWeakGradOn Ω u g') (k : Fin d) :
    g k =ᵐ[volume.restrict Ω] g' k := by
  have hloc : LocallyIntegrableOn (fun x => g k x - g' k x) Ω volume := (hg k).sub (hg' k)
  have key : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → ∫ x, φ x • (g k x - g' k x) ∂volume = 0 := by
    intro φ hφc hφcs hφB
    have hcompl : ∀ x ∉ Ω, φ x • (g k x - g' k x) = 0 := by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport fun hc => hx (hφB hc), zero_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hcompl]
    have hgg' : ∫ x in Ω, g k x * φ x = ∫ x in Ω, g' k x * φ x := by
      have h1 := h φ hφc hφcs hφB k
      have h2 := h' φ hφc hφcs hφB k
      linarith [h1, h2]
    have hsplit : ∫ x in Ω, φ x • (g k x - g' k x)
        = (∫ x in Ω, g k x * φ x) - ∫ x in Ω, g' k x * φ x := by
      rw [← integral_sub
        (integrable_mul_of_locallyIntegrableOn (hg k) hφc.continuous hφcs hφB).integrableOn
        (integrable_mul_of_locallyIntegrableOn (hg' k) hφc.continuous hφcs hφB).integrableOn]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [smul_eq_mul]; ring)
    rw [hsplit, hgg', sub_self]
  have hzero := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    fun φ hφc hφcs hφB => key φ (by exact_mod_cast hφc) hφcs hφB
  filter_upwards [ae_restrict_of_ae hzero, ae_restrict_mem hΩ.measurableSet] with x hx hxB
  have := hx hxB
  linarith

/-! ### The chain rule -/

/-- **Uniqueness of the weak gradient on an open set.** Two weak gradients of the same function
agree almost everywhere, given integrability on the set. -/
theorem hasWeakGradOn_unique_ae {B : Set (EuclideanSpace ℝ (Fin d))} (hBo : IsOpen B)
    (_hBm : MeasurableSet B) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g g' : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : ∀ k, IntegrableOn (g k) B volume) (hg' : ∀ k, IntegrableOn (g' k) B volume)
    (h : HasWeakGradOn B u g) (h' : HasWeakGradOn B u g') (k : Fin d) :
    g k =ᵐ[volume.restrict B] g' k :=
  hasWeakGradOn_unique_ae_of_locallyIntegrableOn hBo (fun k => (hg k).locallyIntegrableOn)
    (fun k => (hg' k).locallyIntegrableOn) h h' k

end EllipticPdes.Embedding
