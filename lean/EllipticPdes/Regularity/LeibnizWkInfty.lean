/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Regularity.MollifyWkInfty
import EllipticPdes.Regularity.Interior
import EllipticPdes.Regularity.Caccioppoli

/-!
# The Leibniz rule for a `W^{1,∞}` weight

`EllipticPdes.Regularity.HasWeakDerivOn.mul_contDiff_left` proves the weak-derivative product
rule for a `C¹` weight. Guo's hypothesis supplies no classical derivative, and this file
replaces that route.

## The smooth case is free

For a weight that is already `C^∞`, no mollification is needed at all and no product rule for
weak derivatives has to be proved: `b · φ` is itself a smooth compactly supported test function
supported where `φ` is, so it may be fed straight to `HasWeakDerivOn`, and the classical
Leibniz rule splits the result. That is `weakDerivOn_smul_test_contDiff` below, and it is the
whole content of the mollified stage.

## Where the weak hypothesis enters

The mollification `a ⋆ ρ_ε` of a `W^{1,∞}` weight is `C^∞`, uniformly bounded by the essential
bound of `a` (`abs_convolution_le_of_measurable`), and its derivative is the mollification of
the weak derivative (`partialD_convolution_eq_of_hasWeakPartial`), so it is uniformly bounded
by the essential bound of `a'`. Feeding it to the smooth case gives the identity for every `ε`,
and what remains is to pass to the limit.

## Main declarations

* `weakDerivOn_smul_test_contDiff`: the identity for a `C^∞` weight, with no mollification.
-/

open MeasureTheory
open scoped Topology ENNReal Convolution

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- A continuous compactly supported function is in `L²` of any restricted Lebesgue measure. -/
theorem memLp_two_restrict_of_continuous_hasCompactSupport
    {V : Set (EuclideanSpace ℝ (Fin d))} {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : Continuous h) (hcs : HasCompactSupport h) :
    MemLp h 2 (volume.restrict V) :=
  (hc.memLp_of_hasCompactSupport (μ := volume) hcs).restrict V

/-- **The Leibniz identity for a `C^∞` weight.** If `g` has weak `ℓ`-derivative `g'` on `V` and
`b` is smooth, then for every test function `φ` supported in `V`,

`∫_V g · (b · ∂_ℓφ) = - ∫_V (g' · b + g · ∂_ℓ b) · φ`.

No mollification and no product rule for weak derivatives is involved: `b · φ` is a smooth
compactly supported test function supported inside `V`, so `HasWeakDerivOn` applies to it
directly, and the classical Leibniz rule splits the derivative of the product. -/
theorem weakDerivOn_smul_test_contDiff {V : Set (EuclideanSpace ℝ (Fin d))} (ℓ : Fin d)
    {g g' : Lp ℝ 2 (volume.restrict V)} (hg : HasWeakDerivOn V ℓ g g')
    {b : EuclideanSpace ℝ (Fin d) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    ∫ x in V, (g x : ℝ) * (b x * partialD ℓ φ x)
      = - ∫ x in V, ((g' x : ℝ) * b x + (g x : ℝ) * partialD ℓ b x) * φ x := by
  have hbd : Differentiable ℝ b := hb.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφc.differentiable (by simp)
  -- `b · φ` is a test function supported where `φ` is.
  have hbφ_cd : ContDiff ℝ (⊤ : ℕ∞) (fun x => b x * φ x) := hb.mul hφc
  have hbφ_cs : HasCompactSupport (fun x => b x * φ x) := hφcs.mul_left
  have hbφ_V : tsupport (fun x => b x * φ x) ⊆ V :=
    Set.Subset.trans (closure_mono (Function.support_mul_subset_right b φ)) hφV
  have key := hg _ hbφ_cd hbφ_cs hbφ_V
  rw [partialD_mul hbd hφd ℓ] at key
  -- Both halves of the split integrand are `L¹(V)`: `g` is `L²` and each cofactor is
  -- continuous with compact support, hence `L²` on the restriction.
  have hcont_bdφ : Continuous (fun x => b x * partialD ℓ φ x) :=
    hb.continuous.mul ((hφc.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hcs_bdφ : HasCompactSupport (fun x => b x * partialD ℓ φ x) :=
    (hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single ℓ 1)).mul_left
  have hcont_dbφ : Continuous (fun x => partialD ℓ b x * φ x) :=
    ((hb.continuous_fderiv (by simp)).clm_apply continuous_const).mul hφc.continuous
  have hcs_dbφ : HasCompactSupport (fun x => partialD ℓ b x * φ x) := hφcs.mul_left
  have hint1 : Integrable (fun x => (g x : ℝ) * (b x * partialD ℓ φ x))
      (volume.restrict V) :=
    (Lp.memLp g).integrable_mul
      (memLp_two_restrict_of_continuous_hasCompactSupport hcont_bdφ hcs_bdφ)
  have hint2 : Integrable (fun x => (g x : ℝ) * (partialD ℓ b x * φ x))
      (volume.restrict V) :=
    (Lp.memLp g).integrable_mul
      (memLp_two_restrict_of_continuous_hasCompactSupport hcont_dbφ hcs_dbφ)
  have hsplit : ∫ x in V, (g x : ℝ) * (b x * partialD ℓ φ x + partialD ℓ b x * φ x)
      = (∫ x in V, (g x : ℝ) * (b x * partialD ℓ φ x))
        + ∫ x in V, (g x : ℝ) * (partialD ℓ b x * φ x) := by
    rw [← integral_add hint1 hint2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hsplit] at key
  -- Reassemble the right-hand side into one integrand.
  have hintR1 : Integrable (fun x => (g' x : ℝ) * (b x * φ x)) (volume.restrict V) :=
    (Lp.memLp g').integrable_mul
      (memLp_two_restrict_of_continuous_hasCompactSupport
        (hb.continuous.mul hφc.continuous) hbφ_cs)
  have hcollect : ∫ x in V, ((g' x : ℝ) * b x + (g x : ℝ) * partialD ℓ b x) * φ x
      = (∫ x in V, (g' x : ℝ) * (b x * φ x))
        + ∫ x in V, (g x : ℝ) * (partialD ℓ b x * φ x) := by
    rw [← integral_add hintR1 hint2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hcollect]
  linarith [key]

end EllipticPdes.Regularity
