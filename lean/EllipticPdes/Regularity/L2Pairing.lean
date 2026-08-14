/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Regularity.MulIterated

/-!
# Pairing an `L²` class against a test function

Evans's step 3 of §6.3.1, Theorem 2 assembles a datum out of a dozen products of a coefficient
against a derivative of the solution, and every one of them reaches the statement as an
integral against a test function. Moving between the sum of the integrals and the integral of
the sum is the whole of the bookkeeping, and it is the same three facts each time: the pairing
is additive, it commutes with a finite sum, and a weighted class pairs as the weight times the
class.

Integrability is what makes the moves legal, and it is uniform: an `L²` class against a
continuous compactly supported function is integrable, by Hölder. Every lemma here takes the
test function as smooth with compact support and asks nothing about its support, since none of
these steps localises.

## Main declarations

* `integrable_mul_testFn`: the product of an `L²(V)` class with a test function is integrable.
* `setIntegral_add_mul_testFn`, `setIntegral_sub_mul_testFn`, `setIntegral_neg_mul_testFn`:
  the pairing is additive.
* `setIntegral_finsetSum_mul_testFn`, `setIntegral_sum_mul_testFn`: the pairing commutes with a
  finite sum.
* `setIntegral_mulL2_mul_testFn`: a weighted class pairs as the weight against the class.
-/

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {V : Set (EuclideanSpace ℝ (Fin d))}

/-- **An `L²` class against a test function is integrable.** Hölder with the two exponents `2`
and the continuous compactly supported factor in `L²`. -/
theorem integrable_mul_testFn (F : L2D V) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφc : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcs : HasCompactSupport φ) :
    Integrable (fun x => (F x : ℝ) * φ x) (volume.restrict V) := by
  haveI : ENNReal.HolderTriple (2 : ENNReal) 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  exact (Lp.memLp F).integrable_mul
    ((hφc.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hφcs).restrict V)

/-- The pairing is additive in the class. -/
theorem setIntegral_add_mul_testFn (F G : L2D V) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφc : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcs : HasCompactSupport φ) :
    (∫ x in V, ((F + G) x : ℝ) * φ x)
      = (∫ x in V, (F x : ℝ) * φ x) + ∫ x in V, (G x : ℝ) * φ x := by
  have hcong : (∫ x in V, ((F + G) x : ℝ) * φ x)
      = ∫ x in V, ((F x : ℝ) * φ x + (G x : ℝ) * φ x) := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add F G] with x hx
    rw [hx, Pi.add_apply, add_mul]
  rw [hcong, integral_add (integrable_mul_testFn F hφc hφcs)
    (integrable_mul_testFn G hφc hφcs)]

/-- The pairing subtracts in the class. -/
theorem setIntegral_sub_mul_testFn (F G : L2D V) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφc : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcs : HasCompactSupport φ) :
    (∫ x in V, ((F - G) x : ℝ) * φ x)
      = (∫ x in V, (F x : ℝ) * φ x) - ∫ x in V, (G x : ℝ) * φ x := by
  have hcong : (∫ x in V, ((F - G) x : ℝ) * φ x)
      = ∫ x in V, ((F x : ℝ) * φ x - (G x : ℝ) * φ x) := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub F G] with x hx
    rw [hx, Pi.sub_apply, sub_mul]
  rw [hcong, integral_sub (integrable_mul_testFn F hφc hφcs)
    (integrable_mul_testFn G hφc hφcs)]

/-- The pairing negates in the class. -/
theorem setIntegral_neg_mul_testFn (F : L2D V) (φ : EuclideanSpace ℝ (Fin d) → ℝ) :
    (∫ x in V, ((-F) x : ℝ) * φ x) = -∫ x in V, (F x : ℝ) * φ x := by
  rw [← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_neg F] with x hx
  rw [hx, Pi.neg_apply, neg_mul]

/-- The pairing commutes with a finite sum over a `Finset`. -/
theorem setIntegral_finsetSum_mul_testFn {ι : Type*} (s : Finset ι) (F : ι → L2D V)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) :
    (∫ x in V, ((∑ i ∈ s, F i) x : ℝ) * φ x) = ∑ i ∈ s, ∫ x in V, (F i x : ℝ) * φ x := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    rw [show (∫ x in V, ((0 : L2D V) x : ℝ) * φ x) = 0 from ?_]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volume.restrict V)] with x hx
    rw [hx, Pi.zero_apply, zero_mul]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, setIntegral_add_mul_testFn _ _ hφc hφcs, ih]

/-- The pairing commutes with a finite sum over a `Fintype`. -/
theorem setIntegral_sum_mul_testFn {ι : Type*} [Fintype ι] (F : ι → L2D V)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) :
    (∫ x in V, ((∑ i, F i) x : ℝ) * φ x) = ∑ i, ∫ x in V, (F i x : ℝ) * φ x :=
  setIntegral_finsetSum_mul_testFn Finset.univ F hφc hφcs

/-- A weighted class pairs as the weight against the class. -/
theorem setIntegral_mulL2_mul_testFn {a : EuclideanSpace ℝ (Fin d) → ℝ} (ham : Measurable a)
    {M : ℝ} (haM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |a x| ≤ M) (p : L2D V)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) :
    (∫ x in V, (mulL2 ham haM p x : ℝ) * φ x) = ∫ x in V, a x * (p x : ℝ) * φ x := by
  refine integral_congr_ae ?_
  filter_upwards [mulL2_coeFn ham haM p] with x hx
  rw [hx]

end EllipticPdes.Regularity
