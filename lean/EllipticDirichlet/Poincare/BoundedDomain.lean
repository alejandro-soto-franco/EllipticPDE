import EllipticDirichlet.Poincare.BoxSlice

/-!
# The Poincaré inequality on arbitrary bounded domains (chain step 5)

`BoxSlice.lean` discharges the per-direction slice bound when the domain IS the open
coordinate box. This file removes that restriction: any `Ω` contained in a box inherits
the slice bound, because a test function of `Ω` is a test function of the box
(`IsTestFn.mono`) and the box integrals restrict to `Ω` (the integrands vanish off
`tsupport φ ⊆ Ω`). Averaging (`poincare_testfn`) and density (`poincare_H01`) are already
domain-general, so the Poincaré inequality follows on every bounded domain
(`poincare_H01_of_bounded`), with the closed-form constant `L²/(2(n+1))` from any
bounding box of side `L`. This is the `p = q = 2` Friedrichs case of Guo
Theorem III.4.6; the limit passage that Guo performs by mollification is the
density step `poincare_H01`, which is architectural here because `H₀¹` is defined
as the closure of the test-function graphs.
-/

open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticDirichlet.Poincare

open EllipticDirichlet.Sobolev

variable {n : ℕ}

/-- **The per-direction Poincaré bound for a subset of a box.** A test function of any
`Ω` inside the open box obeys the box slice bound with the integrals taken over `Ω`. -/
theorem slice_bound_of_subset_euclBox {a b : Fin (n + 1) → ℝ} (hab : ∀ k, a k ≤ b k)
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hsub : Ω ⊆ euclBox a b)
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (h : IsTestFn Ω φ) (i : Fin (n + 1)) :
    ∫ x in Ω, (φ x) ^ 2 ≤ (b i - a i) ^ 2 / 2 * ∫ x in Ω, (partialD i φ x) ^ 2 := by
  have hbox : IsTestFn (euclBox a b) φ := h.mono hsub
  -- Both box integrals restrict to `Ω`: the integrands vanish on `euclBox \ Ω`.
  have hφeq : ∫ x in euclBox a b, (φ x) ^ 2 = ∫ x in Ω, (φ x) ^ 2 :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero
      (isOpen_euclBox a b).measurableSet hsub
      (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun hm => hx.2 (h.2.2 hm))]
        ring)
  have hdeq : ∫ x in euclBox a b, (partialD i φ x) ^ 2
      = ∫ x in Ω, (partialD i φ x) ^ 2 :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero
      (isOpen_euclBox a b).measurableSet hsub
      (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport
          (fun hm => hx.2 (((tsupport_partialD_subset i φ).trans h.2.2) hm))]
        ring)
  calc ∫ x in Ω, (φ x) ^ 2
      = ∫ x in euclBox a b, (φ x) ^ 2 := hφeq.symm
    _ ≤ (b i - a i) ^ 2 / 2 * ∫ x in euclBox a b, (partialD i φ x) ^ 2 :=
        slice_bound_euclBox a b hab hbox i
    _ = (b i - a i) ^ 2 / 2 * ∫ x in Ω, (partialD i φ x) ^ 2 := by rw [hdeq]

end EllipticDirichlet.Poincare
