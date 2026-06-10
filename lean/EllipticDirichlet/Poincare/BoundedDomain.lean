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

/-- **The Poincaré inequality on `H₀¹(Ω)` for `Ω` inside a box** with sides at most `L`:
`‖U₀‖² ≤ L²/(2(n+1)) · ∑ᵢ ‖Uᵢ‖²`. -/
theorem poincare_H01_of_subset_euclBox {a b : Fin (n + 1) → ℝ} (hab : ∀ k, a k ≤ b k)
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hsub : Ω ⊆ euclBox a b)
    {L : ℝ} (hL : ∀ i, b i - a i ≤ L)
    {U : H1amb Ω} (hU : U ∈ H01 Ω) :
    ‖U 0‖ ^ 2 ≤ L ^ 2 / (2 * (n + 1)) * ∑ i : Fin (n + 1), ‖U i.succ‖ ^ 2 := by
  have hL0 : 0 ≤ L := le_trans (sub_nonneg.mpr (hab 0)) (hL 0)
  have hslice : ∀ {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
      (h : IsTestFn Ω φ) (i : Fin (n + 1)),
      ∫ x in Ω, (φ x) ^ 2 ≤ L ^ 2 / 2 * ∫ x in Ω, (partialD i φ x) ^ 2 := by
    intro φ h i
    refine le_trans (slice_bound_of_subset_euclBox hab hsub h i)
      (mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun x => sq_nonneg _))
    have hside : (b i - a i) ^ 2 ≤ L ^ 2 := by
      have h1 : 0 ≤ b i - a i := sub_nonneg.mpr (hab i)
      nlinarith [hL i]
    linarith
  have h := poincare_H01 (Ω := Ω) _
    (fun {_φ} hφ => poincare_testfn (Nat.succ_pos n) (L ^ 2 / 2)
      (fun {_ψ} h' i => hslice h' i) hφ) hU
  refine le_trans h (le_of_eq ?_)
  rw [div_div]
  norm_cast

/-- The test-function instance, in the slice-constant form the coercivity layer
consumes. Derived FROM `poincare_H01_of_subset_euclBox` (test graphs lie in `H₀¹`). -/
theorem testfn_bound_of_subset_euclBox {a b : Fin (n + 1) → ℝ} (hab : ∀ k, a k ≤ b k)
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hsub : Ω ⊆ euclBox a b)
    {C : ℝ} (hC : ∀ i, (b i - a i) ^ 2 / 2 ≤ C)
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (h : IsTestFn Ω φ) :
    ‖(h.testGraph 0 : L2D Ω)‖ ^ 2
      ≤ C / (n + 1) * ∑ i : Fin (n + 1), ‖h.testGraph i.succ‖ ^ 2 := by
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  have h2C : (0 : ℝ) ≤ 2 * C := by linarith
  have hL : ∀ i, b i - a i ≤ Real.sqrt (2 * C) := by
    intro i
    have h1 : 0 ≤ b i - a i := sub_nonneg.mpr (hab i)
    have h2 : (b i - a i) ^ 2 ≤ 2 * C := by linarith [hC i]
    calc b i - a i = Real.sqrt ((b i - a i) ^ 2) := (Real.sqrt_sq h1).symm
      _ ≤ Real.sqrt (2 * C) := Real.sqrt_le_sqrt h2
  have hmem : h.testGraph ∈ H01 Ω :=
    (Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨φ, h, rfl⟩)
  have hp := poincare_H01_of_subset_euclBox hab hsub hL hmem
  rw [Real.sq_sqrt h2C] at hp
  refine le_trans hp (le_of_eq ?_)
  rw [mul_div_mul_left C ((n : ℝ) + 1) two_ne_zero]

end EllipticDirichlet.Poincare
