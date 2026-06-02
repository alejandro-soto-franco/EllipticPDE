import Mathlib.Analysis.FunctionalSpaces.PoincareInequality
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Per-coordinate-direction bound via Fubini (dependency-chain step 2)

Apply the one-dimensional Poincaré inequality (`MeasureTheory.poincare_1d`) on
each coordinate slice of a box and integrate the remaining variables out.

A box `Ω = B ×ˢ (a, b) ⊆ β × ℝ` is integrated over by Fubini as
`∫_Ω f = ∫_{y ∈ B} ∫_{x ∈ (a,b)} f (y, x)`. On each slice `x ↦ f (y, x)` the
one-dimensional Poincaré inequality controls the `L²` norm by the `L²` norm of
the slice derivative `∂_x f`. Integrating that estimate over the remaining
variables `y` gives the per-direction bound on the box.

* `poincare_slice_iterated`: the bound in iterated form, for a general measure
  on the remaining variables. This is the Fubini-decomposed statement.
* `poincare_slice_box`: the same bound written as a single integral over the box
  `B ×ˢ (a, b)`, obtained from the iterated form by Fubini (`setIntegral_prod`).
-/

open MeasureTheory Set intervalIntegral

namespace EllipticDirichlet.Poincare

/-- The per-direction Poincaré bound in iterated form. For a family of
one-dimensional slices `x ↦ Φ y x`, each satisfying the Poincaré hypotheses on
`[a, b]` (a derivative `Φ' y` continuous on `[a, b]`, vanishing at `a`), the
integral over the remaining variables `y` of the slice `L²` norms is bounded by
the same integral of the slice derivative `L²` norms. -/
theorem poincare_slice_iterated
    {β : Type*} [MeasurableSpace β] {ν : Measure β}
    {a b : ℝ} (hab : a ≤ b) {Φ Φ' : β → ℝ → ℝ}
    (hderiv : ∀ y, ∀ x ∈ uIcc a b, HasDerivAt (Φ y) (Φ' y x) x)
    (hcont : ∀ y, ContinuousOn (Φ' y) (uIcc a b))
    (hzero : ∀ y, Φ y a = 0)
    (hg : Integrable (fun y => ∫ x in a..b, (Φ y x) ^ 2) ν)
    (hh : Integrable (fun y => ∫ x in a..b, (Φ' y x) ^ 2) ν) :
    (∫ y, (∫ x in a..b, (Φ y x) ^ 2) ∂ν)
      ≤ (b - a) ^ 2 / 2 * ∫ y, (∫ x in a..b, (Φ' y x) ^ 2) ∂ν := by
  have hslice : (fun y => ∫ x in a..b, (Φ y x) ^ 2)
      ≤ fun y => (b - a) ^ 2 / 2 * ∫ x in a..b, (Φ' y x) ^ 2 :=
    fun y => poincare_1d hab (hderiv y) (hcont y) (hzero y)
  calc (∫ y, (∫ x in a..b, (Φ y x) ^ 2) ∂ν)
      ≤ ∫ y, ((b - a) ^ 2 / 2 * ∫ x in a..b, (Φ' y x) ^ 2) ∂ν :=
        MeasureTheory.integral_mono hg (hh.const_mul _) hslice
    _ = (b - a) ^ 2 / 2 * ∫ y, (∫ x in a..b, (Φ' y x) ^ 2) ∂ν :=
        MeasureTheory.integral_const_mul _ _

/-- The per-direction Poincaré bound on a box `B ×ˢ (a, b) ⊆ β × ℝ`, written as
a single integral over the box. For a function `Φ` whose one-dimensional slices
`x ↦ Φ (y, x)` are `C¹` on `[a, b]` with derivative `∂_x Φ = Φ'` continuous and
`Φ (y, a) = 0`,
`∫_{B ×ˢ (a,b)} Φ² ≤ (b - a)² / 2 * ∫_{B ×ˢ (a,b)} (∂_x Φ)²`.

Fubini (`setIntegral_prod`) reduces both sides to iterated integrals; the
one-dimensional Poincaré inequality bounds each slice; integrating over `B`
gives the result. -/
theorem poincare_slice_box
    {β : Type*} [MeasurableSpace β] {ν : Measure β} [SFinite ν]
    {a b : ℝ} (hab : a ≤ b) {s : Set β} (hs : MeasurableSet s) {Φ Φ' : β × ℝ → ℝ}
    (hderiv : ∀ y, ∀ x ∈ uIcc a b, HasDerivAt (fun t => Φ (y, t)) (Φ' (y, x)) x)
    (hcont : ∀ y, ContinuousOn (fun t => Φ' (y, t)) (uIcc a b))
    (hzero : ∀ y, Φ (y, a) = 0)
    (hΦ2 : IntegrableOn (fun p => (Φ p) ^ 2) (s ×ˢ Ioo a b) (ν.prod volume))
    (hΦ'2 : IntegrableOn (fun p => (Φ' p) ^ 2) (s ×ˢ Ioo a b) (ν.prod volume)) :
    (∫ p in s ×ˢ Ioo a b, (Φ p) ^ 2 ∂(ν.prod volume))
      ≤ (b - a) ^ 2 / 2 * ∫ p in s ×ˢ Ioo a b, (Φ' p) ^ 2 ∂(ν.prod volume) := by
  -- Per-slice Poincaré bound, in `Ioo`-integral form.
  have hslice : ∀ y, (∫ x in Ioo a b, (Φ (y, x)) ^ 2)
      ≤ (b - a) ^ 2 / 2 * ∫ x in Ioo a b, (Φ' (y, x)) ^ 2 := by
    intro y
    have hp := poincare_1d hab (hderiv y) (hcont y) (hzero y)
    rwa [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo] at hp
  -- Marginal integrability of each slice integral, from product integrability.
  have hΦ2' : Integrable (fun p => (Φ p) ^ 2)
      ((ν.restrict s).prod (volume.restrict (Ioo a b))) := by
    rw [Measure.prod_restrict s (Ioo a b)]; exact hΦ2
  have hΦ'2' : Integrable (fun p => (Φ' p) ^ 2)
      ((ν.restrict s).prod (volume.restrict (Ioo a b))) := by
    rw [Measure.prod_restrict s (Ioo a b)]; exact hΦ'2
  have hgI : IntegrableOn (fun y => ∫ x in Ioo a b, (Φ (y, x)) ^ 2) s ν :=
    hΦ2'.integral_prod_left
  have hhI : IntegrableOn (fun y => ∫ x in Ioo a b, (Φ' (y, x)) ^ 2) s ν :=
    hΦ'2'.integral_prod_left
  -- Fubini both sides, then integrate the slice bound over `B`.
  rw [setIntegral_prod _ hΦ2, setIntegral_prod _ hΦ'2]
  calc (∫ y in s, ∫ x in Ioo a b, (Φ (y, x)) ^ 2 ∂volume ∂ν)
      ≤ ∫ y in s, ((b - a) ^ 2 / 2 * ∫ x in Ioo a b, (Φ' (y, x)) ^ 2) ∂ν :=
        setIntegral_mono_on hgI (hhI.const_mul _) hs (fun y _ => hslice y)
    _ = (b - a) ^ 2 / 2 * ∫ y in s, (∫ x in Ioo a b, (Φ' (y, x)) ^ 2) ∂ν :=
        MeasureTheory.integral_const_mul _ _

end EllipticDirichlet.Poincare
