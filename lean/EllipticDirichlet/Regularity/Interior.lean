/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticDirichlet.Regularity.RestrictedDiffQuotientMem
import EllipticDirichlet.Regularity.CoeffC1
import EllipticDirichlet.Regularity.CutoffTower

/-!
# The master interior difference-quotient energy estimate

The interior second-derivative estimate (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1; Gilbarg-Trudinger, *Elliptic PDE of Second Order*, Theorem 8.8) proceeds by testing
the weak formulation of `L u = f` with the difference-quotient test element
`v_h = -Dₖ^{-h}(ξ² Dₖ^h u)`, using discrete integration by parts to move the outer difference
quotient onto the coefficient factor, uniform ellipticity from below to control the leading
term, and Cauchy-Schwarz together with the Peter-Paul (Young) inequality to absorb the
commutator, cross, zeroth-order, and right-hand terms.

## Main declarations

* `evansTest`: the admissible test element `v_h = -Dₖ^{-h}(ξ² Dₖ^h u) ∈ H₀¹(Ω)`, whose
  membership is two applications of `cutoffMul_diffQuotG_mem_H01`.
-/

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticDirichlet.Regularity

open EllipticDirichlet.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
  {ξ θ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ### D1: The admissible Evans test element -/

/-- **The admissible Evans test element** `v_h = -Dₖ^{-h}(ξ² Dₖ^h u) ∈ H₀¹(Ω)`. The inner
cutoff `ξ²` and the outer cutoff `θ` (which is `≡ 1` on `tsupport ξ`) localise the two
difference quotients so that the composite stays inside `H₀¹(Ω)`; membership is two
applications of the crux admissibility lemma `cutoffMul_diffQuotG_mem_H01`, together with
closure of the submodule under negation. This is the single admissible test vector that the
weak formulation consumes in the difference-quotient energy method (Evans, *Partial
Differential Equations* (2nd ed.), §6.3.1). -/
noncomputable def evansTest (hΩm : MeasurableSet Ω) (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ)
    (k : Fin d) (h : ℝ)
    (hsm_in : ∀ x ∈ tsupport (fun y => ξ y * ξ y), x + hshift k h ∈ Ω)
    (hsm_out : ∀ x ∈ tsupport θ, x + hshift k (-h) ∈ Ω) (u : H01 Ω) : H01 Ω :=
  ⟨-(cutoffMul hθ (diffQuotG k (-h) hΩm
      (cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))))),
    Submodule.neg_mem _
      (cutoffMul_diffQuotG_mem_H01 hθ k hΩm hsm_out
        (cutoffMul_diffQuotG_mem_H01 (isTestFn_mul hξ hξ) k hΩm hsm_in u.2))⟩

/-- The ambient-graph value of `evansTest` is the negated cutoff of the outer difference
quotient of `ξ² Dₖ^h u`. -/
theorem evansTest_coe (hΩm : MeasurableSet Ω) (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ)
    (k : Fin d) (h : ℝ)
    (hsm_in : ∀ x ∈ tsupport (fun y => ξ y * ξ y), x + hshift k h ∈ Ω)
    (hsm_out : ∀ x ∈ tsupport θ, x + hshift k (-h) ∈ Ω) (u : H01 Ω) :
    (evansTest hΩm hξ hθ k h hsm_in hsm_out u : H1amb Ω)
      = -(cutoffMul hθ (diffQuotG k (-h) hΩm
          (cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))))) :=
  rfl

/-! ### D2 core: support control and θ-invisibility -/

/-- A cutoff-multiplied class vanishes a.e. off the topological support of the cutoff. -/
private lemma mulTest_ae_eq_zero_off_tsupport {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hη : IsTestFn Ω η) (g : L2D Ω) :
    ∀ᵐ x ∂(volume.restrict Ω),
      x ∉ tsupport η → (mulTest hη g x : ℝ) = 0 := by
  filter_upwards [mulTest_coeFn hη g] with x hx hxns
  rw [hx, image_eq_zero_of_notMem_tsupport hxns, zero_mul]

/-- **Support of the interior difference quotient.** If a class `g` has whole-space extension
a.e. supported in a measurable set `S`, then its interior difference quotient `diffQuotD k h g`
vanishes (a.e. on `Ω`) outside `S ∪ (S - h eₖ)`: the numerator
`extendL2 g (x + h eₖ) - g x` can be nonzero only when `x ∈ S` (through `g x`) or
`x + h eₖ ∈ S` (through the translate). -/
private lemma diffQuotD_ae_eq_zero_off (hΩm : MeasurableSet Ω) (k : Fin d) {h : ℝ}
    (g : L2D Ω) {S : Set (EuclideanSpace ℝ (Fin d))}
    (hgS : ∀ᵐ x ∂volume, (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) x ≠ 0 → x ∈ S) :
    ∀ᵐ x ∂(volume.restrict Ω),
      x ∉ S → x + hshift k h ∉ S → (diffQuotD k h hΩm g x : ℝ) = 0 := by
  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving (· + hshift k h) volume volume :=
    (measurePreserving_add_right volume (hshift k h)).quasiMeasurePreserving
  have hgS_shift : ∀ᵐ x ∂volume,
      (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) (x + hshift k h) ≠ 0 →
        x + hshift k h ∈ S := hqmp.ae hgS
  filter_upwards [coeFn_diffQuotD k h hΩm g, ae_restrict_of_ae hgS,
    ae_restrict_of_ae hgS_shift, ae_restrict_of_ae (coeFn_extendL2 hΩm g),
    ae_restrict_mem hΩm] with x hdq hgx hgxs hext hmem hxS hxsS
  rw [hdq]
  have h1 : (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) (x + hshift k h) = 0 := by
    by_contra hne; exact hxsS (hgxs hne)
  have h2 : (g x : ℝ) = 0 := by
    by_contra hne
    refine hxS (hgx ?_)
    rw [hext, Set.indicator_of_mem hmem]; exact hne
  rw [h1, h2, sub_zero, zero_div]

/-! ### D2 core: discrete integration by parts -/

/-- **Discrete integration by parts, principal term.** For a class `p` whose whole-space
extension stays supported inside `Ω` after the backward shift, the restricted-domain pairing
of the coefficient action against the backward interior difference quotient of `p` transfers,
via the extension isometry and the whole-space adjoint relation `diffQuot_inner_adjoint`,
into minus the whole-space pairing of the *forward* difference quotient of the coefficient
action against `extendL2 p`. This is the discrete analogue of moving the derivative off the
test factor onto the coefficient factor (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1, proof of Theorem 3). -/
private lemma actL_diffQuotD_ibp (A : EllipticCoeff d) (hΩm : MeasurableSet Ω)
    (i j k : Fin d) {h : ℝ} (g p : L2D Ω)
    (hsupp : ∀ᵐ x ∂volume,
      (extendL2 hΩm p : EuclideanSpace ℝ (Fin d) → ℝ) (x + hshift k (-h)) ≠ 0 → x ∈ Ω) :
    ⟪A.actL i j g, diffQuotD k (-h) hΩm p⟫
      = -⟪diffQuot k h (extendL2 hΩm (A.actL i j g)), extendL2 hΩm p⟫ := by
  rw [← (extendL2 hΩm).inner_map_map (A.actL i j g) (diffQuotD k (-h) hΩm p),
    extendL2_diffQuotD_eq k (-h) hΩm p hsupp,
    diffQuot_inner_adjoint k h (extendL2 hΩm (A.actL i j g)) (extendL2 hΩm p)]
  exact (neg_neg _).symm

end EllipticDirichlet.Regularity
