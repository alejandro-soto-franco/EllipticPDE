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

end EllipticDirichlet.Regularity
