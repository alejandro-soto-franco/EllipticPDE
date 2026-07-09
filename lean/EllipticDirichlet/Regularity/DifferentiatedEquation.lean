/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticDirichlet.Regularity.Interior
import EllipticDirichlet.Regularity.CoeffC2

/-!
# The differentiated-equation integral identity

For `u ∈ H₀¹(Ω)` weakly solving `Lu = f` with `C²` principal coefficients, this file builds
towards the **differentiated-equation integral identity** of Evans, *Partial Differential
Equations* (2nd ed.), §6.3.2, Theorem 4: for a fixed direction `ℓ` and every smooth
compactly-supported test `φ` with `tsupport φ ⊆ V`,

```
∑_{i,j} ∫_V a_{ij} (∂ₖ∂ᵢu) ∂ⱼφ  +  ∑_{i,j} ∫_V (∂_ℓ a_{ij})(∂ᵢu) ∂ⱼφ  =  ∫_V f_ℓ · φ
```

with `f_ℓ` an explicit lower-order datum. The identity is stated in `HasWeakDerivOn`-style
integration by parts on plain `Lp ℝ 2 (volume.restrict V)` classes.

This file starts with the small calculus facts used repeatedly throughout the milestone: the
partial derivative of a smooth (resp. compactly supported) test function is again smooth
(resp. compactly supported), so `∂ⱼφ` is again an admissible `HasWeakDerivOn` test function,
and the pointwise Leibniz rule for `partialD` against a product.
-/

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticDirichlet.Regularity

open EllipticDirichlet.Sobolev

variable {d : ℕ}

/-! ### Test-function calculus -/

/-- The partial derivative of a `C^∞` function is `C^∞`. -/
theorem contDiff_partialD {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (partialD j φ) := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := (contDiff_infty_iff_fderiv.mp hφ).2
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => (fderiv ℝ φ x) (EuclideanSpace.single j 1))
  exact hf.clm_apply (contDiff_const (c := EuclideanSpace.single j (1 : ℝ)))

/-- The partial derivative of a compactly-supported function has compact support. -/
theorem hasCompactSupport_partialD {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : HasCompactSupport φ) (j : Fin d) : HasCompactSupport (partialD j φ) :=
  hφ.mono' ((subset_tsupport (partialD j φ)).trans (tsupport_partialD_subset j φ))

/-- `∂ⱼφ` is again an admissible `HasWeakDerivOn` test function on `V` when `φ` is. -/
theorem isTest_partialD {V : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ)
    (hV : tsupport φ ⊆ V) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (partialD j φ) ∧ HasCompactSupport (partialD j φ)
      ∧ tsupport (partialD j φ) ⊆ V :=
  ⟨contDiff_partialD hc j, hasCompactSupport_partialD hcs j,
    (tsupport_partialD_subset j φ).trans hV⟩

/- The pointwise Leibniz rule for `partialD` against a product already exists as
`partialD_mul` (`Regularity/Caccioppoli.lean`, transitively imported via `Interior`):
`partialD i (fun x => η x * φ x) = fun x => η x * partialD i φ x + partialD i η x * φ x`
for `η, φ` differentiable. It is mathematically the same identity with the two summands
commuted (`add_comm`), so it is reused here rather than redeclared under the same name. -/

end EllipticDirichlet.Regularity
