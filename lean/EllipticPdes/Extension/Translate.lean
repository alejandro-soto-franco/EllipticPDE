/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.Reflect
public import EllipticPdes.Extension.Basic

/-!
# Translation of a weak gradient

Translation is measure preserving and has the identity as derivative, so it moves a weak gradient
with no sign and no Jacobian.

## Main declarations

* `EllipticPdes.Extension.partialD_comp_translate`: the partial derivatives of a translate.
* `EllipticPdes.Extension.hasWeakGradOn_comp_translate`: the weak gradient of a translate.
* `EllipticPdes.Extension.eLpNorm_comp_translate`: translation preserves every `Lᵖ` seminorm.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.3.3, Theorem 3.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev EllipticPdes.Embedding

variable {d : ℕ}

/-! ### The translation -/

/-! ### Derivatives and supports -/

/-- **Partial derivatives of a translate.** Translation has derivative the identity, so a
partial derivative translates with no factor. -/
theorem partialD_comp_translate {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : Differentiable ℝ φ)
    (h : EuclideanSpace ℝ (Fin d)) (k : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    partialD k (fun y => φ (y + h)) x = partialD k φ (x + h) := by
  simpa [partialD] using partialD_comp (f := fun y => y + h) (hφ _)
    ((hasFDerivAt_id x).add_const h) k

/-! ### The weak gradient of a translate -/

/-- **Translation of a weak gradient.** If `u` has weak gradient `g` on `B`, then `u(· + h)` has
weak gradient `k ↦ gₖ(· + h)` on the preimage of `B` under the translation. -/
theorem hasWeakGradOn_comp_translate {B : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hw : HasWeakGradOn B u g) (h : EuclideanSpace ℝ (Fin d)) :
    HasWeakGradOn ((fun y : EuclideanSpace ℝ (Fin d) => y + h) ⁻¹' B)
      (fun y => u (y + h)) (fun k y => g k (y + h)) := by
  rw [hasWeakGradOn_iff] at hw ⊢
  exact fun k => by
    simpa using (hw k).comp_affine (ContinuousLinearEquiv.refl ℝ _) h
      (measurePreserving_add_right volume h)

/-- **Translation preserves every `Lᵖ` seminorm.** -/
theorem eLpNorm_comp_translate {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : AEStronglyMeasurable f volume) (h : EuclideanSpace ℝ (Fin d)) (p : ℝ≥0∞) :
    eLpNorm (fun y => f (y + h)) p volume = eLpNorm f p volume :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_add_right volume h)

end EllipticPdes.Extension
