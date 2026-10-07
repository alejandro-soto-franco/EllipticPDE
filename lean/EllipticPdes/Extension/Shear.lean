/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.C1Test
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Shear of a `C¹` boundary chart

A bounded domain with `C¹` boundary is, near a boundary point and after a rotation, the region
above the graph of a `C¹` function `γ` of the remaining coordinates. The map that flattens the
boundary is the shear `y ↦ y + γ(y) • n` along a vector `n`, whose inverse is the shear by `-γ`
when `γ` is constant along `n`, and whose derivative is the identity plus a rank-one map that
annihilates its own direction. Its determinant is therefore `1`, so it preserves every additive
Haar measure and the change of variables leaves every integral unchanged.

The results are stated for a vector `n` in any finite-dimensional real normed space with an
additive Haar measure (`shearBy`, `IndepAlong`). The coordinate shear `shear j` is `shearBy` along
the `j`-th basis vector of `EuclideanSpace ℝ (Fin d)`.

## Main declarations

* `EllipticPdes.Extension.shearBy`: the shear along a vector.
* `EllipticPdes.Extension.measurePreserving_shearBy`: it preserves every additive Haar measure.
* `EllipticPdes.Extension.fderiv_comp_shearBy`: the chain rule through it.
* `EllipticPdes.Extension.shear`: the map along a coordinate axis.
* `EllipticPdes.Extension.shear_shear_neg`: the shear by `-γ` inverts it.
* `EllipticPdes.Extension.det_shearDeriv`: the derivative has determinant `1`.
* `EllipticPdes.Extension.shearHomeomorph`: the shear as a homeomorphism of the whole space.
* `EllipticPdes.Extension.measurePreserving_shear`: the shear preserves Lebesgue measure.
* `EllipticPdes.Extension.partialD_comp_shear`: the chain rule through a shear.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4, and §C.1 for the boundary chart.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev (partialD)

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Shear along a vector.** The point `y` moves along `n` by `γ y`. -/
def shearBy (n : E) (γ : E → ℝ) (y : E) : E := y + γ y • n

/-- `γ` is constant along the direction `n`, which is what makes the shear along `n`
invertible by a shear and its derivative nilpotent. -/
def IndepAlong (n : E) (γ : E → ℝ) : Prop := ∀ (y : E) (t : ℝ), γ (y + t • n) = γ y

/-- **Inversion of the shear by `γ`.** -/
theorem shearBy_shearBy_neg {n : E} {γ : E → ℝ} (hind : IndepAlong n γ) (y : E) :
    shearBy n (fun z => -γ z) (shearBy n γ y) = y := by
  simp only [shearBy, hind y (γ y)]
  module

/-- **Inversion of the shear by `-γ`.** -/
theorem shearBy_neg_shearBy {n : E} {γ : E → ℝ} (hind : IndepAlong n γ) (y : E) :
    shearBy n γ (shearBy n (fun z => -γ z) y) = y := by
  simp only [shearBy]
  rw [hind y (-γ y)]
  module

/-- The shear is a bijection of the whole space. -/
theorem bijective_shearBy {n : E} {γ : E → ℝ} (hind : IndepAlong n γ) :
    Function.Bijective (shearBy n γ) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨shearBy n (fun z => -γ z), shearBy_shearBy_neg hind, shearBy_neg_shearBy hind⟩

/-- Negating a chart preserves constancy along `n`. -/
theorem IndepAlong.neg {n : E} {γ : E → ℝ} (hind : IndepAlong n γ) :
    IndepAlong n fun z => -γ z := fun y t => by
  change -γ (y + t • n) = -γ y
  rw [hind y t]

/-- **Vanishing derivative along `n` of a function constant along `n`.** -/
theorem fderiv_apply_eq_zero_of_indepAlong {n : E} {γ : E → ℝ} (hγ : Differentiable ℝ γ)
    (hind : IndepAlong n γ) (y : E) : fderiv ℝ γ y n = 0 := by
  rw [← (hγ y).lineDeriv_eq_fderiv, lineDeriv,
    show (fun t : ℝ => γ (y + t • n)) = fun _ => γ y from funext (hind y), deriv_const]

/-- The derivative of the shear: the identity plus a rank-one map in the direction `n`. -/
def shearDerivBy (n : E) (γ : E → ℝ) (y : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + (fderiv ℝ γ y).smulRight n

/-- **Derivative of the shear.** -/
theorem hasFDerivAt_shearBy {n : E} {γ : E → ℝ} (hγ : Differentiable ℝ γ) (y : E) :
    HasFDerivAt (shearBy n γ) (shearDerivBy n γ y) y :=
  (hasFDerivAt_id y).add (((hγ y).hasFDerivAt).smul_const n)

/-- The shear is continuous when the chart is. -/
theorem continuous_shearBy {n : E} {γ : E → ℝ} (hγ : Continuous γ) : Continuous (shearBy n γ) :=
  continuous_id.add (hγ.smul continuous_const)

/-- The shear is `C^k` when the chart is. -/
theorem contDiff_shearBy {n : E} {γ : E → ℝ} {k : ℕ∞} (hγ : ContDiff ℝ k γ) :
    ContDiff ℝ k (shearBy n γ) :=
  contDiff_id.add (hγ.smul contDiff_const)

/-- **Shear as a homeomorphism of the whole space**, inverted by the shear by `-γ`. -/
def shearHomeomorphBy {n : E} {γ : E → ℝ} (hγ : Continuous γ) (hind : IndepAlong n γ) :
    E ≃ₜ E where
  toFun := shearBy n γ
  invFun := shearBy n fun z => -γ z
  left_inv := shearBy_shearBy_neg hind
  right_inv := shearBy_neg_shearBy hind
  continuous_toFun := continuous_shearBy hγ
  continuous_invFun := continuous_shearBy hγ.neg

/-- **Derivative through a shear.** The derivative of the shear is the identity plus a rank-one
map in the direction `n`, so the derivative of a composition adds to the derivative of the outer
function the derivative of the chart times its derivative along `n`. -/
theorem fderiv_comp_shearBy {n : E} {γ φ : E → ℝ} (hγ : Differentiable ℝ γ)
    (hφ : Differentiable ℝ φ) (y : E) :
    fderiv ℝ (fun z => φ (shearBy n γ z)) y
      = fderiv ℝ φ (shearBy n γ y) + fderiv ℝ φ (shearBy n γ y) n • fderiv ℝ γ y := by
  change fderiv ℝ (φ ∘ shearBy n γ) y = _
  rw [((hφ _).hasFDerivAt.comp y (hasFDerivAt_shearBy hγ y)).fderiv]
  ext v
  simp [shearDerivBy]
  ring

end General

section Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] in
/-- The shear is a measurable embedding, being a homeomorphism. -/
theorem measurableEmbedding_shearBy {n : E} {γ : E → ℝ} (hγ : Continuous γ)
    (hind : IndepAlong n γ) : MeasurableEmbedding (shearBy n γ) :=
  (shearHomeomorphBy hγ hind).measurableEmbedding

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Determinant `1` of the shear derivative.** It is the identity plus a rank-one map that
annihilates its own direction. -/
theorem det_shearDerivBy {n : E} {γ : E → ℝ} (hγ : Differentiable ℝ γ) (hind : IndepAlong n γ)
    (y : E) : (shearDerivBy n γ y).det = 1 := by
  have h := LinearMap.det_id_add_smulRight (fderiv ℝ γ y : E →ₗ[ℝ] ℝ) n
  simpa [ContinuousLinearMap.det, shearDerivBy, fderiv_apply_eq_zero_of_indepAlong hγ hind y]
    using h

/-- **Preservation of Haar measure by a shear.** Its inverse is the shear by `-γ`, whose
derivative has determinant `1`, so the image of a measurable set has the measure of the set. -/
theorem measurePreserving_shearBy {n : E} {γ : E → ℝ} (hγ : Differentiable ℝ γ)
    (hind : IndepAlong n γ) : MeasurePreserving (shearBy n γ) μ μ := by
  have hcont : Continuous (shearBy n γ) := continuous_shearBy hγ.continuous
  refine ⟨hcont.measurable, Measure.ext fun s hs => ?_⟩
  have hpre : shearBy n γ ⁻¹' s = shearBy n (fun z => -γ z) '' s :=
    (congrFun (shearHomeomorphBy hγ.continuous hind).image_symm s).symm
  have hnd : Differentiable ℝ fun z => -γ z := hγ.neg
  rw [Measure.map_apply hcont.measurable hs, hpre,
    ← lintegral_abs_det_fderiv_eq_addHaar_image μ hs
      (fun x _ => (hasFDerivAt_shearBy hnd x).hasFDerivWithinAt)
      (bijective_shearBy hind.neg).injective.injOn]
  simp [det_shearDerivBy hnd hind.neg]

end Measure

variable {d : ℕ}

/-- **Shear of a boundary chart.** The point `y` moves along the `j`-th axis by `γ y`. -/
def shear (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  y + γ y • EuclideanSpace.single j (1 : ℝ)

/-- `γ` does not depend on the `j`-th coordinate, which is what makes the shear invertible by a
shear and its derivative nilpotent. -/
def IndepCoord (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  IndepAlong (EuclideanSpace.single j (1 : ℝ)) γ

/-- **Inversion of the shear by `γ`.** -/
theorem shear_shear_neg {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hind : IndepCoord j γ)
    (y : EuclideanSpace ℝ (Fin d)) : shear j (fun z => -γ z) (shear j γ y) = y :=
  shearBy_shearBy_neg hind y

/-- **Inversion of the shear by `-γ`.** -/
theorem shear_neg_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hind : IndepCoord j γ)
    (y : EuclideanSpace ℝ (Fin d)) : shear j γ (shear j (fun z => -γ z) y) = y :=
  shearBy_neg_shearBy hind y

/-- The shear is a bijection of the whole space. -/
theorem bijective_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hind : IndepCoord j γ) :
    Function.Bijective (shear j γ) :=
  bijective_shearBy hind

/-- **Vanishing `j`-th partial of a function independent of that coordinate.** -/
theorem partialD_eq_zero_of_indepCoord {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) (y : EuclideanSpace ℝ (Fin d)) :
    partialD j γ y = 0 :=
  fderiv_apply_eq_zero_of_indepAlong hγ hind y

/-- The derivative of the shear: the identity plus a rank-one map in the direction `eⱼ`. -/
def shearDeriv (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))
    + (fderiv ℝ γ y).smulRight (EuclideanSpace.single j (1 : ℝ))

/-- **Determinant `1` of the shear derivative.** It is the identity plus a rank-one map that
annihilates its own direction. -/
theorem det_shearDeriv {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) (y : EuclideanSpace ℝ (Fin d)) :
    (shearDeriv j γ y).det = 1 :=
  det_shearDerivBy hγ hind y

/-- The shear is continuous when the chart is. -/
theorem continuous_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hγ : Continuous γ) :
    Continuous (shear j γ) :=
  continuous_shearBy hγ

/-- The shear is `C^n` when the chart is. -/
theorem contDiff_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} {n : ℕ∞}
    (hγ : ContDiff ℝ n γ) : ContDiff ℝ n (shear j γ) :=
  contDiff_shearBy hγ

/-- Negating a chart preserves independence of the `j`-th coordinate. -/
theorem IndepCoord.neg {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hind : IndepCoord j γ) :
    IndepCoord j fun z => -γ z :=
  IndepAlong.neg hind

/-- **Shear as a homeomorphism of the whole space**, inverted by the shear by `-γ`. -/
def shearHomeomorph {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hγ : Continuous γ)
    (hind : IndepCoord j γ) : EuclideanSpace ℝ (Fin d) ≃ₜ EuclideanSpace ℝ (Fin d) where
  toFun := shear j γ
  invFun := shear j fun z => -γ z
  left_inv := shear_shear_neg hind
  right_inv := shear_neg_shear hind
  continuous_toFun := continuous_shear hγ
  continuous_invFun := continuous_shear hγ.neg

/-- The shear is a measurable embedding, being a homeomorphism. -/
theorem measurableEmbedding_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Continuous γ) (hind : IndepCoord j γ) : MeasurableEmbedding (shear j γ) :=
  measurableEmbedding_shearBy hγ hind

/-- **Preservation of Lebesgue measure by a shear.** -/
theorem measurePreserving_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) :
    MeasurePreserving (shear j γ) volume volume :=
  measurePreserving_shearBy hγ hind

/-- **Partial derivatives through a shear.** A partial derivative of a composition adds to the
corresponding partial of the outer function the `j`-th one times the partial of the chart. -/
theorem partialD_comp_shear {j : Fin d} {γ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hφ : Differentiable ℝ φ) (k : Fin d)
    (y : EuclideanSpace ℝ (Fin d)) :
    partialD k (fun z => φ (shear j γ z)) y
      = partialD k φ (shear j γ y) + partialD j φ (shear j γ y) * partialD k γ y := by
  have := congrArg (fun L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ => L (EuclideanSpace.single k 1))
    (fderiv_comp_shearBy (n := EuclideanSpace.single j (1 : ℝ)) hγ hφ y)
  simpa [partialD, shear, shearBy] using this

end EllipticPdes.Extension
