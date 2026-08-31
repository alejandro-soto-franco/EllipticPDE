/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Extension.C1Test
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The shear of a `C¹` boundary chart

A bounded domain with `C¹` boundary is, near a boundary point and after relabelling the
coordinates, the region above the graph of a `C¹` function `γ` of the remaining coordinates.
The map that flattens the boundary is the shear `y ↦ y + γ(y) • eⱼ`, whose inverse is the shear
by `-γ`, and whose derivative is the identity plus a rank-one map that annihilates its own
direction. Its determinant is therefore `1`, so it preserves Lebesgue measure and the change of
variables costs nothing.

## Main declarations

* `EllipticPdes.Extension.shear`: the map.
* `EllipticPdes.Extension.shear_shear_neg`: the shear by `-γ` inverts it.
* `EllipticPdes.Extension.det_shearDeriv`: the derivative has determinant `1`.
* `EllipticPdes.Extension.integral_comp_shear`: the change of variables.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4, and §C.1 for the boundary chart.
-/

open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- **Shear of a boundary chart.** The point `y` moves along the `j`-th axis by `γ y`. -/
def shear (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  y + γ y • EuclideanSpace.single j (1 : ℝ)

/-- `γ` does not depend on the `j`-th coordinate, which is what makes the shear invertible by a
shear and its derivative nilpotent. -/
def IndepCoord (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ (y : EuclideanSpace ℝ (Fin d)) (t : ℝ), γ (y + t • EuclideanSpace.single j (1 : ℝ)) = γ y

/-- **Inversion of the shear by `γ`.** -/
theorem shear_shear_neg {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hind : IndepCoord j γ)
    (y : EuclideanSpace ℝ (Fin d)) : shear j (fun z => -γ z) (shear j γ y) = y := by
  simp only [shear, hind y (γ y)]
  module

/-- **Inversion of the shear by `-γ`.** -/
theorem shear_neg_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hind : IndepCoord j γ)
    (y : EuclideanSpace ℝ (Fin d)) : shear j γ (shear j (fun z => -γ z) y) = y := by
  simp only [shear]
  rw [hind y (-γ y)]
  module

/-- The shear is a bijection of the whole space. -/
theorem bijective_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hind : IndepCoord j γ) :
    Function.Bijective (shear j γ) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨shear j (fun z => -γ z), shear_shear_neg hind, shear_neg_shear hind⟩

/-- **A function independent of the `j`-th coordinate has vanishing `j`-th partial.** -/
theorem partialD_eq_zero_of_indepCoord {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) (y : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ γ y (EuclideanSpace.single j (1 : ℝ)) = 0 := by
  have h1 : HasLineDerivAt ℝ γ (fderiv ℝ γ y (EuclideanSpace.single j (1 : ℝ))) y
      (EuclideanSpace.single j (1 : ℝ)) :=
    (hγ y).hasFDerivAt.hasLineDerivAt _
  have h0 : HasLineDerivAt ℝ γ 0 y (EuclideanSpace.single j (1 : ℝ)) := by
    change HasDerivAt (fun t : ℝ => γ (y + t • EuclideanSpace.single j (1 : ℝ))) 0 0
    have hconst : (fun t : ℝ => γ (y + t • EuclideanSpace.single j (1 : ℝ))) = fun _ => γ y :=
      funext (hind y)
    rw [hconst]
    exact hasDerivAt_const 0 (γ y)
  exact h1.unique h0

/-- The derivative of the shear: the identity plus a rank-one map in the direction `eⱼ`. -/
def shearDeriv (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))
    + (fderiv ℝ γ y).smulRight (EuclideanSpace.single j (1 : ℝ))

/-- **Derivative of the shear.** -/
theorem hasFDerivAt_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (y : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (shear j γ) (shearDeriv j γ y) y := by
  exact (hasFDerivAt_id y).add (((hγ y).hasFDerivAt).smul_const
    (EuclideanSpace.single j (1 : ℝ)))

/-- **Determinant `1` of the shear derivative.** In the standard basis the matrix is the
identity with row `j` replaced by `eⱼ + ∇γ`. Multilinearity in that row splits the determinant
into `det 1` and the determinant of the identity with row `j` replaced by `∇γ`, and the latter
reads off as the `j`-th component of `∇γ`, which vanishes. -/
theorem det_shearDeriv {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) (y : EuclideanSpace ℝ (Fin d)) :
    (shearDeriv j γ y).det = 1 := by
  classical
  set b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis with hb
  set c : Fin d → ℝ := fun k => fderiv ℝ γ y (b k) with hc
  have hbk : ∀ k, b k = EuclideanSpace.single k (1 : ℝ) := by
    intro k; rw [hb]; simp [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  have hcj : c j = 0 := by
    rw [hc]
    simp only
    rw [hbk j]
    exact partialD_eq_zero_of_indepCoord hγ hind y
  have hmat : LinearMap.toMatrix b b (shearDeriv j γ y : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _)
      = Matrix.updateRow (1 : Matrix (Fin d) (Fin d) ℝ) j
          ((1 : Matrix (Fin d) (Fin d) ℝ) j + c) := by
    ext i k
    rw [LinearMap.toMatrix_apply]
    simp only [hb, shearDeriv]
    by_cases hij : i = j
    · subst hij
      simp [Matrix.updateRow_apply, Matrix.one_apply, hc, hbk]
    · rw [Matrix.updateRow_ne hij]
      simp [Matrix.one_apply, hij]
  have hdet : (Matrix.updateRow (1 : Matrix (Fin d) (Fin d) ℝ) j
      ((1 : Matrix (Fin d) (Fin d) ℝ) j + c)).det = 1 := by
    rw [Matrix.det_updateRow_add]
    have h1 : (Matrix.updateRow (1 : Matrix (Fin d) (Fin d) ℝ) j
        ((1 : Matrix (Fin d) (Fin d) ℝ) j)).det = 1 := by
      rw [Matrix.updateRow_eq_self, Matrix.det_one]
    have h2 : (Matrix.updateRow (1 : Matrix (Fin d) (Fin d) ℝ) j c).det = 0 := by
      have hrow : c = ∑ k, c k • (1 : Matrix (Fin d) (Fin d) ℝ) k := by
        funext m
        simp [Matrix.one_apply, Finset.sum_apply]
      rw [hrow, Matrix.det_updateRow_sum, Matrix.det_one]
      simp [hcj]
    rw [h1, h2, add_zero]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, hmat, hdet]

/-- **Change of variables through a shear.** The Jacobian determinant is `1`, so the shear
leaves every integral unchanged. -/
theorem integral_comp_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) (g : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫ y, g (shear j γ y) = ∫ x, g x := by
  have hinj : Set.InjOn (shear j γ) Set.univ := (bijective_shear hind).injective.injOn
  have hfd : ∀ y ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin d))),
      HasFDerivWithinAt (shear j γ) (shearDeriv j γ y) Set.univ y :=
    fun y _ => (hasFDerivAt_shear hγ y).hasFDerivWithinAt
  have himg : (shear j γ) '' Set.univ = Set.univ := by
    rw [Set.image_univ, (bijective_shear hind).surjective.range_eq]
  have h := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) MeasurableSet.univ hfd
    hinj g
  rw [himg, Measure.restrict_univ] at h
  simp only [det_shearDeriv hγ hind, abs_one, one_smul] at h
  exact h.symm

end EllipticPdes.Extension
