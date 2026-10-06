/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.Local.Reduction
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# Weak gradient of a `W^{1,infinity}` coefficient

`IsLipCoeff` is the hypothesis the interior estimate reads, and the cutoff reduction that
takes the estimate from `H_0^1(Omega)` to `H^1(Omega)` reads one thing more: a weak gradient
of each coefficient entry, essentially bounded. A `C^1` coefficient supplies it through its
classical partials (`IsC1Coeff.coeffWeakGrad`) and a `W^{k+1,infinity}` family through its first
order (`IsWkInftyCoeff.coeffWeakGrad`). This file supplies it from the Lipschitz estimate alone,
which is what Guo, *Partial Differential Equations I and II* (Course Lecture Notes),
Theorem VIII.2.2 (p. 63) and Gilbarg-Trudinger, *Elliptic Partial Differential Equations of
Second Order*, Theorem 8.8 (p. 179) ask of the leading coefficients.

Rademacher's theorem (`LipschitzWith.ae_differentiableAt`) gives a derivative almost
everywhere, and `fderiv` names it: the total `fderiv` of Mathlib is the derivative where one
exists and zero elsewhere, so `coeffDa A l i j` below is measurable (`measurable_fderiv`) and
bounded by the Lipschitz constant (`norm_fderiv_le_of_lipschitz`). It is the weak derivative by
the integration by parts formula for Lipschitz functions,
`LipschitzWith.integral_lineDeriv_mul_eq`.

## Main declarations

* `coeffDa`: the chosen representative of `∂_l a_{ij}`.
* `measurable_coeffDa`, `IsLipCoeff.abs_da_le`: its measurability and its bound.
* `IsLipCoeff.hasWeakPartial`: it is the weak partial derivative of the entry.
* `IsLipCoeff.toIsWkInftyCoeff`: a Lipschitz coefficient is a `W^{1,∞}` coefficient.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology NNReal

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {A : EllipticCoeff d}

/-- The chosen representative of the weak partial `∂_l a_{ij}`: the total `fderiv` applied to
the `l`-th basis vector, which is the classical partial wherever the entry is differentiable
and zero on the null set where it is not. It is written for the coefficient rather than for a
bundle over it, no hypothesis being needed to name it. -/
def coeffDa (A : EllipticCoeff d) (l i j : Fin d) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single l (1 : ℝ))

/-- `coeffDa` is measurable, the total `fderiv` being measurable and evaluation at a vector
continuous. No regularity of the entry enters. -/
theorem measurable_coeffDa (A : EllipticCoeff d) (l i j : Fin d) :
    Measurable (coeffDa A l i j) :=
  ((ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single l (1 : ℝ))).continuous.measurable).comp
    (measurable_fderiv ℝ (fun y => A.a y i j))

/-- `coeffDa` is bounded by the Lipschitz constant everywhere: where the entry is differentiable
this is the converse mean value inequality, and elsewhere `fderiv` is zero. -/
theorem IsLipCoeff.abs_da_le (hA : IsLipCoeff A) (l i j : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : |coeffDa A l i j x| ≤ hA.A1 := by
  have hop : ‖fderiv ℝ (fun y => A.a y i j) x‖ ≤ (Real.toNNReal hA.A1 : ℝ) :=
    norm_fderiv_le_of_lipschitz ℝ (hA.lipschitzWith i j)
  have hle := (fderiv ℝ (fun y => A.a y i j) x).le_opNorm
    (EuclideanSpace.single l (1 : ℝ))
  rw [PiLp.norm_single, norm_one, mul_one] at hle
  have : ‖coeffDa A l i j x‖ ≤ (Real.toNNReal hA.A1 : ℝ) := le_trans hle hop
  rwa [Real.norm_eq_abs, Real.coe_toNNReal _ hA.A1_nonneg] at this

/-- **A Lipschitz entry has the weak partial `coeffDa`.** Integration by parts for Lipschitz
functions against a smooth compactly supported test function, with the line derivative of the
entry equal to `fderiv` almost everywhere by Rademacher's theorem. -/
theorem IsLipCoeff.hasWeakPartial (hA : IsLipCoeff A) (l i j : Fin d) :
    HasWeakPartial l (fun x => A.a x i j) (coeffDa A l i j) := by
  intro φ hφ hφc
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ (by simp)
  have h := (hA.lipschitzWith i j).integral_lineDeriv_mul_eq hD hφc
    (EuclideanSpace.single l (1 : ℝ)) (μ := volume)
  have hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      lineDeriv ℝ (fun y => A.a y i j) x (EuclideanSpace.single l (1 : ℝ)) * φ x
        = coeffDa A l i j x * φ x := by
    filter_upwards [(hA.lipschitzWith i j).ae_differentiableAt (μ := volume)] with x hx
    rw [hx.lineDeriv_eq_fderiv]; rfl
  have hφd : ∀ x, lineDeriv ℝ φ x (-EuclideanSpace.single l (1 : ℝ)) = -partialD l φ x :=
    fun x => by
    rw [((hφ.differentiable (by simp)).differentiableAt).lineDeriv_eq_fderiv, map_neg]; rfl
  rw [integral_congr_ae hae] at h
  simp only [hφd, neg_mul, integral_neg] at h
  rw [show (∫ x, A.a x i j * partialD l φ x) = ∫ x, partialD l φ x * A.a x i j from
    integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)]
  linarith only [h]

/-- **A Lipschitz coefficient is a `W^{1,∞}` coefficient.** The family is the entry, its
partials `coeffDa`, and zero beyond order one. -/
def IsLipCoeff.toIsWkInftyCoeff (hA : IsLipCoeff A) : IsWkInftyCoeff A 1 where
  D α i j := match α with
    | [] => fun x => A.a x i j
    | [l] => coeffDa A l i j
    | _ => 0
  D_nil _ _ := rfl
  D_meas i j α hα := by
    match α, hα with
    | [], _ => exact A.measurable i j
    | [l], _ => exact measurable_coeffDa A l i j
    | _ :: _ :: _, h => simp at h
  D_step i j l α hα := by
    match α, hα with
    | [], _ => exact hA.hasWeakPartial l i j
    | _ :: _, h => simp at h
  bound m := if m = 0 then A.Λ else hA.A1
  bound_nonneg m := by
    by_cases h : m = 0 <;> simp [h, A.Λ_nonneg, hA.A1_nonneg]
  ess_bdd i j α hα := by
    match α, hα with
    | [], _ => filter_upwards [A.bdd i j] with x hx; simpa using hx
    | [l], _ => exact Filter.Eventually.of_forall fun x => by simpa using hA.abs_da_le l i j x
    | _ :: _ :: _, h => simp at h

end EllipticPdes.Regularity
