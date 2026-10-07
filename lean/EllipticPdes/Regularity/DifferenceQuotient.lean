/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Analysis.FrechetKolmogorov
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous

/-!
# Difference quotients on `L²`

The difference quotient `Dₖʰ u(x) = (u(x + h eₖ) - u(x)) / h` drives the interior regularity
theory (Evans, *Partial Differential Equations* (2nd ed.), §5.8.2 and §6.3.1). It is realised
here as a continuous linear map on the whole-space space `EucL2 d`, built from the translation
isometry `transL2`, so that its adjoint and norm bounds descend from translation invariance of
Lebesgue measure.

The difference quotient `diffQuotAlong μ v h` along a vector `v` of any additive group `E` with an
additively right invariant measure `μ` is built from the translation isometry `transLp μ`, which
is the action of `DomAddAct.mk v` on `Lp`. The coordinate quotient `diffQuot k h` is the instance
`v = eₖ` with `μ` the Lebesgue measure.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

section General

set_option linter.unusedSectionVars false

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [MeasurableSpace E] [MeasurableAdd E]
  (μ : Measure E) [μ.IsAddRightInvariant]

/-- Translation by `v` as a linear isometry of `L²(μ)`, for an additively right invariant
measure `μ`. -/
def transLp (v : E) : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 μ :=
  Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (· + v) (measurePreserving_add_right μ v)

/-- A translate is represented almost everywhere by the shifted function. -/
theorem coeFn_transLp (v : E) (g : Lp ℝ 2 μ) :
    (transLp μ v g : E → ℝ) =ᵐ[μ] fun x => g (x + v) :=
  Lp.coeFn_compMeasurePreserving _ _

/-- Translation is the action of `DomAddAct.mk v` on `L²`. -/
theorem transLp_apply [μ.IsAddLeftInvariant] (v : E) (g : Lp ℝ 2 μ) :
    transLp μ v g = DomAddAct.mk v +ᵥ g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_transLp μ v g, DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk v) g] with x h1 h2
  rw [h1, h2]
  simp [add_comm]

/-- Translation by `-v` inverts translation by `v`. -/
theorem transLp_transLp_neg (v : E) (g : Lp ℝ 2 μ) :
    transLp μ v (transLp μ (-v) g) = g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_transLp μ v (transLp μ (-v) g),
    (measurePreserving_add_right μ v).quasiMeasurePreserving.ae_eq_comp
      (coeFn_transLp μ (-v) g)] with x h1 h2
  rw [h1]
  simpa using h2

/-- Translation by `v` is adjoint to translation by `-v` in the real `L²` inner product:
`⟪τ_v u, w⟫ = ⟪u, τ_{-v} w⟫`. -/
theorem transLp_inner_adjoint (v : E) (u w : Lp ℝ 2 μ) :
    ⟪transLp μ v u, w⟫ = ⟪u, transLp μ (-v) w⟫ := by
  rw [← (transLp μ v).inner_map_map u (transLp μ (-v) w), transLp_transLp_neg]

/-- The forward difference quotient `D_v^h u = (τ_{h v} u - u) / h` along a vector `v`, as a
continuous linear map on `L²(μ)`. For `h = 0` it is the zero map. -/
def diffQuotAlong (v : E) (h : ℝ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  h⁻¹ • ((transLp μ (h • v)).toContinuousLinearMap - ContinuousLinearMap.id ℝ (Lp ℝ 2 μ))

/-- The difference quotient vanishes identically at `h = 0`. -/
@[simp] theorem diffQuotAlong_zero (v : E) : diffQuotAlong μ v (0 : ℝ) = 0 := by
  simp [diffQuotAlong]

/-- The difference quotient is the translation difference divided by the step. -/
theorem diffQuotAlong_apply (v : E) (h : ℝ) (u : Lp ℝ 2 μ) :
    diffQuotAlong μ v h u = h⁻¹ • (transLp μ (h • v) u - u) := by
  simp [diffQuotAlong, LinearIsometry.coe_toContinuousLinearMap]

/-- The pointwise a.e. formula `D_v^h u(x) = (u(x + h v) - u(x)) / h`. -/
theorem coeFn_diffQuotAlong (v : E) (h : ℝ) (u : Lp ℝ 2 μ) :
    (diffQuotAlong μ v h u : E → ℝ) =ᵐ[μ] fun x => (u (x + h • v) - u x) / h := by
  rw [diffQuotAlong_apply]
  filter_upwards [Lp.coeFn_smul h⁻¹ (transLp μ (h • v) u - u),
      Lp.coeFn_sub (transLp μ (h • v) u) u, coeFn_transLp μ (h • v) u]
    with x hx1 hx2 hx3
  simp only [hx1, Pi.smul_apply, hx2, Pi.sub_apply, hx3, smul_eq_mul, div_eq_inv_mul]

/-- **Discrete integration by parts** along `v`: `⟪D_v^h u, w⟫ = -⟪u, D_v^{-h} w⟫`. -/
theorem diffQuotAlong_inner_adjoint (v : E) (h : ℝ) (u w : Lp ℝ 2 μ) :
    ⟪diffQuotAlong μ v h u, w⟫ = -⟪u, diffQuotAlong μ v (-h) w⟫ := by
  rw [diffQuotAlong_apply, diffQuotAlong_apply, real_inner_smul_left, real_inner_smul_right,
    inner_sub_left, inner_sub_right, transLp_inner_adjoint μ (h • v) u w, neg_smul]
  ring

end General

variable {d : ℕ}

/-- The shift vector `h • eₖ` in the `k`-th coordinate direction. -/
def hshift (k : Fin d) (h : ℝ) : EuclideanSpace ℝ (Fin d) :=
  h • EuclideanSpace.single k (1 : ℝ)

/-- The forward difference quotient `Dₖʰ u = (τ_{h eₖ} u - u) / h` as a
continuous linear map on `L²(ℝⁿ)`: the instance `v = eₖ` of `diffQuotAlong`. For `h = 0` it is
the zero map. -/
def diffQuot (k : Fin d) (h : ℝ) : EucL2 d →L[ℝ] EucL2 d :=
  h⁻¹ • ((transL2 (hshift k h)).toContinuousLinearMap - ContinuousLinearMap.id ℝ (EucL2 d))

/-- Translation on `EucL2 d` is the general translation for Lebesgue measure. -/
theorem transL2_eq_transLp (v : EuclideanSpace ℝ (Fin d)) :
    transL2 v = transLp volume v := rfl

/-- The coordinate difference quotient is the difference quotient along `eₖ`. -/
theorem diffQuot_eq_diffQuotAlong (k : Fin d) (h : ℝ) :
    diffQuot k h = diffQuotAlong volume (EuclideanSpace.single k (1 : ℝ)) h := rfl

/-- The difference quotient vanishes identically at `h = 0`. -/
@[simp] theorem diffQuot_zero (k : Fin d) : diffQuot k (0 : ℝ) = 0 := by
  simp [diffQuot]

/-- The difference quotient is the translation difference divided by the step. -/
theorem diffQuot_apply (k : Fin d) (h : ℝ) (u : EucL2 d) :
    diffQuot k h u = h⁻¹ • (transL2 (hshift k h) u - u) :=
  diffQuotAlong_apply volume _ h u

/-- The pointwise a.e. formula for the difference quotient:
`Dₖʰ u(x) = (u(x + h eₖ) - u(x)) / h`. -/
theorem coeFn_diffQuot (k : Fin d) (h : ℝ) (u : EucL2 d) :
    (diffQuot k h u : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume] fun x => (u (x + hshift k h) - u x) / h :=
  coeFn_diffQuotAlong volume _ h u

/-- Translation by `v` is adjoint to translation by `-v` in the real `L²` inner product:
`⟪τ_v u, w⟫ = ⟪u, τ_{-v} w⟫`. This is the continuous shadow of discrete summation by
parts, and rests on translation invariance of Lebesgue measure (Evans, *Partial
Differential Equations* (2nd ed.), §5.8.2). -/
theorem transL2_inner_adjoint (v : EuclideanSpace ℝ (Fin d)) (u w : EucL2 d) :
    ⟪transL2 v u, w⟫ = ⟪u, transL2 (-v) w⟫ :=
  transLp_inner_adjoint volume v u w

/-- The shift vector negates under negation of the step: `h eₖ ↦ -(h eₖ)` as `h ↦ -h`. -/
theorem hshift_neg (k : Fin d) (h : ℝ) : hshift k (-h) = - hshift k h := by
  simp [hshift, neg_smul]

/-- **Discrete integration by parts.** The difference quotient `Dₖʰ` is adjoint, up to a
sign, to the backward difference quotient `Dₖ⁻ʰ`: `⟪Dₖʰ u, w⟫ = -⟪u, Dₖ⁻ʰ w⟫`. This is
the discretised analogue of integration by parts underlying the Caccioppoli-type interior
estimate (Evans, *Partial Differential Equations* (2nd ed.), §5.8.2, proof of Theorem 3). -/
theorem diffQuot_inner_adjoint (k : Fin d) (h : ℝ) (u w : EucL2 d) :
    ⟪diffQuot k h u, w⟫ = -⟪u, diffQuot k (-h) w⟫ :=
  diffQuotAlong_inner_adjoint volume _ h u w

end EllipticPdes.Regularity
