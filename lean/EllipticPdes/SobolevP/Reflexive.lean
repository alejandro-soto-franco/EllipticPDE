/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Monotone.ReflexiveLp
public import EllipticPdes.SobolevP.Graph

/-!
# Reflexivity of `W₀^{1,p}`

For `1 < p < ∞`, a finite-dimensional normed space `E` and a set `Ω` of finite measure under an
additive Haar measure, `W1pGraph p μ Ω` is a product of two reflexive spaces, `L^p(Ω)` and
`L^p(Ω; E*)`. Its closed subspace `W1p0 p μ Ω` is therefore reflexive.

## Main declarations

* `EllipticPdes.isReflexive_W1pGraph`: the graph space is reflexive.
* `EllipticPdes.isReflexive_W1p0`: `W₀^{1,p}(Ω)` is reflexive.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace EllipticPdes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- **Reflexivity of the graph space.** `L^p(Ω) × L^p(Ω; E*)` is a product of reflexive spaces for
`1 < p < ∞` and `μ Ω < ∞`. -/
theorem isReflexive_W1pGraph (hΩ : μ Ω ≠ ∞) (hp1 : 1 < p) (hpt : p ≠ ∞) :
    Analysis.IsReflexive (W1pGraph p μ Ω) := by
  have : IsFiniteMeasure (μ.restrict Ω) := isFiniteMeasure_restrict.2 hΩ
  exact Analysis.IsReflexive.prod p (Analysis.isReflexive_Lp hp1 hpt)
    (Analysis.isReflexive_Lp_finiteDimensional hp1 hpt)

/-- **`W₀^{1,p}(Ω)` is reflexive.** A closed subspace of the reflexive graph space is reflexive
(Brezis Proposition 3.20, p. 70). -/
theorem isReflexive_W1p0 (hΩ : μ Ω ≠ ∞) (hp1 : 1 < p) (hpt : p ≠ ∞) :
    Analysis.IsReflexive (W1p0 p μ Ω) :=
  (isReflexive_W1pGraph hΩ hp1 hpt).submodule _ (isClosed_W1p0 p μ Ω)

end EllipticPdes
