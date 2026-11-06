/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.Graph
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Density of `H₀¹(Ω)` in `L²(Ω)` and separability of the graph space

For an open set `Ω` in a finite-dimensional real inner product space and a measure finite on
compact sets, the inclusion `H₀¹(Ω) → L²(Ω)` has dense range. Its range contains the classes of the
test functions. A class orthogonal to all of them integrates to zero against every smooth function
with compact support in `Ω`, and the fundamental lemma of the calculus of variations makes it vanish
almost everywhere on `Ω`.

The graph space is second countable. The Borel σ-algebra of `E` is countably generated, and a
measure finite on compact sets of a σ-compact space is σ-finite. Mathlib's
`Lp.SecondCountableTopology` then applies to `L²(Ω)` and `L²(Ω; E)`. Second countability passes
to their product and to every subspace of it.

## Main declarations

* `EllipticPdes.H1Graph.denseRange_embL2`
* `EllipticPdes.H1Graph.secondCountableTopology`, `EllipticPdes.H1Graph.secondCountableTopology_H01`
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace EllipticPdes.H1Graph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {Ω : Set E}

/-! ### Separability -/

variable (μ Ω) in
/-- **The graph space is second countable.** -/
instance secondCountableTopology : SecondCountableTopology (H1Graph μ Ω) :=
  haveI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  inferInstanceAs
    (SecondCountableTopology (WithLp 2 (Lp ℝ 2 (μ.restrict Ω) × Lp E 2 (μ.restrict Ω))))

variable (μ Ω) in
/-- **`H₀¹(Ω)` is second countable**, hence separable. -/
instance secondCountableTopology_H01 : SecondCountableTopology (H01 μ Ω) :=
  TopologicalSpace.Subtype.secondCountableTopology _

/-! ### Density -/

omit [FiniteDimensional ℝ E] in
/-- The inner product of the class of a test function with `f` is the integral of their
product against `μ`. -/
lemma Internal.inner_fnCls_eq_integral (φ : testFunctions Ω) (f : Lp ℝ 2 (μ.restrict Ω)) :
    ⟪fnCls μ Ω φ, f⟫ = ∫ x, (φ : E → ℝ) x • f x ∂μ := by
  rw [L2.inner_def]
  refine (integral_congr_ae (g := fun x => (φ : E → ℝ) x • f x) ?_).trans
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_)
  · filter_upwards [coeFn_fnCls φ] with x hx
    simp [hx, mul_comm]
  · rw [image_eq_zero_of_notMem_tsupport fun h => hx (φ.2.2.2 h), zero_smul]

/-- **A class orthogonal to every test function vanishes.** -/
lemma Internal.eq_zero_of_inner_fnCls (hΩ : IsOpen Ω) {f : Lp ℝ 2 (μ.restrict Ω)}
    (h : ∀ φ : testFunctions Ω, ⟪fnCls μ Ω φ, f⟫ = 0) : f = 0 :=
  Lp.eq_zero_iff_ae_eq_zero.2 (by
    filter_upwards [(ae_restrict_iff' hΩ.measurableSet).2
        (hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
          (locallyIntegrableOn_of_locallyIntegrable_restrict
            ((Lp.memLp f).locallyIntegrable one_le_two))
          fun g hg hgc hgs => (Internal.inner_fnCls_eq_integral ⟨g, hg, hgc, hgs⟩ f).symm.trans
            (h _))] with x h1
    exact h1)

/-- **`H₀¹(Ω)` is dense in `L²(Ω)`** for an open set `Ω` and a measure finite on compact sets. -/
theorem denseRange_embL2 (hΩ : IsOpen Ω) : DenseRange (embL2 μ Ω) := by
  change Dense ((LinearMap.range (embL2 μ Ω : H01 μ Ω →ₗ[ℝ] Lp ℝ 2 (μ.restrict Ω)) :
    Set (Lp ℝ 2 (μ.restrict Ω))))
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  exact fun f hf => Internal.eq_zero_of_inner_fnCls hΩ fun φ =>
    Submodule.inner_right_of_mem_orthogonal
      (LinearMap.mem_range.2 ⟨⟨_, testGraphₗ_mem_H01 φ⟩, rfl⟩ :
        fnCls μ Ω φ ∈ LinearMap.range (embL2 μ Ω : H01 μ Ω →ₗ[ℝ] Lp ℝ 2 (μ.restrict Ω))) hf

end EllipticPdes.H1Graph
