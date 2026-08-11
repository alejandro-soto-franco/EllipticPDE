/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Existence.Garding

/-!
# The weak formulation extends from test functions to all of `H₀¹(Ω)`

`EllipticPdes.Regularity.localWeakForm_of_fullBilin` reads a localised identity off the
weak formulation `∀ w : H₀¹(Ω), B[u, w] = ⟪f, w₀⟫`. The induction of Guo, *Partial
Differential Equations I and II* (Course Lecture Notes), Theorem VIII.3.2 (p. 65) needs
the converse: the differentiated equation is produced against test functions, and the
induction hypothesis consumes an identity quantified over every `w : H₀¹(Ω)`.

The passage is density. `H₀¹(Ω)` is by definition the closure of the test-function graphs
inside the ambient graph space, and both sides of the identity are continuous linear in
`w`, so agreement on the graphs is agreement everywhere. The datum side is continuous
because it is an inner product against a fixed vector: `⟪f, w₀⟫ = ⟪single 0 f, w⟫` by
`EllipticPdes.Sobolev.inner_single_left`, which is what `datumL` records.

## Main declarations

* `testGraph_mem_H01`: a test function's graph lies in `H₀¹(Ω)`.
* `datumL`: the datum functional `w ↦ ∫_Ω f w₀`, as a continuous linear map on `H₀¹(Ω)`.
* `eq_of_eq_on_testGraphs`: two continuous linear functionals agreeing on every
  test-function graph agree on `H₀¹(Ω)`.
* `weakForm_of_testFn`: the weak formulation, from test functions to `H₀¹(Ω)`.
-/

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- A test function's graph lies in `H₀¹(Ω)`, being one of the vectors whose span is
closed to form it. -/
theorem testGraph_mem_H01 {v : EuclideanSpace ℝ (Fin d) → ℝ} (hv : IsTestFn Ω v) :
    hv.testGraph ∈ H01 Ω :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨v, hv, rfl⟩)

/-- **The datum functional.** Pairing against `f` in the function coordinate,
`w ↦ ∫_Ω f w₀`, is continuous linear on `H₀¹(Ω)`: it is the inner product against the
ambient vector carrying `f` in coordinate `0` and zero elsewhere, restricted to the
subspace. -/
def datumL (f : L2D Ω) : H01 Ω →L[ℝ] ℝ :=
  (innerSL ℝ (PiLp.single 2 (0 : Fin (d + 1)) f)).comp (Submodule.subtypeL (H01 Ω))

/-- `datumL f` is the integral of `f` against the function coordinate. -/
theorem datumL_apply (f : L2D Ω) (w : H01 Ω) :
    datumL f w = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ) := by
  change ⟪PiLp.single 2 (0 : Fin (d + 1)) f, (w : H1amb Ω)⟫ = _
  rw [inner_single_left, L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun a => Real.inner_apply _ _)

/-- **Test-function graphs determine a continuous functional on `H₀¹(Ω)`.** Their span is
dense by the definition of `H₀¹(Ω)` as a topological closure, so a sequence of graphs
converges to any given `w`, and continuity carries the agreement across the limit. -/
theorem eq_of_eq_on_testGraphs (F G : H01 Ω →L[ℝ] ℝ)
    (h : ∀ (v : EuclideanSpace ℝ (Fin d) → ℝ) (hv : IsTestFn Ω v),
      F ⟨hv.testGraph, testGraph_mem_H01 hv⟩ = G ⟨hv.testGraph, testGraph_mem_H01 hv⟩)
    (w : H01 Ω) : F w = G w := by
  classical
  have hmem : (w : H1amb Ω)
      ∈ closure ((Submodule.span ℝ (testGraphSet Ω) : Submodule ℝ (H1amb Ω)) : Set (H1amb Ω)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact w.2
  obtain ⟨x, hx, hxt⟩ := mem_closure_iff_seq_limit.1 hmem
  have hxmem : ∀ n, x n ∈ H01 Ω := fun n => Submodule.le_topologicalClosure _ (hx n)
  set y : ℕ → H01 Ω := fun n => ⟨x n, hxmem n⟩ with hy
  have hyt : Filter.Tendsto y Filter.atTop (nhds w) := by
    rw [Topology.IsEmbedding.tendsto_nhds_iff Topology.IsEmbedding.subtypeVal]
    exact hxt
  have hFG : ∀ n, F (y n) = G (y n) := by
    intro n
    have hxn : x n ∈ testGraphSet Ω := by
      have := hx n
      rwa [span_testGraphSet] at this
    obtain ⟨v, hv, hveq⟩ := hxn
    have hyn : y n = ⟨hv.testGraph, testGraph_mem_H01 hv⟩ := Subtype.ext hveq
    rw [hyn]
    exact h v hv
  have h1 : Filter.Tendsto (fun n => F (y n)) Filter.atTop (nhds (F w)) :=
    (F.continuous.tendsto w).comp hyt
  have h2 : Filter.Tendsto (fun n => G (y n)) Filter.atTop (nhds (G w)) :=
    (G.continuous.tendsto w).comp hyt
  refine tendsto_nhds_unique ?_ h2
  simpa only [hFG] using h1

/-- **The weak formulation, from test functions to `H₀¹(Ω)`.** An identity
`B[u, φ] = ∫_Ω f φ` holding for every test function holds against every `w ∈ H₀¹(Ω)`. This
is the shape `InteriorRegularityAt` consumes, and the shape the differentiated equation
does not directly produce, since a differentiated equation is derived by testing. -/
theorem weakForm_of_testFn (Op : FullEllipticOp d) (u : H01 Ω) (f : L2D Ω)
    (h : ∀ (v : EuclideanSpace ℝ (Fin d) → ℝ) (hv : IsTestFn Ω v),
      Op.fullBilin Ω u ⟨hv.testGraph, testGraph_mem_H01 hv⟩ = ∫ x in Ω, (f x : ℝ) * v x)
    (w : H01 Ω) :
    Op.fullBilin Ω u w = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ) := by
  have hEq := eq_of_eq_on_testGraphs (Op.fullBilin Ω u) (datumL f) ?_ w
  · rwa [datumL_apply] at hEq
  · intro v hv
    rw [datumL_apply, h v hv]
    refine integral_congr_ae ?_
    have hcoe : ((⟨hv.testGraph, testGraph_mem_H01 hv⟩ : H01 Ω) : H1amb Ω) 0
        = hv.mem_lp.toLp v := IsTestFn.testGraph_zero hv
    rw [hcoe]
    filter_upwards [hv.mem_lp.coeFn_toLp] with a ha
    rw [ha]

end EllipticPdes.Regularity
