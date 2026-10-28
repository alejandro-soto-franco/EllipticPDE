/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.C1Boundary

/-!
# Domains with `C^k` boundary

Evans's Appendix C.1 (p. 710) defines the `C^k` boundary of an open bounded set `U` and
`k ∈ {1, 2, …}`: for each `x⁰ ∈ ∂U` there are `r > 0` and a `C^k` function `γ : ℝ^{n-1} → ℝ`
such that `U ∩ B(x⁰, r) = {x ∈ B(x⁰, r) | xₙ > γ(x₁, …, x_{n-1})}` after relabelling and
reorienting the coordinate axes if necessary.

This file states the definition with the chart of `C1Boundary.lean` and the smoothness `k` as a
parameter. It applies to any set `Ω` of the library, and Evans's open bounded `U` is a special
case. The restriction `k ≥ 1` appears as a hypothesis only where a lemma needs it.

## Main declarations

* `EllipticPdes.Extension.CkChart`: a boundary chart with a `C^k` graph.
* `EllipticPdes.Extension.CkChart.Fits`: the chart describes the domain near a point.
* `EllipticPdes.Extension.HasCkBoundary`: every boundary point admits a chart.
* `EllipticPdes.Extension.hasCkBoundary_one_iff`: at `k = 1` this is `HasC1Boundary`.
* `EllipticPdes.Extension.HasCkBoundary.mono`: a `C^k` boundary is a `C^l` boundary for `l ≤ k`.
* `EllipticPdes.Extension.hasCkBoundary_aboveGraph`: the region above a `C^k` graph.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), Appendix C.1 (p. 710).
-/

@[expose] public section

noncomputable section

namespace EllipticPdes.Extension

variable {d : ℕ}

/-- **Boundary chart of class `C^k`.** The isometry is the relabelling and reorientation of the
axes, the direction is the coordinate the graph is taken in, and the radius is the size of the
neighbourhood the description covers. -/
structure CkChart (d k : ℕ) where
  /-- The relabelling and reorientation of the coordinate axes. -/
  motion : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)
  /-- The coordinate the graph is taken in. -/
  dir : Fin d
  /-- The graph, which depends on the coordinates other than `dir`. -/
  graph : EuclideanSpace ℝ (Fin d) → ℝ
  /-- The radius of the neighbourhood the chart describes. -/
  radius : ℝ
  /-- The neighbourhood is nonempty. -/
  radius_pos : 0 < radius
  /-- The graph is of class `C^k`. -/
  graph_contDiff : ContDiff ℝ k graph
  /-- The graph does not depend on the coordinate it is a graph in. -/
  graph_indep : IndepCoord dir graph

namespace CkChart

variable {k : ℕ} (c : CkChart d k)

/-- The region the chart describes, in the coordinates the chart puts the domain in. -/
def region : Set (EuclideanSpace ℝ (Fin d)) := aboveGraph c.dir c.graph

/-- **Description of `Ω` near `x` by the chart.** After the rigid motion the domain and the
region above the graph agree on the ball of the chart's radius. -/
def Fits (Ω : Set (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) : Prop :=
  c.motion '' Ω ∩ Metric.ball (c.motion x) c.radius
    = c.region ∩ Metric.ball (c.motion x) c.radius

end CkChart

/-- **`Ω` has `C^k` boundary** (Evans Appendix C.1, p. 710). Every boundary point admits a
chart with a `C^k` graph. -/
def HasCkBoundary (k : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ x ∈ frontier Ω, ∃ c : CkChart d k, c.Fits Ω x

/-- A chart of class `C^1` read as a chart of the extension theorem. -/
def CkChart.toC1Chart (c : CkChart d 1) : C1Chart d where
  motion := c.motion
  dir := c.dir
  graph := c.graph
  radius := c.radius
  radius_pos := c.radius_pos
  graph_contDiff := c.graph_contDiff
  graph_indep := c.graph_indep

/-- A chart of the extension theorem read as a chart of class `C^1`. -/
def C1Chart.toCkChart (c : C1Chart d) : CkChart d 1 where
  motion := c.motion
  dir := c.dir
  graph := c.graph
  radius := c.radius
  radius_pos := c.radius_pos
  graph_contDiff := c.graph_contDiff
  graph_indep := c.graph_indep

/-- **Evans's `C^1` boundary.** `HasCkBoundary 1` is the library's `HasC1Boundary`, since the two
chart structures have the same fields. -/
theorem hasCkBoundary_one_iff {Ω : Set (EuclideanSpace ℝ (Fin d))} :
    HasCkBoundary 1 Ω ↔ HasC1Boundary Ω :=
  ⟨fun h x hx => let ⟨c, hc⟩ := h x hx; ⟨c.toC1Chart, hc⟩,
    fun h x hx => let ⟨c, hc⟩ := h x hx; ⟨c.toCkChart, hc⟩⟩

/-- A chart of class `C^k` is a chart of class `C^l` for `l ≤ k`. -/
def CkChart.weaken {k l : ℕ} (hlk : l ≤ k) (c : CkChart d k) : CkChart d l where
  motion := c.motion
  dir := c.dir
  graph := c.graph
  radius := c.radius
  radius_pos := c.radius_pos
  graph_contDiff := c.graph_contDiff.of_le (by exact_mod_cast hlk)
  graph_indep := c.graph_indep

/-- **Monotonicity of `C^k` boundaries in `k`.** A `C^k` boundary is a `C^l` boundary for
every `l ≤ k`. -/
theorem HasCkBoundary.mono {k l : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hlk : l ≤ k)
    (h : HasCkBoundary k Ω) : HasCkBoundary l Ω :=
  fun x hx => let ⟨c, hc⟩ := h x hx; ⟨c.weaken hlk, hc⟩

/-- **`C^k` boundary of the region above a graph.** The identity is a chart at every point. -/
theorem hasCkBoundary_aboveGraph {k : ℕ} {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : ContDiff ℝ k γ) (hind : IndepCoord j γ) : HasCkBoundary k (aboveGraph j γ) := by
  intro x _
  refine ⟨⟨LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin d)), j, γ, 1, one_pos, hγ, hind⟩, ?_⟩
  change (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin d))) '' aboveGraph j γ ∩ _
    = aboveGraph j γ ∩ _
  rw [LinearIsometryEquiv.coe_refl, Set.image_id]

end EllipticPdes.Extension
