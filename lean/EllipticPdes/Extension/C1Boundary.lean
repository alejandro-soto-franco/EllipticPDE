/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Extension.BoundaryChart

/-!
# Domains with `C¹` boundary

The extension operator asks that the boundary be `C¹`, and this file states that hypothesis.
Guo's Theorem III.2.2 and Evans' §C.1 both phrase it the same way: near a boundary point, and
after relabelling and reorienting the coordinate axes, the domain is the region above the graph
of a `C¹` function of the remaining coordinates.

The relabelling and reorientation together are a linear isometry of the whole space, so a chart
is that isometry, a direction, a `C¹` function of the remaining coordinates, and a radius. The
gradient bound is part of the chart rather than a consequence of it: a `C¹` function on the whole
space need not have a bounded gradient, and every statement about the shear asks for one.

## Main declarations

* `EllipticPdes.Extension.C1Chart`: a boundary chart.
* `EllipticPdes.Extension.C1Chart.Fits`: the chart describes the domain near a point.
* `EllipticPdes.Extension.HasC1Boundary`: every boundary point admits a chart.
* `EllipticPdes.Extension.hasC1Boundary_aboveGraph`: the region above a graph has `C¹` boundary.
* `EllipticPdes.Extension.isCompact_frontier`: the boundary of a bounded domain is compact,
  which is what a finite subcover of charts needs.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem III.2.2
(p. 20) and its proof, step 2 (p. 21); L. C. Evans, *Partial Differential Equations* (2nd ed.),
§C.1 (p. 666) and §5.4 Theorem 1 (p. 253).
-/

open MeasureTheory Metric Set

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- **Boundary chart of class `C¹`.** The isometry is the relabelling and reorientation of the axes,
the direction is the coordinate the graph is taken in, and the radius is the size of the
neighbourhood the description covers. -/
structure C1Chart (d : ℕ) where
  /-- The relabelling and reorientation of the coordinate axes. -/
  motion : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)
  /-- The coordinate the graph is taken in. -/
  dir : Fin d
  /-- The graph, which depends on the coordinates other than `dir`. -/
  graph : EuclideanSpace ℝ (Fin d) → ℝ
  /-- The radius of the neighbourhood the chart describes. -/
  radius : ℝ
  /-- A bound on the gradient of the graph. -/
  bound : ℝ
  /-- The neighbourhood is nonempty. -/
  radius_pos : 0 < radius
  /-- The graph is of class `C¹`. -/
  graph_contDiff : ContDiff ℝ 1 graph
  /-- The graph does not depend on the coordinate it is a graph in. -/
  graph_indep : IndepCoord dir graph
  /-- The gradient of the graph is bounded. -/
  graph_bounded : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)), ‖partialD k graph y‖ ≤ bound

namespace C1Chart

variable (c : C1Chart d)

/-- The region the chart describes, in the coordinates the chart puts the domain in. -/
def region : Set (EuclideanSpace ℝ (Fin d)) := aboveGraph c.dir c.graph

/-- **Description of `Ω` near `x` by the chart.** After the rigid motion, the domain and the region
above the graph agree on the ball of the chart's radius. -/
def Fits (Ω : Set (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) : Prop :=
  c.motion '' Ω ∩ ball (c.motion x) c.radius = c.region ∩ ball (c.motion x) c.radius

/-- The graph is differentiable, being of class `C¹`. -/
theorem graph_differentiable : Differentiable ℝ c.graph :=
  c.graph_contDiff.differentiable (by simp)

/-- The region the chart describes is open. -/
theorem isOpen_region : IsOpen c.region :=
  isOpen_aboveGraph c.graph_differentiable.continuous

end C1Chart

/-- **`Ω` has `C¹` boundary.** Every boundary point admits a chart, which is the hypothesis of
Guo's Theorem III.2.2 and of Evans' §5.4 Theorem 1. -/
def HasC1Boundary (Ω : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ x ∈ frontier Ω, ∃ c : C1Chart d, c.Fits Ω x

/-! ### Instances and consequences -/

/-- The chart taken by a region that is already the region above a graph: the identity motion,
and any radius. -/
def graphChart {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hγ : ContDiff ℝ 1 γ)
    (hind : IndepCoord j γ) {M : ℝ}
    (hb : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)), ‖partialD k γ y‖ ≤ M) : C1Chart d where
  motion := LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin d))
  dir := j
  graph := γ
  radius := 1
  bound := M
  radius_pos := one_pos
  graph_contDiff := hγ
  graph_indep := hind
  graph_bounded := hb

/-- **`C¹` boundary of the region above a graph**, the identity being a chart at every point. -/
theorem hasC1Boundary_aboveGraph {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hind : IndepCoord j γ) {M : ℝ}
    (hb : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)), ‖partialD k γ y‖ ≤ M) :
    HasC1Boundary (aboveGraph j γ) := by
  intro x _
  refine ⟨graphChart hγ hind hb, ?_⟩
  change (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin d))) '' aboveGraph j γ ∩ _
    = aboveGraph j γ ∩ _
  rw [LinearIsometryEquiv.coe_refl, Set.image_id]

/-- **`C¹` boundary of the half space**, its chart being the zero graph. -/
theorem hasC1Boundary_halfSpace (j : Fin d) : HasC1Boundary (halfSpace j) := by
  have hzero : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)),
      ‖partialD k (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) y‖ ≤ 0 := by
    intro k y
    simp [partialD]
  have hset : halfSpace j = aboveGraph j fun _ => (0 : ℝ) := rfl
  rw [hset]
  exact hasC1Boundary_aboveGraph contDiff_const (fun _ _ => rfl) hzero

/-- **Compactness of the boundary of a bounded domain**, which is what a finite subcover of
charts asks for. -/
theorem isCompact_frontier {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Bornology.IsBounded Ω) :
    IsCompact (frontier Ω) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_frontier
    (hΩ.closure.subset (frontier_subset_closure))

end EllipticPdes.Extension
