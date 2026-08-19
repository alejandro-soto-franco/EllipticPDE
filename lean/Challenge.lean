/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Fredholm alternative for a second-order divergence-form elliptic operator

Let `Ω ⊆ ℝ^d` and let

  `L u = -∂_j (a_{ij} ∂_i u) + b_i ∂_i u + c u`

be a second-order operator in divergence form whose coefficients are measurable and
bounded and whose principal part is uniformly elliptic, `∑_{ij} a_{ij}(x) ξ_i ξ_j ≥ λ |ξ|²`
for almost every `x` and every `ξ`. The drift `b` is unrestricted, so the operator is in
general non-symmetric and the problem carries no variational structure.

The weak formulation of the Dirichlet problem seeks `u ∈ H_0^1(Ω)` with

  `B[u, v] = ⟨f, v⟩` for every `v ∈ H_0^1(Ω)`,

where

  `B[u, v] = ∑_{ij} ∫_Ω a_{ij} ∂_i u ∂_j v + ∑_i ∫_Ω b_i ∂_i u v + ∫_Ω c u v`.

The theorem below is the Fredholm alternative for that problem (Evans, *Partial
Differential Equations* (2nd ed.), §6.2.3, Theorem 4(i), p. 321): exactly one of the two
alternatives holds. Either the homogeneous problem `L u = 0` has a weak solution other
than `0`, or `L u = f` has exactly one weak solution for every bounded functional `f`.

## Encoding of `H_0^1(Ω)`

`H_0^1(Ω)` is realised as the closure of the smooth compactly supported functions inside
the graph space `L²(Ω) × (L²(Ω))^d`, carrying the `H¹` inner product. An element `U` of
that ambient space is a `(d+1)`-tuple of `L²` classes: coordinate `0` is the function and
coordinate `i.succ` is its `i`-th partial derivative. A test function `φ` enters as the
tuple `(φ, ∂_1 φ, …, ∂_d φ)`, and `H_0^1(Ω)` is the topological closure of the span of
those tuples. So a member of `H_0^1(Ω)` carries its weak gradient with it, and
`(U : H1amb Ω) 0` denotes the function while `(U : H1amb Ω) i.succ` denotes `∂_i u`.

The compactness of the embedding `H_0^1(Ω) ↪ L²(Ω)`, which for a bounded `Ω` is the
Rellich-Kondrachov theorem, enters as a hypothesis.
-/

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

noncomputable section

namespace Palomar

variable {d : ℕ}

/-! ### The graph encoding of `H_0^1(Ω)` -/

/-- The real `L²` space on a domain `Ω ⊆ ℝ^d` (restricted Lebesgue measure). -/
abbrev L2D (Ω : Set (EuclideanSpace ℝ (Fin d))) : Type :=
  Lp ℝ 2 (volume.restrict Ω)

/-- Ambient Hilbert space for the graph encoding: a function value together with `d`
gradient components, carrying the ℓ² (`H¹`) inner product. Coordinate `0` is the
function; coordinate `i.succ` is the `i`-th weak partial derivative. -/
abbrev H1amb (Ω : Set (EuclideanSpace ℝ (Fin d))) : Type :=
  PiLp 2 (fun _ : Fin (d + 1) => L2D Ω)

/-- The `i`-th classical partial derivative of `φ` (a directional `fderiv`). -/
def partialD (i : Fin d) (φ : EuclideanSpace ℝ (Fin d) → ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)

/-- A smooth, compactly supported test function whose support sits inside `Ω`. -/
def IsTestFn (Ω : Set (EuclideanSpace ℝ (Fin d))) (φ : EuclideanSpace ℝ (Fin d) → ℝ) :
    Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

namespace IsTestFn

variable {Ω : Set (EuclideanSpace ℝ (Fin d))} {φ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- A test function is continuous. -/
lemma continuous (h : IsTestFn Ω φ) : Continuous φ := h.1.continuous

/-- Each partial derivative of a test function is continuous. -/
lemma continuous_partialD (h : IsTestFn Ω φ) (i : Fin d) : Continuous (partialD i φ) :=
  ((h.1.continuous_fderiv (by simp)).clm_apply continuous_const)

/-- Each partial derivative of a test function has compact support. -/
lemma hasCompactSupport_partialD (h : IsTestFn Ω φ) (i : Fin d) :
    HasCompactSupport (partialD i φ) :=
  h.2.1.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)

/-- A test function lies in `L²(Ω)`. -/
lemma mem_lp (h : IsTestFn Ω φ) : MemLp φ 2 (volume.restrict Ω) :=
  h.continuous.memLp_of_hasCompactSupport h.2.1

/-- Each partial derivative of a test function lies in `L²(Ω)`. -/
lemma memLp_partialD (h : IsTestFn Ω φ) (i : Fin d) :
    MemLp (partialD i φ) 2 (volume.restrict Ω) :=
  (h.continuous_partialD i).memLp_of_hasCompactSupport (h.hasCompactSupport_partialD i)

/-- The `L²(Ω)` class of a test function. -/
def testCls (h : IsTestFn Ω φ) : L2D Ω := h.mem_lp.toLp φ

/-- The `L²(Ω)` class of the `i`-th partial derivative of a test function. -/
def partialCls (h : IsTestFn Ω φ) (i : Fin d) : L2D Ω :=
  (h.memLp_partialD i).toLp (partialD i φ)

/-- A test function embedded as its graph `(φ, ∇φ)` in the ambient space: coordinate `0`
is the function, coordinate `i.succ` its `i`-th classical (equivalently weak) partial. -/
def testGraph (h : IsTestFn Ω φ) : H1amb Ω :=
  WithLp.toLp 2 (Fin.cons h.testCls (fun i => h.partialCls i))

end IsTestFn

/-- The set of test-function graphs over `Ω`. -/
def testGraphSet (Ω : Set (EuclideanSpace ℝ (Fin d))) : Set (H1amb Ω) :=
  { U | ∃ (φ : EuclideanSpace ℝ (Fin d) → ℝ) (h : IsTestFn Ω φ), U = h.testGraph }

/-- `H_0^1(Ω)`: the closure of the smooth compactly supported functions inside the
ambient `H¹` space. As a topological closure it is a closed, complete, real Hilbert
space. -/
def H01 (Ω : Set (EuclideanSpace ℝ (Fin d))) : Submodule ℝ (H1amb Ω) :=
  (Submodule.span ℝ (testGraphSet Ω)).topologicalClosure

/-- The embedding `H_0^1(Ω) ↪ L²(Ω)`, `U ↦ U 0`, as a continuous linear map: the
projection onto coordinate `0` precomposed with the inclusion. -/
def embL2 (Ω : Set (EuclideanSpace ℝ (Fin d))) : H01 Ω →L[ℝ] L2D Ω :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d + 1) => L2D Ω) (0 : Fin (d + 1))).comp
    (H01 Ω).subtypeL

/-! ### The operator and its bilinear form -/

/-- A second-order divergence-form operator
`L u = -∂_j (a_{ij} ∂_i u) + b_i ∂_i u + c u` with measurable coefficients, bounded by
`Λ`, `Bsup` and `Csup` respectively, whose principal part is uniformly elliptic with
constant `lam`. No sign condition is imposed on `c` and no smallness condition on `b`. -/
structure EllipticOperator (d : ℕ) where
  /-- The principal coefficient matrix. -/
  a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ
  /-- The transport (first-order) coefficients. -/
  b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ
  /-- The zeroth-order coefficient. -/
  c : EuclideanSpace ℝ (Fin d) → ℝ
  /-- The ellipticity constant. -/
  lam : ℝ
  /-- A uniform sup bound on the entries of `a`. -/
  Λ : ℝ
  /-- A uniform sup bound on the transport field. -/
  Bsup : ℝ
  /-- A uniform sup bound on the zeroth-order coefficient. -/
  Csup : ℝ
  /-- The ellipticity constant is strictly positive. -/
  lam_pos : 0 < lam
  /-- The sup bound on `a` is nonnegative. -/
  Λ_nonneg : 0 ≤ Λ
  /-- The sup bound on `b` is nonnegative. -/
  Bsup_nonneg : 0 ≤ Bsup
  /-- The sup bound on `c` is nonnegative. -/
  Csup_nonneg : 0 ≤ Csup
  /-- Every entry of `a` is measurable. -/
  a_meas : ∀ i j, Measurable (fun x => a x i j)
  /-- Every component of `b` is measurable. -/
  b_meas : ∀ i, Measurable (fun x => b x i)
  /-- The zeroth-order coefficient is measurable. -/
  c_meas : Measurable c
  /-- Every entry of `a` is bounded by `Λ` almost everywhere. -/
  a_bdd : ∀ i j, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |a x i j| ≤ Λ
  /-- Every component of `b` is bounded by `Bsup` almost everywhere. -/
  b_bdd : ∀ i, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |b x i| ≤ Bsup
  /-- The zeroth-order coefficient is bounded by `Csup` almost everywhere. -/
  c_bdd : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |c x| ≤ Csup
  /-- Uniform ellipticity: `∑_{ij} a_{ij}(x) ξ_i ξ_j ≥ lam |ξ|²` for almost every `x`. -/
  elliptic : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
    ∀ ξ : Fin d → ℝ, lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j

/-- The bilinear form of the operator,
`B[u, v] = ∑_{ij} ∫_Ω a_{ij} ∂_i u ∂_j v + ∑_i ∫_Ω b_i ∂_i u v + ∫_Ω c u v`,
read off the graph coordinates: `(U : H1amb Ω) 0` is `u` and `(U : H1amb Ω) i.succ` is
`∂_i u`. -/
def weakForm (Op : EllipticOperator d) (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (U V : H01 Ω) : ℝ :=
  (∑ i : Fin d, ∑ j : Fin d,
      ∫ x in Ω, Op.a x i j * ((U : H1amb Ω) i.succ x : ℝ) * ((V : H1amb Ω) j.succ x : ℝ))
    + (∑ i : Fin d,
        ∫ x in Ω, Op.b x i * ((U : H1amb Ω) i.succ x : ℝ) * ((V : H1amb Ω) 0 x : ℝ))
    + ∫ x in Ω, Op.c x * ((U : H1amb Ω) 0 x : ℝ) * ((V : H1amb Ω) 0 x : ℝ)

/-! ### The Fredholm alternative -/

/-- **The Fredholm alternative for the elliptic Dirichlet problem** (Evans, *Partial
Differential Equations* (2nd ed.), §6.2.3, Theorem 4(i), p. 321). Let `L` be a
second-order divergence-form operator with measurable bounded coefficients and uniformly
elliptic principal part, on a domain whose embedding `H_0^1(Ω) ↪ L²(Ω)` is compact.
Then exactly one of the following holds.

* The homogeneous problem `L u = 0` has a weak solution `u ≠ 0`, that is, some `u ≠ 0` in
  `H_0^1(Ω)` with `B[u, v] = 0` for every `v ∈ H_0^1(Ω)`.
* The problem `L u = f` has exactly one weak solution for every bounded linear functional
  `f` on `H_0^1(Ω)`.

The two alternatives exclude one another, since a nonzero solution of the homogeneous
problem can be added to any solution of the inhomogeneous one. -/
theorem fredholm_alternative (Op : EllipticOperator d)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hRellich : IsCompactOperator (embL2 Ω)) :
    (∃ u : H01 Ω, u ≠ 0 ∧ ∀ v : H01 Ω, weakForm Op Ω u v = 0)
      ∨ (∀ f : H01 Ω →L[ℝ] ℝ, ∃! u : H01 Ω, ∀ v : H01 Ω, weakForm Op Ω u v = f v) := by
  sorry

end Palomar
