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
# Solvability theory for second-order divergence-form elliptic operators

Let `Ω ⊆ ℝ^d` and let

  `L u = -∂_j (a_{ij} ∂_i u) + b_i ∂_i u + c u`

be a second-order operator in divergence form whose coefficients are measurable and
bounded and whose principal part is uniformly elliptic, `∑_{ij} a_{ij}(x) ξ_i ξ_j ≥ λ |ξ|²`
for almost every `x` and every `ξ`. The drift `b` is unrestricted and `c` obeys no sign
condition, so the operator is in general non-symmetric. The weak Dirichlet problem seeks
`u ∈ H_0^1(Ω)` with `B[u, v] = ⟨f, v⟩` for every `v ∈ H_0^1(Ω)`, where

  `B[u, v] = ∑_{ij} ∫_Ω a_{ij} ∂_i u ∂_j v + ∑_i ∫_Ω b_i ∂_i u v + ∫_Ω c u v`.

Six results are stated below, all from Evans, *Partial Differential Equations* (2nd ed.),
§6.2, on a bounded open `Ω` with no boundary hypothesis, the first asking nothing of `Ω`:

* the Gårding inequality (§6.2.2, Theorem 2, p. 318);
* existence, uniqueness and the a-priori bound at `b = 0`, `c ≥ 0` (§6.2.2, Thm 3, p. 319);
* the Fredholm alternative (§6.2.3, Theorem 4(i), p. 321);
* solvability against the transpose problem (§6.2.3, Theorem 4(iii), p. 321);
* the discrete set of `μ` off which `L u = μ u + f` is solvable (§6.2.3, Thm 5, p. 323);
* boundedness of the inverse off that set (§6.2.3, Theorem 6, p. 324).

## Encoding of `H_0^1(Ω)`

`H_0^1(Ω)` is realised as the closure of the smooth compactly supported functions inside
the graph space `L²(Ω) × (L²(Ω))^d`, carrying the `H¹` inner product. An element `U` is a
`(d+1)`-tuple of `L²` classes: coordinate `0` is the function, coordinate `i.succ` its
`i`-th partial derivative. A test function `φ` enters as `(φ, ∂_1 φ, …, ∂_d φ)`, and
`H_0^1(Ω)` is the topological closure of the span of those tuples, so a member carries its
weak gradient with it. Openness keeps that space non-trivial: a test function has
`tsupport φ ⊆ Ω`, so on a set with empty interior every test function vanishes.
Compactness of the embedding `H_0^1(Ω) ↪ L²(Ω)`, the Rellich-Kondrachov theorem, is proved
for a bounded `Ω` rather than assumed, so it appears in none of the statements below.
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

/-- The `L²` pairing of the function coordinates, `⟨u, v⟩ = ∫_Ω u v`. A spectral shift
`L u + μ u` enters the weak formulation through it. -/
def zerothPairing (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : H01 Ω) : ℝ :=
  ∫ x in Ω, ((U : H1amb Ω) 0 x : ℝ) * ((V : H1amb Ω) 0 x : ℝ)

/-- The pairing of an `L²(Ω)` datum against the function coordinate, `⟨f, v⟩ = ∫_Ω f v`.
An `L²` right-hand side enters the weak problem through it. -/
def datumPairing {Ω : Set (EuclideanSpace ℝ (Fin d))} (f : L2D Ω) (V : H01 Ω) : ℝ :=
  ∫ x in Ω, (f x : ℝ) * ((V : H1amb Ω) 0 x : ℝ)

/-! ### The Gårding inequality -/

/-- **The Gårding inequality** (Evans, *Partial Differential Equations* (2nd ed.),
§6.2.2, Theorem 2, p. 318). The form is coercive on `H_0^1(Ω)` after a shift by a
multiple of the `L²` norm,

`(λ/2) ‖u‖²_{H¹} ≤ B[u, u] + γ ‖u‖²_{L²}`,   `γ = λ/2 + C + d B² / (2λ)`,

for every `u ∈ H_0^1(Ω)` and any `Ω`, where `B` and `C` are the bounds it supplies,
`|b_i| ≤ B` and `|c| ≤ C` almost everywhere, neither asked to be an essential supremum, so
a looser bound gives a larger shift. Removing the shift takes more than `b = 0` and
`c ≥ 0`: coercivity in the `H¹` norm needs a Poincaré inequality, so it holds on a bounded
domain, as in the next result. -/
theorem garding (Op : EllipticOperator d) (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (U : H01 Ω) :
    Op.lam / 2 * ‖U‖ ^ 2
      ≤ weakForm Op Ω U U
        + (Op.lam / 2 + Op.Csup + (d : ℝ) * Op.Bsup ^ 2 / (2 * Op.lam))
            * ‖(U : H1amb Ω) 0‖ ^ 2 := by
  sorry

/-! ### Existence and uniqueness for a nonnegative zeroth-order coefficient -/

/-- **First Existence Theorem for weak solutions** (Evans, §6.2.2, Theorem 3, p. 319).
On a bounded `Ω`, with no drift and a nonnegative zeroth-order coefficient, the Dirichlet
problem `L u = f` has exactly one weak solution for every `f ∈ L²(Ω)`, and that solution
obeys `‖u‖_{H¹} ≤ ((C_P + 1) / λ) ‖f‖_{L²}` for some `C_P ≥ 0`, quantified after `Ω` and
the operator, so it is not asserted to depend on the domain alone. Evans asks for `c ≥ 0`
on `U`; the hypotheses here are the almost-everywhere forms on `Ω`. -/
theorem weak_solution_of_nonneg_zeroth {n : ℕ} (Op : EllipticOperator (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω)
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ f : L2D Ω,
      (∃! u : H01 Ω, ∀ v : H01 Ω, weakForm Op Ω u v = datumPairing f v)
        ∧ ∀ u : H01 Ω, (∀ v : H01 Ω, weakForm Op Ω u v = datumPairing f v) →
            ‖u‖ ≤ (CP + 1) / Op.lam * ‖f‖ := by
  sorry

/-! ### The Fredholm alternative -/

/-- **Second Existence Theorem for weak solutions** (Evans, §6.2.3, Theorem 4(i),
p. 321). On a bounded open `Ω`, exactly one of the following holds. Either the
homogeneous problem `L u = 0` has a weak solution `u ≠ 0`, or `L u = f` has exactly one
weak solution for every bounded linear functional `f` on `H_0^1(Ω)`. The two exclude one
another: a nonzero solution of the homogeneous problem adds to any solution of the
inhomogeneous one. -/
theorem fredholm_alternative (Op : EllipticOperator d)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) :
    (∃ u : H01 Ω, u ≠ 0 ∧ ∀ v : H01 Ω, weakForm Op Ω u v = 0)
      ∨ (∀ f : H01 Ω →L[ℝ] ℝ, ∃! u : H01 Ω,
          ∀ v : H01 Ω, weakForm Op Ω u v = f v) := by
  sorry

/-- **Solvability against the transpose problem** (Evans, §6.2.3, Theorem 4(iii),
p. 321). `L u = f` has a weak solution exactly when `f` annihilates every weak solution
of the transpose problem `B[v, w] = 0`, which is the weak form of the formal adjoint
`L* w = -∂_i (a_{ij} ∂_j w) - ∂_i (b_i w) + c w`. Nothing here asks a coefficient to be
differentiable, so the adjoint appears only through the transposed form. -/
theorem solvable_iff_orthogonal_transpose (Op : EllipticOperator d)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (f : H01 Ω →L[ℝ] ℝ) :
    (∃ u : H01 Ω, ∀ v : H01 Ω, weakForm Op Ω u v = f v)
      ↔ ∀ w : H01 Ω, (∀ v : H01 Ω, weakForm Op Ω v w = 0) → f w = 0 := by
  sorry

/-! ### The discrete set of exceptional shifts -/

/-- **Third Existence Theorem for weak solutions** (Evans, §6.2.3, Theorem 5, p. 323).
On a bounded open `Ω` there is an at most countable set `Σ ⊆ ℝ`, finite below every
level, such that `L u = μ u + f` is uniquely solvable for every `f ∈ L²(Ω)` exactly when
`μ ∉ Σ`, so the weak form below reads `B[u, v] = μ ⟨u, v⟩_{L²} + ⟨f, v⟩_{L²}`. Evans
records `Σ` as the eigenvalues of `L`, the `μ` at which `L w = μ w` has a nontrivial weak
solution; the statement here fixes `Σ` by the solvability property alone. -/
theorem existence_three (Op : EllipticOperator d)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) :
    ∃ S : Set ℝ, S.Countable ∧ (∀ C : ℝ, (S ∩ Set.Iic C).Finite) ∧
      ∀ lam : ℝ, lam ∉ S ↔ ∀ f : L2D Ω, ∃! u : H01 Ω, ∀ v : H01 Ω,
        weakForm Op Ω u v = lam * zerothPairing Ω u v + datumPairing f v := by
  sorry

/-! ### Boundedness of the inverse -/

/-- **Boundedness of the inverse** (Evans, §6.2.3, Theorem 6, p. 324). At a `μ` where
`L u = μ u + f` is uniquely solvable for every right-hand side, the solution operator is
bounded from `L²(Ω)` to `L²(Ω)`: one constant serves every datum and every solution. -/
theorem resolvent_bound (Op : EllipticOperator d)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {lam : ℝ}
    (hlam : ∀ f : H01 Ω →L[ℝ] ℝ, ∃! u : H01 Ω, ∀ v : H01 Ω,
      weakForm Op Ω u v = lam * zerothPairing Ω u v + f v) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : L2D Ω, ∀ u : H01 Ω,
      (∀ v : H01 Ω,
        weakForm Op Ω u v = lam * zerothPairing Ω u v + datumPairing f v) →
      ‖(u : H1amb Ω) 0‖ ≤ C * ‖f‖ := by
  sorry

end Palomar
