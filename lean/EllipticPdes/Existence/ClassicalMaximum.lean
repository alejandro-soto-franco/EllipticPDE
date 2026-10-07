/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import EllipticPdes.Sobolev.Basic
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Topology.Connected.Clopen

/-!
# Classical weak maximum principle

The weak maximum principle for a `C²` subsolution of a non-divergence-form elliptic equation
on a bounded open set: the maximum over the closure is attained on the boundary.

The results are stated on a finite-dimensional real inner product space `E` for the operator
`L u = -tr (A D²u) + D u (b) + c u` defined below, with `A x` a
symmetric uniformly elliptic endomorphism field and `b` bounded along a unit vector `e`. At an
interior maximum of a `C²` function the gradient vanishes and the Hessian is negative
semidefinite, so the principal part is nonnegative there; a strict subsolution therefore has no
interior maximum. The general case perturbs by `ε exp(λ ⟪e, x⟫)`, a strict subsolution for `λ`
large, and lets `ε` tend to zero. The Euclidean statements with a coefficient matrix and the
operator `nondivOp` follow from the general ones through the dictionary at the end of the file.

The coefficients are asked to be symmetric, uniformly elliptic and, for the transport term,
bounded on the set; the sources also ask for continuity, which the proof does not use.

## Main declarations

* `IsLocalMax.fderiv_fderiv_nonpos`: the Hessian is negative semidefinite at a local maximum.
* `EllipticPdes.Classical.traceHessian`: `tr (A D²u(x))`, the contraction of the Hessian against an
  endomorphism, defined through the canonical tensor and independent of any basis;
  `traceHessian_nonpos` is the trace inequality.
* `EllipticPdes.Classical.nondivOperator`: the operator `L`, with its linearity lemmas.
* `EllipticPdes.Classical.IsUniformlyElliptic`: the symmetric uniformly elliptic coefficient.
* `EllipticPdes.Classical.expInner`: the perturbation `exp (λ ⟪e, x⟫)` and its image under `L`.
* `EllipticPdes.Classical.weak_maximum_principle`: the weak maximum principle for a
  subsolution with no zeroth-order term.
* `EllipticPdes.Classical.weak_minimum_principle`: the same for a supersolution.
* `EllipticPdes.Classical.weak_maximum_principle_of_nonneg`: the weak maximum principle with
  nonnegative zeroth-order coefficient, through the positive part on the boundary.
* `EllipticPdes.Classical.comparison_principle`, `dirichlet_unique`: the corollaries.
* `EllipticPdes.Classical.nondivOp`: the Euclidean operator with a coefficient matrix, and
  the Euclidean forms of the principles above.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.4.1 Theorem 1 (p. 343) and
Theorem 2 (p. 344);
D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§3.1 Theorem 3.1 (p. 32) and Corollary 3.2 (p. 33);
Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem XI.3.7.
-/

@[expose] public section

open Set Filter Topology InnerProductSpace Metric TensorProduct
open scoped RealInnerProductSpace

noncomputable section

/-- **One-dimensional second-order test.** A function with a continuous second derivative
near `0` and a local maximum at `0` has nonpositive second derivative at `0`. -/
theorem IsLocalMax.deriv2_nonpos {φ φ' φ'' : ℝ → ℝ} (hmax : IsLocalMax φ 0)
    (h1 : ∀ᶠ t in 𝓝 0, HasDerivAt φ (φ' t) t) (h2 : ∀ᶠ t in 𝓝 0, HasDerivAt φ' (φ'' t) t)
    (hc : ContinuousAt φ'' 0) : φ'' 0 ≤ 0 := by
  by_contra hpos
  have h0 : φ' 0 = 0 := hmax.hasDerivAt_eq_zero h1.self_of_nhds
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff.mp
    (h1.and (h2.and (hc.eventually (lt_mem_nhds (lt_of_not_ge hpos)))))
  have hmem : ∀ t ∈ Ioo (-ε) ε, dist t 0 < ε := fun t ht => by
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact ht
  have hmono : StrictMonoOn φ' (Ioo (-ε) ε) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) (fun t ht => ?_) fun t ht => ?_
    · exact (hall (hmem t ht)).2.1.continuousAt.continuousWithinAt
    · rw [interior_Ioo] at ht
      rw [(hall (hmem t ht)).2.1.deriv]
      exact (hall (hmem t ht)).2.2
  have hpos' : ∀ t ∈ Ioo 0 ε, 0 < φ' t := fun t ht => by
    simpa [h0] using hmono ⟨by linarith, hε⟩ ⟨by linarith [ht.1], ht.2⟩ ht.1
  have hφmono : StrictMonoOn φ (Ico 0 ε) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico _ _) (fun t ht => ?_) fun t ht => ?_
    · exact (hall (hmem t ⟨by linarith [ht.1], ht.2⟩)).1.continuousAt.continuousWithinAt
    · rw [interior_Ico] at ht
      rw [(hall (hmem t ⟨by linarith [ht.1], ht.2⟩)).1.deriv]
      exact hpos' t ht
  obtain ⟨η, hη, hmax'⟩ := Metric.eventually_nhds_iff.mp hmax
  obtain ⟨t, ht0, htε, htη⟩ : ∃ t : ℝ, 0 < t ∧ t < ε ∧ t < η :=
    ⟨(ε ⊓ η) / 2, by positivity, by linarith [inf_le_left (a := ε) (b := η)],
      by linarith [inf_le_right (a := ε) (b := η)]⟩
  have hlt := hφmono ⟨le_rfl, hε⟩ ⟨ht0.le, htε⟩ ht0
  have hle := hmax' (y := t) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht0]; exact htη)
  linarith

section Line
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The line `s ↦ x₀ + s ξ` has velocity `ξ`. -/
theorem hasDerivAt_add_smul (x₀ ξ : E) (t : ℝ) : HasDerivAt (fun s : ℝ => x₀ + s • ξ) ξ t := by
  simpa using ((hasDerivAt_id t).smul_const ξ).const_add x₀

/-- The derivative of a differentiable function along a line. -/
theorem HasDerivAt.comp_line {u : E → ℝ} {x₀ ξ : E} {t : ℝ}
    (hu : DifferentiableAt ℝ u (x₀ + t • ξ)) :
    HasDerivAt (fun s => u (x₀ + s • ξ)) (fderiv ℝ u (x₀ + t • ξ) ξ) t :=
  hu.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_add_smul x₀ ξ t)

/-- **Hessian at a local maximum.** A function `C²` at a local maximum `x₀` has
`D²u(x₀)(ξ, ξ) ≤ 0` for every direction `ξ`. -/
theorem IsLocalMax.fderiv_fderiv_nonpos {u : E → ℝ} {x₀ : E} (hmax : IsLocalMax u x₀)
    (hu : ContDiffAt ℝ 2 u x₀) (ξ : E) : fderiv ℝ (fderiv ℝ u) x₀ ξ ξ ≤ 0 := by
  have hline : Continuous fun s : ℝ => x₀ + s • ξ :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hline0 : Tendsto (fun s : ℝ => x₀ + s • ξ) (𝓝 0) (𝓝 x₀) := by
    simpa using hline.tendsto 0
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 u (x₀ + s • ξ) :=
    hline0.eventually (hu.eventually (by decide))
  have hd2 : ∀ y, ContDiffAt ℝ 2 u y → DifferentiableAt ℝ (fderiv ℝ u) y := fun y hy =>
    (hy.fderiv_right (m := 1) (by decide)).differentiableAt (by simp)
  refine IsLocalMax.deriv2_nonpos (φ := fun s => u (x₀ + s • ξ))
    (φ' := fun s => fderiv ℝ u (x₀ + s • ξ) ξ)
    (φ'' := fun s => fderiv ℝ (fderiv ℝ u) (x₀ + s • ξ) ξ ξ) ?_ ?_ ?_ ?_ |>.trans_eq' (by simp)
  · have hm0 : IsLocalMax u ((fun s : ℝ => x₀ + s • ξ) 0) := by simpa using hmax
    exact hm0.comp_continuous (g := fun s : ℝ => x₀ + s • ξ) (b := 0) hline.continuousAt
  · filter_upwards [hev] with s hs
    exact HasDerivAt.comp_line (hs.differentiableAt (by simp))
  · filter_upwards [hev] with s hs
    have h := ((hd2 _ hs).hasFDerivAt.clm_apply
      (hasFDerivAt_const ξ (x₀ + s • ξ))).comp_hasDerivAt s (hasDerivAt_add_smul x₀ ξ s)
    exact h.congr_deriv (by simp)
  · have hcont : ContinuousAt (fderiv ℝ (fderiv ℝ u)) x₀ :=
      ((hu.fderiv_right (m := 1) (by decide)).fderiv_right (m := 0) (by decide)).continuousAt
    exact ((hcont.comp_of_eq hline.continuousAt (by simp)).clm_apply continuousAt_const).clm_apply
      continuousAt_const

end Line

namespace EllipticPdes.Classical

section Hessian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The contraction `tr (A D²u(x))` of the Hessian of `u` at `x` against an endomorphism `A`,
that is `∑ᵢ D²u(x)(A vᵢ, vᵢ)` for any orthonormal basis `v`
(`traceHessian_eq_sum`). It is the second-order part of a non-divergence-form operator, and
`traceHessian 1 u` is the Laplacian. -/
noncomputable def traceHessian (A : E →L[ℝ] E) (u : E → ℝ) (x : E) : ℝ :=
  tensorIteratedFDerivTwo ℝ u x
    (TensorProduct.map A.toLinearMap LinearMap.id (canonicalCovariantTensor E))

/-- `tr (A D²u(x))` is `∑ᵢ D²u(x)(A vᵢ, vᵢ)` for every orthonormal basis `v`. -/
theorem traceHessian_eq_sum {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (u : E → ℝ) (x : E) :
    traceHessian A u x = ∑ i, fderiv ℝ (fderiv ℝ u) x (A (v i)) (v i) := by
  simp [traceHessian, canonicalCovariantTensor_eq_sum E v,
    tensorIteratedFDerivTwo_eq_iteratedFDeriv,
    iteratedFDeriv_two_apply, map_sum]

/-- `tr (A D²u(x))` in terms of the iterated derivative. -/
theorem traceHessian_eq_sum_iteratedFDeriv {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E)
    (A : E →L[ℝ] E) (u : E → ℝ) (x : E) :
    traceHessian A u x = ∑ i, iteratedFDeriv ℝ 2 u x ![A (v i), v i] := by
  simp [traceHessian, canonicalCovariantTensor_eq_sum E v,
    tensorIteratedFDerivTwo_eq_iteratedFDeriv,
    map_sum]

/-- `tr (A D²u)` is linear in `u` at a point where both functions are `C²`. -/
theorem traceHessian_add_smul (A : E →L[ℝ] E) {u v : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    (hv : ContDiffAt ℝ 2 v x) (ε : ℝ) :
    traceHessian A (fun y => u y + ε * v y) x = traceHessian A u x + ε * traceHessian A v x := by
  have h : iteratedFDeriv ℝ 2 (fun y => u y + ε * v y) x
      = iteratedFDeriv ℝ 2 u x + ε • iteratedFDeriv ℝ 2 v x := by
    rw [← iteratedFDeriv_const_smul_apply' (a := ε) hv]
    exact iteratedFDeriv_add_apply hu (hv.const_smul ε)
  simp only [traceHessian_eq_sum_iteratedFDeriv (stdOrthonormalBasis ℝ E), h, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  simp

/-- `tr (A D²u)` vanishes on constants. -/
theorem traceHessian_const (A : E →L[ℝ] E) (K : ℝ) (x : E) :
    traceHessian A (fun _ => K) x = 0 := by
  simp [traceHessian_eq_sum_iteratedFDeriv (stdOrthonormalBasis ℝ E),
    iteratedFDeriv_const_of_ne two_ne_zero]

/-- **Trace inequality.** For a symmetric positive semidefinite `A` and a function whose Hessian
at `x` is negative semidefinite, `tr (A D²u(x)) ≤ 0`. In an eigenbasis of `A` the sum is
`∑ μᵢ D²u(x)(wᵢ, wᵢ)` with `μᵢ ≥ 0`. -/
theorem traceHessian_nonpos {A : E →L[ℝ] E} (hsymm : (A : E →ₗ[ℝ] E).IsSymmetric)
    (hpsd : ∀ ξ, 0 ≤ ⟪A ξ, ξ⟫) {u : E → ℝ} {x : E}
    (h : ∀ ξ, fderiv ℝ (fderiv ℝ u) x ξ ξ ≤ 0) : traceHessian A u x ≤ 0 := by
  rw [traceHessian_eq_sum (hsymm.eigenvectorBasis rfl)]
  refine Finset.sum_nonpos fun i _ => ?_
  set w := hsymm.eigenvectorBasis rfl i
  have hAw : A w = (hsymm.eigenvalues rfl i) • w := hsymm.apply_eigenvectorBasis rfl i
  have hμ : 0 ≤ hsymm.eigenvalues rfl i := by
    have := hpsd w
    rw [hAw, real_inner_smul_left, real_inner_self_eq_norm_sq,
      (hsymm.eigenvectorBasis rfl).norm_eq_one i] at this
    simpa using this
  rw [hAw, map_smul]
  exact mul_nonpos_of_nonneg_of_nonpos hμ (h w)

/-- `tr (A D²u)` is nonpositive at a local maximum of a `C²` function, for `A` symmetric and
positive semidefinite. -/
theorem traceHessian_nonpos_of_isLocalMax {A : E →L[ℝ] E} (hsymm : (A : E →ₗ[ℝ] E).IsSymmetric)
    (hpsd : ∀ ξ, 0 ≤ ⟪A ξ, ξ⟫) {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    (hmax : IsLocalMax u x) : traceHessian A u x ≤ 0 :=
  traceHessian_nonpos hsymm hpsd (hmax.fderiv_fderiv_nonpos hu)

/-- **Non-divergence-form operator** `L u = -tr (A D²u) + D u (b) + c u`. -/
noncomputable def nondivOperator (A : E → E →L[ℝ] E) (b : E → E) (c : E → ℝ) (u : E → ℝ)
    (x : E) : ℝ :=
  -traceHessian (A x) u x + fderiv ℝ u x (b x) + c x * u x

/-- **Operator at an interior local maximum.** The gradient vanishes and the Hessian
contraction is nonpositive, so `L u ≥ c u` there. -/
theorem le_nondivOperator_of_isLocalMax {A : E → E →L[ℝ] E} {b : E → E} {c : E → ℝ} {x : E}
    (hsymm : (A x : E →ₗ[ℝ] E).IsSymmetric) (hpsd : ∀ ξ, 0 ≤ ⟪A x ξ, ξ⟫) {u : E → ℝ}
    (hu : ContDiffAt ℝ 2 u x) (hmax : IsLocalMax u x) : c x * u x ≤ nondivOperator A b c u x := by
  have := traceHessian_nonpos_of_isLocalMax hsymm hpsd hu hmax
  rw [nondivOperator, hmax.fderiv_eq_zero]
  simp only [zero_apply, add_zero]
  linarith

/-- **Linearity of the operator** at a point where both functions are `C²`. -/
theorem nondivOperator_add_smul (A : E → E →L[ℝ] E) (b : E → E) (c : E → ℝ) {u v : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) (ε : ℝ) :
    nondivOperator A b c (fun y => u y + ε * v y) x
      = nondivOperator A b c u x + ε * nondivOperator A b c v x := by
  have h1 := hu.differentiableAt (by simp)
  have h2 := hv.differentiableAt (by simp)
  simp only [nondivOperator, traceHessian_add_smul _ hu hv, fderiv_fun_add h1 (h2.const_mul ε),
    fderiv_const_mul h2 ε, add_apply, smul_apply,
    smul_eq_mul]
  ring

/-- The operator on a constant. -/
theorem nondivOperator_const (A : E → E →L[ℝ] E) (b : E → E) (c : E → ℝ) (K : ℝ) (x : E) :
    nondivOperator A b c (fun _ => K) x = c x * K := by
  simp [nondivOperator, traceHessian_const]

/-- The operator on a function minus a constant. -/
theorem nondivOperator_sub_const (A : E → E →L[ℝ] E) (b : E → E) (c : E → ℝ) {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (K : ℝ) :
    nondivOperator A b c (fun y => u y - K) x = nondivOperator A b c u x - c x * K := by
  have h := nondivOperator_add_smul A b c hu (contDiffAt_const (c := (1 : ℝ))) (-K) (x := x)
  simp only [nondivOperator_const, mul_one] at h
  have e : (fun y => u y - K) = fun y => u y + -K := by ext; ring
  rw [e, h]
  ring

/-- The operator on a negative. -/
theorem nondivOperator_neg (A : E → E →L[ℝ] E) (b : E → E) (c : E → ℝ) {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) :
    nondivOperator A b c (fun y => -u y) x = -nondivOperator A b c u x := by
  have h := nondivOperator_add_smul A b c (contDiffAt_const (c := (0 : ℝ))) hu (-1) (x := x)
  simp only [nondivOperator_const, mul_zero, zero_add, neg_mul, one_mul] at h
  simpa using h

/-- The operator on a difference. -/
theorem nondivOperator_sub (A : E → E →L[ℝ] E) (b : E → E) (c : E → ℝ) {u v : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    nondivOperator A b c (fun y => u y - v y) x
      = nondivOperator A b c u x - nondivOperator A b c v x := by
  have h := nondivOperator_add_smul A b c hu hv (-1)
  have e : (fun y => u y + (-1) * v y) = fun y => u y - v y := by ext; ring
  rw [e] at h
  rw [h]
  ring

/-- The operator at a point depends only on the germ of the function. -/
theorem nondivOperator_congr_of_eventuallyEq (A : E → E →L[ℝ] E) (b : E → E) (c : E → ℝ)
    {u v : E → ℝ} {x : E} (h : u =ᶠ[𝓝 x] v) :
    nondivOperator A b c u x = nondivOperator A b c v x := by
  simp only [nondivOperator, traceHessian_eq_sum_iteratedFDeriv (stdOrthonormalBasis ℝ E),
    h.fderiv_eq, h.eq_of_nhds, (h.iteratedFDeriv ℝ 2).eq_of_nhds]

/-- Changing the zeroth-order coefficient changes the operator by the difference times the
function. -/
theorem nondivOperator_congr_zeroth (A : E → E →L[ℝ] E) (b : E → E) (c c' : E → ℝ) (u : E → ℝ)
    (x : E) : nondivOperator A b c' u x = nondivOperator A b c u x + (c' x - c x) * u x := by
  unfold nondivOperator
  ring


/-- The trace of `A` against a Hessian of rank one plus a multiple of the inner product:
if `D²u(x)(ξ, η) = α ⟪p, ξ⟫ ⟪q, η⟫ + β ⟪ξ, η⟫` then `tr (A D²u(x)) = α ⟪p, A q⟫ + β tr A`. -/
theorem traceHessian_eq_of_fderiv_fderiv {A : E →L[ℝ] E} {u : E → ℝ} {x : E} {α β : ℝ} {p q : E}
    (h : ∀ ξ η, fderiv ℝ (fderiv ℝ u) x ξ η = α * ⟪p, ξ⟫ * ⟪q, η⟫ + β * ⟪ξ, η⟫) :
    traceHessian A u x = α * ⟪p, A q⟫ + β * LinearMap.trace ℝ E (A : E →ₗ[ℝ] E) := by
  let v := stdOrthonormalBasis ℝ E
  have h1 : ⟪p, A q⟫ = ∑ i, ⟪p, A (v i)⟫ * ⟪q, v i⟫ := by
    conv_lhs => rw [← v.sum_repr' q]
    simp [map_sum, inner_sum, real_inner_smul_right, mul_comm, real_inner_comm]
  rw [traceHessian_eq_sum v, LinearMap.trace_eq_sum_inner _ v, h1, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h, real_inner_comm (v i) (A (v i))]
  simp only [ContinuousLinearMap.coe_coe]
  ring

end Hessian

section Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `A` is a symmetric, uniformly elliptic coefficient on `U` with constant `θ`:
`θ ‖ξ‖² ≤ ⟪A x ξ, ξ⟫` for all `x ∈ U`. -/
structure IsUniformlyElliptic (A : E → E →L[ℝ] E) (U : Set E) (θ : ℝ) : Prop where
  /-- The ellipticity constant is positive. -/
  pos : 0 < θ
  /-- The coefficient is symmetric. -/
  symm : ∀ x ∈ U, (A x : E →ₗ[ℝ] E).IsSymmetric
  /-- The quadratic form is bounded below by `θ ‖ξ‖²`. -/
  coercive : ∀ x ∈ U, ∀ ξ, θ * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫

namespace IsUniformlyElliptic

variable {A : E → E →L[ℝ] E} {U V : Set E} {θ : ℝ}

/-- A uniformly elliptic coefficient has a nonnegative quadratic form. -/
theorem psd (h : IsUniformlyElliptic A U θ) {x : E} (hx : x ∈ U) (ξ : E) : 0 ≤ ⟪A x ξ, ξ⟫ :=
  (mul_nonneg h.pos.le (sq_nonneg _)).trans (h.coercive x hx ξ)

/-- Uniform ellipticity restricts to a subset. -/
theorem mono (h : IsUniformlyElliptic A U θ) (hVU : V ⊆ U) : IsUniformlyElliptic A V θ :=
  ⟨h.pos, fun x hx => h.symm x (hVU hx), fun x hx => h.coercive x (hVU hx)⟩

/-- At a unit vector `e` the coefficient is at least `θ`. -/
theorem le_inner_self (h : IsUniformlyElliptic A U θ) {x : E} (hx : x ∈ U) {e : E}
    (he : ‖e‖ = 1) : θ ≤ ⟪A x e, e⟫ := by
  simpa [he] using h.coercive x hx e

end IsUniformlyElliptic

end Elliptic

section ExpInner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The perturbation `x ↦ exp (λ ⟪e, x⟫)`. -/
def expInner (lam : ℝ) (e x : E) : ℝ := Real.exp (lam * ⟪e, x⟫)

/-- The perturbation is positive. -/
theorem expInner_pos (lam : ℝ) (e x : E) : 0 < expInner lam e x := Real.exp_pos _

/-- The perturbation is smooth. -/
theorem contDiff_expInner (lam : ℝ) (e : E) {n : WithTop ℕ∞} : ContDiff ℝ n (expInner lam e) :=
  Real.contDiff_exp.comp (contDiff_const.mul (contDiff_const.inner ℝ contDiff_id))

/-- The derivative of the perturbation. -/
theorem hasFDerivAt_expInner (lam : ℝ) (e x : E) :
    HasFDerivAt (expInner lam e) (expInner lam e x • (lam • innerSL ℝ e)) x := by
  have h1 : HasFDerivAt (fun y : E => lam * ⟪e, y⟫) (lam • innerSL ℝ e) x :=
    (innerSL ℝ e).hasFDerivAt.const_mul lam
  exact (Real.hasDerivAt_exp (lam * ⟪e, x⟫)).comp_hasFDerivAt x h1

/-- The derivative of the perturbation on a vector. -/
theorem fderiv_expInner_apply (lam : ℝ) (e x ξ : E) :
    fderiv ℝ (expInner lam e) x ξ = lam * expInner lam e x * ⟪e, ξ⟫ := by
  simp [(hasFDerivAt_expInner lam e x).fderiv]
  ring

/-- The second derivative of the perturbation. -/
theorem fderiv_fderiv_expInner_apply (lam : ℝ) (e x ξ η : E) :
    fderiv ℝ (fderiv ℝ (expInner lam e)) x ξ η = lam ^ 2 * expInner lam e x * ⟪e, ξ⟫ * ⟪e, η⟫ := by
  have hf : fderiv ℝ (expInner lam e) = fun y => expInner lam e y • (lam • innerSL ℝ e) :=
    funext fun y => (hasFDerivAt_expInner lam e y).fderiv
  rw [hf, ((hasFDerivAt_expInner lam e x).smul_const (lam • innerSL ℝ e)).fderiv]
  simp
  ring

variable [FiniteDimensional ℝ E]

/-- **Operator on the perturbation.** -/
theorem nondivOperator_expInner (A : E → E →L[ℝ] E) (b : E → E) (c : E → ℝ) (lam : ℝ) (e x : E) :
    nondivOperator A b c (expInner lam e) x
      = (-(lam ^ 2 * ⟪e, A x e⟫) + lam * ⟪e, b x⟫ + c x) * expInner lam e x := by
  rw [nondivOperator, traceHessian_eq_of_fderiv_fderiv (α := lam ^ 2 * expInner lam e x) (β := 0)
    (p := e) (q := e) fun ξ η => by simp [fderiv_fderiv_expInner_apply]]
  simp [fderiv_expInner_apply]
  ring

end ExpInner


end EllipticPdes.Classical

section Topology

/-- A bounded nonempty set in a nontrivial real normed space has nonempty frontier. -/
theorem Bornology.IsBounded.frontier_nonempty {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] {U : Set E} (hb : Bornology.IsBounded U) (hne : U.Nonempty) :
    (frontier U).Nonempty := by
  rw [Set.nonempty_iff_ne_empty, Ne, frontier_eq_empty_iff]
  rintro (h | h)
  · exact hne.ne_empty h
  · exact NormedSpace.unbounded_univ ℝ E (h ▸ hb)

/-- A function continuous on the compact closure of a nonempty open set and with no local
maximum in the set attains its maximum over the closure on the frontier. -/
theorem IsOpen.exists_mem_frontier_isMaxOn_of_not_isLocalMax {X : Type*} [TopologicalSpace X]
    {U : Set X} {w : X → ℝ} (hU : IsOpen U) (hcl : IsCompact (closure U)) (hne : U.Nonempty)
    (hw : ContinuousOn w (closure U)) (hno : ∀ z ∈ U, ¬ IsLocalMax w z) :
    ∃ z ∈ frontier U, ∀ x ∈ closure U, w x ≤ w z := by
  obtain ⟨z, hz, hmax⟩ := hcl.exists_isMaxOn (hne.mono subset_closure) hw
  refine ⟨z, ?_, fun x hx => hmax hx⟩
  rw [hU.frontier_eq]
  exact ⟨hz, fun hzU => hno z hzU (hmax.isLocalMax (mem_of_superset (hU.mem_nhds hzU)
    subset_closure))⟩

end Topology

section MatrixTrace

open Matrix

/-- **Trace inequality.** For `A` positive semidefinite and `-H` positive semidefinite,
`∑ᵢⱼ Aᵢⱼ Hᵢⱼ ≤ 0`. Through the spectral theorem `A = U D U*`, the sum is the trace of `A H`,
which is the trace of `D (U* H U)`, a sum of nonnegative eigenvalues times the nonpositive
diagonal entries of `U* H U`. -/
theorem Matrix.PosSemidef.sum_mul_le_zero {n : Type*} [Fintype n]
    {A H : Matrix n n ℝ} (hA : A.PosSemidef) (hH : (-H).PosSemidef) :
    ∑ i, ∑ j, A i j * H i j ≤ 0 := by
  classical
  have hHs : ∀ i j, H i j = H j i := fun i j => by
    have := congrFun (congrFun hH.1 i) j
    simp only [conjTranspose_eq_transpose_of_trivial, transpose_apply, Matrix.neg_apply] at this
    linarith
  have htr : ∑ i, ∑ j, A i j * H i j = trace (A * H) := by
    simp only [trace, diag_apply, mul_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hHs i j]
  set U : Matrix n n ℝ := (hA.1.eigenvectorUnitary : Matrix n n ℝ)
  have hspec : A = U * diagonal hA.1.eigenvalues * star U := by
    have := hA.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [RCLike.ofReal_real_eq_id, U] using this
  have hconj : (star U * (-H) * U).PosSemidef := by
    have := hH.conjTranspose_mul_mul_same U
    rwa [← star_eq_conjTranspose] at this
  have hdiag : ∀ k, (star U * H * U) k k ≤ 0 := fun k => by
    have h1 := hconj.diag_nonneg (i := k)
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply] at h1
    linarith
  rw [htr, show trace (A * H) = trace (diagonal hA.1.eigenvalues * (star U * H * U)) by
    conv_lhs => rw [hspec]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]]
  simp only [trace, diag_apply, diagonal_mul]
  exact Finset.sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos (hA.eigenvalues_nonneg k)
    (hdiag k)

end MatrixTrace

namespace EllipticPdes.Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {A : E → E →L[ℝ] E} {b : E → E} {c : E → ℝ} {U : Set E} {θ B : ℝ}

namespace nondivOperator

/-- **The perturbation is a strict subsolution.** On a set where `A` is uniformly elliptic with
constant `θ` and `⟪b, e⟫ ≤ B` for a unit vector `e`, the function `exp (λ ⟪e, x⟫)` with
`λ = (B + 1) / θ` has `L v < 0` in the absence of a zeroth-order term. -/
theorem expInner_neg (hA : IsUniformlyElliptic A U θ) {e : E} (he : ‖e‖ = 1)
    (hB : 0 ≤ B) (hb : ∀ x ∈ U, ⟪b x, e⟫ ≤ B) {z : E} (hz : z ∈ U) :
    nondivOperator A b (fun _ => 0) (expInner ((B + 1) / θ) e) z < 0 := by
  rw [nondivOperator_expInner]
  have hθ := hA.pos
  have hlam : (B + 1) / θ * θ = B + 1 := div_mul_cancel₀ _ hθ.ne'
  have hlam0 : 0 < (B + 1) / θ := by positivity
  have h1 : θ ≤ ⟪e, A z e⟫ := by simpa [real_inner_comm] using hA.le_inner_self hz he
  have h2 : ⟪e, b z⟫ ≤ B := by simpa [real_inner_comm] using hb z hz
  refine mul_neg_of_neg_of_pos ?_ (expInner_pos _ _ _)
  nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg ((B + 1) / θ)),
    mul_le_mul_of_nonneg_left h2 hlam0.le]

/-- **Weak maximum principle** (Evans §6.4.1 Theorem 1(i), Gilbarg and Trudinger Theorem 3.1,
Guo Theorem XI.3.7(i)). Let `U` be a bounded open nonempty subset of a finite-dimensional real
inner product space, `L` a non-divergence-form operator with symmetric uniformly elliptic
coefficient, no zeroth-order term and transport `b` with `⟪b, e⟫ ≤ B` along a unit vector `e`, and
`u` a function `C²` on `U` and continuous on its closure with `L u ≤ 0` on `U`. Then the maximum
of `u` over the closure is attained on the boundary. -/
theorem weak_maximum_principle (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hA : IsUniformlyElliptic A U θ) {e : E} (he : ‖e‖ = 1) (hb : ∀ x ∈ U, ⟪b x, e⟫ ≤ B)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (huc : ContinuousOn u (closure U))
    (hsub : ∀ x ∈ U, nondivOperator A b (fun _ => 0) u x ≤ 0) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u x ≤ u y := by
  have hcl := hUb.isCompact_closure
  set v := expInner ((max B 0 + 1) / θ) e with hv
  have hvd : ContDiff ℝ 2 v := contDiff_expInner _ _
  have hvc : Continuous v := hvd.continuous
  have hbB : ∀ x ∈ U, ⟪b x, e⟫ ≤ max B 0 := fun x hx => (hb x hx).trans (le_max_left _ _)
  -- for `ε > 0` the maximum of `u + ε v` over the closure lies on the frontier
  have key : ∀ ε > 0, ∃ z ∈ frontier U, ∀ x ∈ closure U, u x + ε * v x ≤ u z + ε * v z :=
    fun ε hε => hU.exists_mem_frontier_isMaxOn_of_not_isLocalMax hcl hUne
      (huc.add (continuousOn_const.mul hvc.continuousOn)) fun z hzU hloc => by
        have hu2 := hu.contDiffAt (hU.mem_nhds hzU)
        have hv2 : ContDiffAt ℝ 2 v z := hvd.contDiffAt
        have h1 := le_nondivOperator_of_isLocalMax (c := fun _ => (0 : ℝ)) (b := b)
          (hA.symm z hzU) (hA.psd hzU) (hu2.add (contDiffAt_const.mul hv2)) hloc
        rw [nondivOperator_add_smul A b _ hu2 hv2] at h1
        have h2 := expInner_neg hA he (le_max_right B 0) hbB hzU
        linarith [hsub z hzU, mul_neg_of_pos_of_neg hε h2]
  have hfr : IsCompact (frontier U) :=
    hcl.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨z₁, hz₁, -⟩ := key 1 one_pos
  obtain ⟨y, hyfr, hymax⟩ := hfr.exists_isMaxOn ⟨z₁, hz₁⟩ (huc.mono frontier_subset_closure)
  refine ⟨y, hyfr, fun x hx => ?_⟩
  obtain ⟨z₀, -, hz₀⟩ := hcl.exists_isMaxOn ⟨x, hx⟩ hvc.continuousOn
  have hM : 0 < v z₀ := expInner_pos _ _ _
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨z, hzfr, hz⟩ := key (η / v z₀) (div_pos hη hM)
  have h1 := hz x hx
  have h2 : u z ≤ u y := hymax hzfr
  have h3 : v z ≤ v z₀ := hz₀ (frontier_subset_closure hzfr)
  have h4 : η / v z₀ * v z ≤ η := by
    calc η / v z₀ * v z ≤ η / v z₀ * v z₀ := by gcongr
      _ = η := div_mul_cancel₀ _ hM.ne'
  have h5 : 0 < η / v z₀ * v x := mul_pos (div_pos hη hM) (expInner_pos _ _ _)
  linarith

/-- **Weak minimum principle for supersolutions** (Evans §6.4.1 Theorem 1(ii)): a supersolution
attains its minimum over the closure on the boundary. -/
theorem weak_minimum_principle (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hA : IsUniformlyElliptic A U θ) {e : E} (he : ‖e‖ = 1) (hb : ∀ x ∈ U, ⟪b x, e⟫ ≤ B)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (huc : ContinuousOn u (closure U))
    (hsup : ∀ x ∈ U, 0 ≤ nondivOperator A b (fun _ => 0) u x) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u y ≤ u x := by
  have hneg : ∀ x ∈ U, nondivOperator A b (fun _ => 0) (fun y => -u y) x ≤ 0 := fun x hx => by
    rw [nondivOperator_neg A b _ (hu.contDiffAt (hU.mem_nhds hx))]
    linarith [hsup x hx]
  obtain ⟨y, hy, hmax⟩ := weak_maximum_principle hU hUb hUne hA he hb hu.neg huc.neg hneg
  exact ⟨y, hy, fun x hx => by linarith [hmax x hx]⟩

/-- **Weak maximum principle with nonnegative zeroth-order coefficient** (Evans §6.4.1
Theorem 2(i), Gilbarg and Trudinger Corollary 3.2, Guo Theorem XI.3.7(ii)). With `c ≥ 0`, a
subsolution is bounded on the closure by the maximum of its positive part over the boundary. -/
theorem weak_maximum_principle_of_nonneg (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUne : U.Nonempty) (hA : IsUniformlyElliptic A U θ) {e : E} (he : ‖e‖ = 1)
    (hb : ∀ x ∈ U, ⟪b x, e⟫ ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, nondivOperator A b c u x ≤ 0) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u x ≤ max (u y) 0 := by
  have : Nontrivial E := ⟨⟨e, 0, fun h => by simp [h] at he⟩⟩
  have hfr : IsCompact (frontier U) :=
    hUb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨y, hyfr, hymax⟩ := hfr.exists_isMaxOn (hUb.frontier_nonempty hUne)
    (huc.mono frontier_subset_closure)
  refine ⟨y, hyfr, fun x hx => ?_⟩
  by_contra hlt
  push Not at hlt
  set K := max (u y) 0 with hK
  set V := U ∩ {z | K < u z} with hV
  have hVo : IsOpen V := hu.continuousOn.isOpen_inter_preimage hU isOpen_Ioi
  have hVU : V ⊆ U := inter_subset_left
  have hxV : x ∈ closure V := by
    have hev : ∀ᶠ z in 𝓝[U] x, K < u z :=
      ((huc x hx).mono subset_closure).eventually (lt_mem_nhds hlt)
    rw [mem_closure_iff_nhdsWithin_neBot, hV, nhdsWithin_inter_of_mem' hev]
    exact mem_closure_iff_nhdsWithin_neBot.mp hx
  obtain ⟨y', hy'fr, hy'max⟩ := weak_maximum_principle hVo (hUb.subset hVU)
    (closure_nonempty_iff.mp ⟨x, hxV⟩) (hA.mono hVU)
    he (fun z hz => hb z (hVU hz)) (hu.mono hVU) (huc.mono (closure_mono hVU)) fun z hz => by
      have := nondivOperator_congr_zeroth A b c (fun _ => 0) u z
      have h3 : 0 ≤ c z * u z := mul_nonneg (hc z (hVU hz)) ((le_max_right _ _).trans hz.2.le)
      linarith [hsub z (hVU hz), nondivOperator_congr_zeroth A b (fun _ => 0) c u z]
  have hy'cl := (hVo.frontier_eq ▸ hy'fr : y' ∈ closure V \ V)
  have hy'K : u y' ≤ K := by
    by_cases hy'U : y' ∈ U
    · exact not_lt.mp fun h => hy'cl.2 ⟨hy'U, h⟩
    · refine (hymax ?_).trans (le_max_left _ _)
      rw [hU.frontier_eq]
      exact ⟨closure_mono hVU hy'cl.1, hy'U⟩
  linarith [hy'max x hxV]

/-- **Strict maximum principle** (Guo Theorem XI.3.5). A strict subsolution, meaning `L u < 0` at
a point, has no local maximum there whenever `c u ≥ 0` at the point. -/
theorem not_isLocalMax_of_neg {x₀ : E} (hsymm : (A x₀ : E →ₗ[ℝ] E).IsSymmetric)
    (hpsd : ∀ ξ, 0 ≤ ⟪A x₀ ξ, ξ⟫) {u : E → ℝ} (hu : ContDiffAt ℝ 2 u x₀)
    (hcu : 0 ≤ c x₀ * u x₀) (hstrict : nondivOperator A b c u x₀ < 0) : ¬ IsLocalMax u x₀ :=
  fun hmax => absurd (le_nondivOperator_of_isLocalMax (b := b) (c := c) hsymm hpsd hu hmax)
    (not_le.mpr (hstrict.trans_le hcu))

/-- **Comparison principle** (Gilbarg and Trudinger Theorem 3.3, Guo Corollary XI.3.11). With
`c ≥ 0`, if `L u ≤ L v` on the set and `u ≤ v` on the boundary, then `u ≤ v` on the closure. -/
theorem comparison_principle (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hA : IsUniformlyElliptic A U θ) {e : E} (he : ‖e‖ = 1) (hb : ∀ x ∈ U, ⟪b x, e⟫ ≤ B)
    (hc : ∀ x ∈ U, 0 ≤ c x) {u v : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOperator A b c u x ≤ nondivOperator A b c v x)
    (hbd : ∀ x ∈ frontier U, u x ≤ v x) : ∀ x ∈ closure U, u x ≤ v x := by
  obtain ⟨y, hy, hmax⟩ := weak_maximum_principle_of_nonneg hU hUb hUne hA he hb hc
    (hu.add (contDiffOn_const.mul hv)) (huc.add (continuousOn_const.mul hvc)) (u := fun z =>
      u z + (-1) * v z) fun x hx => by
    rw [nondivOperator_add_smul A b c (hu.contDiffAt (hU.mem_nhds hx))
      (hv.contDiffAt (hU.mem_nhds hx))]
    linarith [hL x hx]
  intro x hx
  have h1 := hmax x hx
  rw [max_eq_right (by linarith [hbd y hy])] at h1
  linarith

/-- **Bound by the boundary values** (Gilbarg and Trudinger Corollary 3.2, second clause). With
`c ≥ 0`, a solution of `L u = 0` on a bounded open set is bounded in absolute value on the
closure by the maximum of `|u|` over the boundary. -/
theorem abs_le_of_eq_zero (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUne : U.Nonempty) (hA : IsUniformlyElliptic A U θ) {e : E} (he : ‖e‖ = 1)
    (hb : ∀ x ∈ U, ⟪b x, e⟫ ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsol : ∀ x ∈ U, nondivOperator A b c u x = 0) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, |u x| ≤ |u y| := by
  have : Nontrivial E := ⟨⟨e, 0, fun h => by simp [h] at he⟩⟩
  have hfr : IsCompact (frontier U) :=
    hUb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨y, hyfr, hymax⟩ := hfr.exists_isMaxOn (hUb.frontier_nonempty hUne)
    (huc.mono frontier_subset_closure).abs
  refine ⟨y, hyfr, fun x hx => ?_⟩
  obtain ⟨y₁, hy₁, h₁⟩ := weak_maximum_principle_of_nonneg hU hUb hUne hA he hb hc hu huc
    fun z hz => (hsol z hz).le
  obtain ⟨y₂, hy₂, h₂⟩ := weak_maximum_principle_of_nonneg hU hUb hUne hA he hb hc hu.neg huc.neg
    fun z hz => by rw [nondivOperator_neg A b c (hu.contDiffAt (hU.mem_nhds hz)), hsol z hz,
      neg_zero]
  have hx₁ : u x ≤ |u y| := (h₁ x hx).trans (max_le ((le_abs_self _).trans (hymax hy₁))
    (abs_nonneg _))
  have hx₂ : -u x ≤ |u y| := (h₂ x hx).trans (max_le ((neg_le_abs _).trans (hymax hy₂))
    (abs_nonneg _))
  exact abs_le.mpr ⟨by linarith, hx₁⟩

/-- **Weak minimum principle with nonnegative zeroth-order coefficient** (Evans §6.4.1
Theorem 2(ii)). With `c ≥ 0`, a supersolution is bounded below on the closure by the minimum of
its negative part over the boundary. -/
theorem weak_minimum_principle_of_nonneg (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUne : U.Nonempty) (hA : IsUniformlyElliptic A U θ) {e : E} (he : ‖e‖ = 1)
    (hb : ∀ x ∈ U, ⟪b x, e⟫ ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsup : ∀ x ∈ U, 0 ≤ nondivOperator A b c u x) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, min (u y) 0 ≤ u x := by
  obtain ⟨y, hy, hmax⟩ := weak_maximum_principle_of_nonneg hU hUb hUne hA he hb hc hu.neg huc.neg
    fun x hx => by
      rw [nondivOperator_neg A b c (hu.contDiffAt (hU.mem_nhds hx))]
      linarith [hsup x hx]
  refine ⟨y, hy, fun x hx => ?_⟩
  have h := hmax x hx
  have e : min (u y) 0 = -max (-u y) 0 := by rw [← min_neg_neg, neg_neg, neg_zero]
  rw [e]
  linarith

/-- **Uniqueness for the Dirichlet problem** (Guo Corollary XI.3.9). With `c ≥ 0`, two functions
with the same image under `L` on the set and the same boundary values agree on the closure. -/
theorem dirichlet_unique (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hA : IsUniformlyElliptic A U θ) {e : E} (he : ‖e‖ = 1) (hb : ∀ x ∈ U, ⟪b x, e⟫ ≤ B)
    (hc : ∀ x ∈ U, 0 ≤ c x) {u v : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOperator A b c u x = nondivOperator A b c v x)
    (hbd : ∀ x ∈ frontier U, u x = v x) : ∀ x ∈ closure U, u x = v x := fun x hx =>
  le_antisymm
    (comparison_principle hU hUb hUne hA he hb hc hu hv huc hvc (fun x hx => (hL x hx).le)
      (fun x hx => (hbd x hx).le) x hx)
    (comparison_principle hU hUb hUne hA he hb hc hv hu hvc huc (fun x hx => (hL x hx).ge)
      (fun x hx => (hbd x hx).ge) x hx)

end nondivOperator

/-- **Trace inequality** for matrices (`Fin d`-indexed form). -/
theorem sum_mul_nonpos_of_posSemidef {d : ℕ} {A H : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.PosSemidef) (hH : (-H).PosSemidef) : ∑ i, ∑ j, A i j * H i j ≤ 0 :=
  hA.sum_mul_le_zero hH

/-! ### Euclidean space with a coefficient matrix -/

open EllipticPdes.Sobolev (partialD partialD_apply)

variable {d : ℕ}

/-- **Hessian at an interior local maximum** on Euclidean space. -/
theorem sndFDeriv_nonpos_of_isLocalMax {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin d)} (hu : ContDiffAt ℝ 2 u x₀) (hmax : IsLocalMax u x₀)
    (ξ : EuclideanSpace ℝ (Fin d)) : fderiv ℝ (fderiv ℝ u) x₀ ξ ξ ≤ 0 :=
  hmax.fderiv_fderiv_nonpos hu ξ

/-- **Non-divergence-form operator** `L u = -∑ aᵢⱼ ∂ᵢ∂ⱼ u + ∑ bᵢ ∂ᵢ u + c u` with a coefficient
matrix `a x` and transport `b x` on Euclidean space. -/
def nondivOp (a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) (c : EuclideanSpace ℝ (Fin d) → ℝ)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  -(∑ i, ∑ j, a x i j * partialD i (partialD j u) x) + ∑ i, b x i * partialD i u x + c x * u x

/-- The endomorphism of Euclidean space with the matrix `M`. -/
abbrev matrixCLM (M : Fin d → Fin d → ℝ) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (Matrix.of M)

/-- The coordinates of `matrixCLM M ξ`. -/
theorem matrixCLM_apply (M : Fin d → Fin d → ℝ) (ξ : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    matrixCLM M ξ i = ∑ j, M i j * ξ j := rfl

/-- The quadratic form of `matrixCLM M` is the quadratic form of `M`. -/
theorem inner_matrixCLM (M : Fin d → Fin d → ℝ) (ξ : EuclideanSpace ℝ (Fin d)) :
    ⟪matrixCLM M ξ, ξ⟫ = ∑ i, ∑ j, M i j * ξ i * ξ j := by
  simp only [PiLp.inner_apply, matrixCLM_apply, RCLike.inner_apply, conj_trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- A symmetric matrix gives a symmetric endomorphism. -/
theorem isSymmetric_matrixCLM {M : Fin d → Fin d → ℝ} (h : ∀ i j, M i j = M j i) :
    ((matrixCLM M : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
      EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)).IsSymmetric := fun ξ η => by
  simp only [ContinuousLinearMap.coe_coe, PiLp.inner_apply, matrixCLM_apply, RCLike.inner_apply,
    conj_trivial, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h i j]
  ring

/-- The trace of `matrixCLM M` is the trace of `M`. -/
theorem trace_matrixCLM (M : Fin d → Fin d → ℝ) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d)) (matrixCLM M : _ →ₗ[ℝ] _) = ∑ i, M i i := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [EuclideanSpace.inner_single_left, matrixCLM_apply, PiLp.single_apply]

/-- `matrixCLM M` maps the `i`-th basis vector to the `i`-th column. -/
theorem matrixCLM_single (M : Fin d → Fin d → ℝ) (i : Fin d) :
    matrixCLM M (EuclideanSpace.single i 1) = ∑ j, M j i • EuclideanSpace.single j 1 := by
  ext k
  simp [matrixCLM_apply, Finset.sum_apply, PiLp.single_apply, Pi.single_apply]

/-- `tr (matrixCLM M D²u(x)) = ∑ᵢⱼ Mᵢⱼ D²u(x)(eᵢ, eⱼ)`. -/
theorem traceHessian_matrixCLM (M : Fin d → Fin d → ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    traceHessian (matrixCLM M) u x
      = ∑ i, ∑ j, M i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) := by
  rw [traceHessian_eq_sum (EuclideanSpace.basisFun (Fin d) ℝ), Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [EuclideanSpace.basisFun_apply, matrixCLM_single, map_sum, map_smul, sum_apply,
    smul_apply, smul_eq_mul]

/-- The second partial derivatives are the entries of the Hessian. -/
theorem partialD_partialD_eq {u : EuclideanSpace ℝ (Fin d) → ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (i j : Fin d) :
    partialD i (partialD j u) x
      = fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have : partialD j u = fun y => fderiv ℝ u y (EuclideanSpace.single j 1) := rfl
  rw [partialD_apply, this, fderiv_clm_apply hu (differentiableAt_const _)]
  simp

/-- The first partials are the coordinates of the derivative. -/
theorem fderiv_toLp_eq_sum (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (v : Fin d → ℝ) : fderiv ℝ u x (WithLp.toLp 2 v) = ∑ i, v i * partialD i u x := by
  have : (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) = ∑ i, v i • EuclideanSpace.single i 1 := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [this, map_sum]
  simp [partialD_apply]

/-- **The Euclidean operator is the coordinate-free one** for a function `C²` at the point. -/
theorem nondivOp_eq {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ}
    {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ} {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hu : ContDiffAt ℝ 2 u x) :
    nondivOp a b c u x = nondivOperator (fun y => matrixCLM (a y))
      (fun y => WithLp.toLp 2 (b y)) c u x := by
  have hd2 : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by decide)).differentiableAt (by simp)
  simp only [nondivOp, nondivOperator, traceHessian_matrixCLM, fderiv_toLp_eq_sum,
    partialD_partialD_eq hd2]

/-- Pointwise form of `nondivOp_eq` on an open set where `u` is `C²`. -/
theorem nondivOp_eq_of_contDiffOn {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ}
    {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ} {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ U) :
    nondivOp a b c u x = nondivOperator (fun y => matrixCLM (a y))
      (fun y => WithLp.toLp 2 (b y)) c u x :=
  nondivOp_eq (hu.contDiffAt (hU.mem_nhds hx))

/-- The Euclidean ellipticity hypotheses make the matrix an elliptic endomorphism field. -/
theorem isUniformlyElliptic_matrixCLM {U : Set (EuclideanSpace ℝ (Fin d))}
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j) :
    IsUniformlyElliptic (fun x => matrixCLM (a x)) U θ :=
  ⟨hθ, fun x hx => isSymmetric_matrixCLM (hsymm x hx), fun x hx ξ => by
    rw [inner_matrixCLM, EuclideanSpace.norm_sq_eq]
    simpa using hell x hx (WithLp.ofLp ξ)⟩

/-- The coordinate bound `|bᵢ| ≤ B` gives `⟪b, e⟫ ≤ B` for the first basis vector `e`. -/
theorem exists_unit_inner_le (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ} {B : ℝ} (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) :
    ∃ e : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 ∧
      ∀ x ∈ U, ⟪(WithLp.toLp 2 (b x) : EuclideanSpace ℝ (Fin d)), e⟫ ≤ B :=
  ⟨EuclideanSpace.single ⟨0, hd⟩ 1, by simp, fun x hx => by
    rw [EuclideanSpace.inner_single_right]
    simpa using (abs_le.mp (hb x hx ⟨0, hd⟩)).2⟩

/-- The Euclidean hypotheses on the coefficients give the coordinate-free ones: the matrix is
uniformly elliptic as an endomorphism field, and `⟪b, e⟫ ≤ B` for the first basis vector. -/
theorem euclid_data (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ}
    {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ} {θ B : ℝ} (hθ : 0 < θ)
    (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) :
    IsUniformlyElliptic (fun x => matrixCLM (a x)) U θ ∧
      ∃ e : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 ∧
        ∀ x ∈ U, ⟪(WithLp.toLp 2 (b x) : EuclideanSpace ℝ (Fin d)), e⟫ ≤ B :=
  ⟨isUniformlyElliptic_matrixCLM hθ hsymm hell, exists_unit_inner_le hd hb⟩

/-- The trace of the matrix endomorphism is at most `d` times a bound on the entries. -/
theorem trace_matrixCLM_le {M : Fin d → Fin d → ℝ} {A : ℝ} (hM : ∀ i j, |M i j| ≤ A) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d)) (matrixCLM M : _ →ₗ[ℝ] _) ≤ d * A := by
  rw [trace_matrixCLM]
  calc ∑ i, M i i ≤ ∑ _i : Fin d, A := Finset.sum_le_sum fun i _ => (le_abs_self _).trans (hM i i)
    _ = d * A := by simp

/-- The Euclidean norm of a vector is at most `d` times a bound on its coordinates. -/
theorem norm_toLp_le {v : Fin d → ℝ} {B : ℝ} (hv : ∀ i, |v i| ≤ B) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ≤ d * B := by
  have : (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) = ∑ i, v i • EuclideanSpace.single i 1 := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [this]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖v i • (EuclideanSpace.single i (1 : ℝ))‖ ≤ ∑ _i : Fin d, B :=
        Finset.sum_le_sum fun i _ => by simpa [norm_smul] using hv i
    _ = d * B := by simp

/-- **Weak maximum principle** (Evans §6.4.1 Theorem 1(i), Gilbarg and Trudinger Theorem 3.1,
Guo Theorem XI.3.7(i)). Let `U` be a bounded open nonempty set, `L` a non-divergence-form
operator with symmetric uniformly elliptic coefficients, bounded transport coefficients and no
zeroth-order term, and `u` a function `C²` on `U` and continuous on its closure with `L u ≤ 0`
on `U`. Then the maximum of `u` over the closure is attained on the boundary. -/
theorem weak_maximum_principle (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, nondivOp a b (fun _ => 0) u x ≤ 0) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u x ≤ u y := by
  obtain ⟨hA, e, he, hb'⟩ := euclid_data hd hθ hsymm hell hb
  exact nondivOperator.weak_maximum_principle hU hUb hUne hA he hb' hu huc fun x hx => by
    rw [← nondivOp_eq_of_contDiffOn hU hu hx]
    exact hsub x hx

/-- **Weak minimum principle for supersolutions** (Evans §6.4.1 Theorem 1(ii)). A
supersolution attains its minimum over the closure on the boundary. -/
theorem weak_minimum_principle (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsup : ∀ x ∈ U, 0 ≤ nondivOp a b (fun _ => 0) u x) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u y ≤ u x := by
  obtain ⟨hA, e, he, hb'⟩ := euclid_data hd hθ hsymm hell hb
  exact nondivOperator.weak_minimum_principle hU hUb hUne hA he hb' hu huc fun x hx => by
    rw [← nondivOp_eq_of_contDiffOn hU hu hx]
    exact hsup x hx

/-- **Weak maximum principle with nonnegative zeroth-order coefficient** (Evans §6.4.1
Theorem 2(i), Gilbarg and Trudinger Corollary 3.2, Guo Theorem XI.3.7(ii)). With `c ≥ 0`, a
subsolution is bounded on the closure by the maximum of its positive part over the boundary. -/
theorem weak_maximum_principle_of_nonneg (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, nondivOp a b c u x ≤ 0) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u x ≤ max (u y) 0 := by
  obtain ⟨hA, e, he, hb'⟩ := euclid_data hd hθ hsymm hell hb
  exact nondivOperator.weak_maximum_principle_of_nonneg hU hUb hUne hA he hb' hc hu huc
    fun x hx => by
      rw [← nondivOp_eq_of_contDiffOn hU hu hx]
      exact hsub x hx

/-- **Weak minimum principle with nonnegative zeroth-order coefficient** (Evans §6.4.1
Theorem 2(ii)). With `c ≥ 0`, a supersolution is bounded below on the closure by the minimum
of its negative part over the boundary. -/
theorem weak_minimum_principle_of_nonneg (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsup : ∀ x ∈ U, 0 ≤ nondivOp a b c u x) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, min (u y) 0 ≤ u x := by
  obtain ⟨hA, e, he, hb'⟩ := euclid_data hd hθ hsymm hell hb
  exact nondivOperator.weak_minimum_principle_of_nonneg hU hUb hUne hA he hb' hc hu huc
    fun x hx => by
      rw [← nondivOp_eq_of_contDiffOn hU hu hx]
      exact hsup x hx

/-- **Strict maximum principle** (Guo Theorem XI.3.5). A strict subsolution, meaning
`L u < 0` at a point, has no local maximum at that point whenever `c u ≥ 0` there: in
particular when `c = 0`, when `c ≥ 0` and the maximum is nonnegative, and when the maximum is
zero. -/
theorem not_isLocalMax_of_nondivOp_neg {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ}
    {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ} {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin d)} (hsymm : ∀ i j, a x₀ i j = a x₀ j i)
    (hpsd : ∀ ξ : Fin d → ℝ, 0 ≤ ∑ i, ∑ j, a x₀ i j * ξ i * ξ j)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffAt ℝ 2 u x₀) (hcu : 0 ≤ c x₀ * u x₀)
    (hstrict : nondivOp a b c u x₀ < 0) : ¬ IsLocalMax u x₀ :=
  nondivOperator.not_isLocalMax_of_neg (A := fun y => matrixCLM (a y))
    (b := fun y => WithLp.toLp 2 (b y)) (c := c) (isSymmetric_matrixCLM hsymm)
    (fun ξ => by simpa [inner_matrixCLM] using hpsd (WithLp.ofLp ξ)) hu hcu
    (by rwa [nondivOp_eq hu] at hstrict)

/-- **Comparison principle** (Gilbarg and Trudinger Theorem 3.3, Guo Corollary XI.3.11). With
`c ≥ 0`, if `L u ≤ L v` on the set and `u ≤ v` on the boundary, then `u ≤ v` on the closure. -/
theorem comparison_principle (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x)
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOp a b c u x ≤ nondivOp a b c v x)
    (hbd : ∀ x ∈ frontier U, u x ≤ v x) : ∀ x ∈ closure U, u x ≤ v x := by
  obtain ⟨hA, e, he, hb'⟩ := euclid_data hd hθ hsymm hell hb
  exact nondivOperator.comparison_principle hU hUb hUne hA he hb' hc hu hv huc hvc
    (fun x hx => by
      rw [← nondivOp_eq_of_contDiffOn hU hu hx, ← nondivOp_eq_of_contDiffOn hU hv hx]
      exact hL x hx) hbd

/-- **Bound by the boundary values** (Gilbarg and Trudinger Corollary 3.2, second clause). With
`c ≥ 0`, a solution of `L u = 0` on a bounded open set is bounded in absolute value on the
closure by the maximum of `|u|` over the boundary. -/
theorem abs_le_of_nondivOp_eq_zero (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsol : ∀ x ∈ U, nondivOp a b c u x = 0) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, |u x| ≤ |u y| := by
  obtain ⟨hA, e, he, hb'⟩ := euclid_data hd hθ hsymm hell hb
  exact nondivOperator.abs_le_of_eq_zero hU hUb hUne hA he hb' hc hu huc fun x hx => by
    rw [← nondivOp_eq_of_contDiffOn hU hu hx]
    exact hsol x hx

/-- **Uniqueness for the Dirichlet problem** (Guo Corollary XI.3.9). With `c ≥ 0`, two
functions with the same image under `L` on the set and the same boundary values agree on the
closure. -/
theorem dirichlet_unique (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x)
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOp a b c u x = nondivOp a b c v x)
    (hbd : ∀ x ∈ frontier U, u x = v x) : ∀ x ∈ closure U, u x = v x := by
  obtain ⟨hA, e, he, hb'⟩ := euclid_data hd hθ hsymm hell hb
  exact nondivOperator.dirichlet_unique hU hUb hUne hA he hb' hc hu hv huc hvc
    (fun x hx => by
      rw [← nondivOp_eq_of_contDiffOn hU hu hx, ← nondivOp_eq_of_contDiffOn hU hv hx]
      exact hL x hx) hbd

end EllipticPdes.Classical
