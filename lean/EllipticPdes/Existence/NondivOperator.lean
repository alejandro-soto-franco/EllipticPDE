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

/-!
# Non-divergence-form operators on a finite-dimensional inner product space

The second-order test at a local maximum and the operator `L u = -tr (A D²u) + D u (b) + c u` on
a finite-dimensional real inner product space `E`, with `A x : E →L[ℝ] E` a field of
endomorphisms, `b x : E` a vector field and `c` a function. The principal part is the contraction
`traceHessian` of the Hessian of `u` against `A`, defined through the canonical tensor of `E`
and therefore independent of any basis. No coordinates occur: the Euclidean matrix form is
recovered in `EllipticPdes.Existence.ClassicalMaximum`.

## Main declarations

* `IsLocalMax.fderiv_fderiv_nonpos`: the Hessian is negative semidefinite at a local maximum.
* `EllipticPdes.Classical.traceHessian`: `tr (A D²u(x))`; `traceHessian_nonpos` is the trace
  inequality for `A` positive semidefinite and `D²u(x)` negative semidefinite.
* `EllipticPdes.Classical.nondivOperator`: the operator, with its linearity lemmas.
* `EllipticPdes.Classical.IsUniformlyElliptic`: the symmetric uniformly elliptic coefficient.
* `EllipticPdes.Classical.expInner`: the perturbation `exp (λ ⟪e, x⟫)` and its image under `L`.
-/

@[expose] public section

open Set Filter Topology InnerProductSpace TensorProduct
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

theorem expInner_pos (lam : ℝ) (e x : E) : 0 < expInner lam e x := Real.exp_pos _

theorem contDiff_expInner (lam : ℝ) (e : E) {n : WithTop ℕ∞} : ContDiff ℝ n (expInner lam e) :=
  Real.contDiff_exp.comp (contDiff_const.mul (contDiff_const.inner ℝ contDiff_id))

theorem hasFDerivAt_expInner (lam : ℝ) (e x : E) :
    HasFDerivAt (expInner lam e) (expInner lam e x • (lam • innerSL ℝ e)) x := by
  have h1 : HasFDerivAt (fun y : E => lam * ⟪e, y⟫) (lam • innerSL ℝ e) x :=
    (innerSL ℝ e).hasFDerivAt.const_mul lam
  exact (Real.hasDerivAt_exp (lam * ⟪e, x⟫)).comp_hasFDerivAt x h1

theorem fderiv_expInner_apply (lam : ℝ) (e x ξ : E) :
    fderiv ℝ (expInner lam e) x ξ = lam * expInner lam e x * ⟪e, ξ⟫ := by
  simp [(hasFDerivAt_expInner lam e x).fderiv]
  ring

theorem fderiv_fderiv_expInner_apply (lam : ℝ) (e x ξ η : E) :
    fderiv ℝ (fderiv ℝ (expInner lam e)) x ξ η = lam ^ 2 * expInner lam e x * ⟪e, ξ⟫ * ⟪e, η⟫ := by
  have hf : fderiv ℝ (expInner lam e) = fun y => expInner lam e y • (lam • innerSL ℝ e) :=
    funext fun y => (hasFDerivAt_expInner lam e y).fderiv
  rw [hf, ((hasFDerivAt_expInner lam e x).smul_const (lam • innerSL ℝ e)).fderiv]
  simp
  ring

variable [FiniteDimensional ℝ E]

theorem nondivOperator_expInner (A : E → E →L[ℝ] E) (b : E → E) (c : E → ℝ) (lam : ℝ) (e x : E) :
    nondivOperator A b c (expInner lam e) x
      = (-(lam ^ 2 * ⟪e, A x e⟫) + lam * ⟪e, b x⟫ + c x) * expInner lam e x := by
  rw [nondivOperator, traceHessian_eq_of_fderiv_fderiv (α := lam ^ 2 * expInner lam e x) (β := 0)
    (p := e) (q := e) fun ξ η => by simp [fderiv_fderiv_expInner_apply]]
  simp [fderiv_expInner_apply]
  ring

end ExpInner


end EllipticPdes.Classical
