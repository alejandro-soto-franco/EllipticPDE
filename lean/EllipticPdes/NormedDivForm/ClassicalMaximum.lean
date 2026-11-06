/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.NormedDivForm.Basic
public import EllipticPdes.Existence.ClassicalMaximum
public import EllipticPdes.Existence.StrongMaximum

/-!
# Classical maximum principles on a normed space

A non-divergence-form operator `L u = -tr (D²u(x) ∘ A x) + Du(x)(b x) + c u` on a
finite-dimensional real normed space `E`, with coefficient `A x : StrongDual ℝ E →L[ℝ] E`. The
trace is that of `D²u(x) ∘ A x` as an endomorphism of `StrongDual ℝ E`, and needs no inner
product. Ellipticity reads `θ ‖ξ‖² ≤ ξ (A x ξ)`, and a transport bound is a bound on `ℓ (b x)`
for a nonzero covector `ℓ`.

Each theorem is proved by transfer along `toEuclidean : E ≃L[ℝ] F` to the inner-product twin of
`Existence/ClassicalMaximum.lean`. The coefficient goes to `transferMat`, the function `u` to
`u ∘ L.symm`, and `traceHessian_transfer` identifies the two traces.

## Main declarations

* `EllipticPdes.NormedClassical.traceHessian`, `nondivOperator`, `IsUniformlyElliptic`
* `EllipticPdes.NormedClassical.nondivOperator_transfer`: the operator after transfer.
* `EllipticPdes.NormedClassical.isUniformlyElliptic_canonicalCoeff`: the ellipticity hypothesis
  is satisfiable on every finite-dimensional real normed space.
* `EllipticPdes.NormedClassical.nondivOperator.weak_maximum_principle` and its corollaries:
  `weak_minimum_principle`, `weak_maximum_principle_of_nonneg`,
  `weak_minimum_principle_of_nonneg`, `comparison_principle`, `abs_le_of_eq_zero`,
  `dirichlet_unique`, `not_isLocalMax_of_neg`.
* `EllipticPdes.NormedClassical.nondivOperator.strong_maximum_principle` and
  `strong_maximum_principle_of_nonneg`, with an operator-norm bound on the coefficient in place
  of the trace bound of the inner-product twin.

Hopf's lemma stays on inner product spaces: its barrier `exp (-λ ‖x - y‖²)` needs a smooth norm,
and its interior ball would transfer to an ellipsoid.
-/

@[expose] public section

open Module Set
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes

namespace NormedClassical

open NormedDivForm

section Definitions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The contraction `tr (D²u(x) ∘ A)` of the Hessian of `u` at `x` against `A : E* → E`, the
trace of `D²u(x) ∘ A` as an endomorphism of `StrongDual ℝ E`. -/
def traceHessian (A : StrongDual ℝ E →L[ℝ] E) (u : E → ℝ) (x : E) : ℝ :=
  LinearMap.trace ℝ (StrongDual ℝ E) ((fderiv ℝ (fderiv ℝ u) x).comp A).toLinearMap

/-- **Non-divergence-form operator** `L u = -tr (D²u ∘ A) + D u (b) + c u` on a normed space. -/
def nondivOperator (A : E → StrongDual ℝ E →L[ℝ] E) (b : E → E) (c : E → ℝ) (u : E → ℝ)
    (x : E) : ℝ :=
  -traceHessian (A x) u x + fderiv ℝ u x (b x) + c x * u x

/-- `A` is a symmetric, uniformly elliptic coefficient on `U` with constant `θ`:
`θ ‖ξ‖² ≤ ξ (A x ξ)` for all `x ∈ U` and covectors `ξ`. -/
structure IsUniformlyElliptic (A : E → StrongDual ℝ E →L[ℝ] E) (U : Set E) (θ : ℝ) : Prop where
  /-- The ellipticity constant is positive. -/
  pos : 0 < θ
  /-- The coefficient is symmetric. -/
  symm : ∀ x ∈ U, ∀ ξ η : StrongDual ℝ E, η (A x ξ) = ξ (A x η)
  /-- The quadratic form is bounded below by `θ ‖ξ‖²`. -/
  coercive : ∀ x ∈ U, ∀ ξ : StrongDual ℝ E, θ * ‖ξ‖ ^ 2 ≤ ξ (A x ξ)

end Definitions

section SecondDerivative

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The derivative of `u ∘ L.symm`. -/
lemma fderiv_comp_symm (L : E ≃L[ℝ] F) (u : E → ℝ) (y : F) :
    fderiv ℝ (u ∘ L.symm) y = (fderiv ℝ u (L.symm y)).comp (L.symm : F →L[ℝ] E) :=
  L.symm.comp_right_fderiv

/-- The derivative of `u ∘ L.symm` as a function of the point. -/
lemma fderiv_comp_symm_eq (L : E ≃L[ℝ] F) (u : E → ℝ) :
    fderiv ℝ (u ∘ L.symm) =
      ⇑(L.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) ∘ fderiv ℝ u ∘ L.symm :=
  funext fun y => (fderiv_comp_symm L u y).trans (by ext; simp)

/-- **Second derivative of `u ∘ L.symm`.** No differentiability is needed, since `L` is an
equivalence. -/
lemma fderiv_fderiv_comp_symm (L : E ≃L[ℝ] F) (u : E → ℝ) (y v w : F) :
    fderiv ℝ (fderiv ℝ (u ∘ L.symm)) y v w =
      fderiv ℝ (fderiv ℝ u) (L.symm y) (L.symm v) (L.symm w) := by
  rw [fderiv_comp_symm_eq,
    (L.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)).comp_fderiv, L.symm.comp_right_fderiv]
  simp

end SecondDerivative

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

local notation "𝔽" => EuclideanSpace ℝ (Fin (finrank ℝ E))
local notation "𝓛" => (toEuclidean (E := E))
local notation "𝓛'" => ContinuousLinearEquiv.symm (toEuclidean (E := E))

/-- The vector of `F` that a covector on `E` transfers to: the Riesz vector of `ξ ∘ L.symm`. -/
def covectorToEuclidean : StrongDual ℝ E →L[ℝ] 𝔽 :=
  RieszBridge.rieszC.comp (W1pGraph.dualMap 𝓛)

lemma covectorToEuclidean_apply (ξ : StrongDual ℝ E) :
    covectorToEuclidean ξ = (InnerProductSpace.toDual ℝ 𝔽).symm (ξ.comp (𝓛' : 𝔽 →L[ℝ] E)) := rfl

/-- The pairing of a vector of `F` with a transferred covector. -/
lemma inner_covectorToEuclidean (w : 𝔽) (ξ : StrongDual ℝ E) :
    ⟪w, covectorToEuclidean ξ⟫ = ξ (𝓛' w) := by
  rw [covectorToEuclidean_apply, real_inner_comm, InnerProductSpace.toDual_symm_apply]
  rfl

lemma covectorToEuclidean_toEuclideanCovector (w : 𝔽) :
    covectorToEuclidean (toEuclideanCovector w) = w :=
  ext_inner_left ℝ fun v => by
    rw [inner_covectorToEuclidean, toEuclideanCovector_apply, real_inner_comm,
      ContinuousLinearEquiv.apply_symm_apply]

/-- Covectors on `E` and vectors of `F` correspond under `toEuclidean` and the Riesz map. -/
def covectorEquiv : StrongDual ℝ E ≃L[ℝ] 𝔽 :=
  ContinuousLinearEquiv.equivOfInverse covectorToEuclidean toEuclideanCovector
    toEuclideanCovector_toDual_symm covectorToEuclidean_toEuclideanCovector

/-- **Trace identity.** The normed trace equals the trace of the transferred coefficient against
the Hessian of `u ∘ L.symm`. -/
theorem traceHessian_transfer (A : StrongDual ℝ E →L[ℝ] E) (u : E → ℝ) (x : E) :
    Classical.traceHessian (transferMat A) (u ∘ 𝓛') (𝓛 x) = traceHessian A u x := by
  rw [traceHessian, ← LinearMap.trace_conj' _ (covectorEquiv (E := E)).toLinearEquiv,
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ 𝔽),
    Classical.traceHessian_eq_sum (stdOrthonormalBasis ℝ 𝔽)]
  refine Finset.sum_congr rfl fun i _ => ?_
  change _ = ⟪stdOrthonormalBasis ℝ 𝔽 i, covectorToEuclidean
    (fderiv ℝ (fderiv ℝ u) x (A (toEuclideanCovector (stdOrthonormalBasis ℝ 𝔽 i))))⟫
  rw [fderiv_fderiv_comp_symm, inner_covectorToEuclidean, transferMat_apply]
  simp

/-- The transferred coefficient field. -/
def transferCoeff (A : E → StrongDual ℝ E →L[ℝ] E) (y : 𝔽) : 𝔽 →L[ℝ] 𝔽 := transferMat (A (𝓛' y))

/-- The transferred drift. -/
def transferDrift (b : E → E) (y : 𝔽) : 𝔽 := 𝓛 (b (𝓛' y))

lemma transferCoeff_apply_toEuclidean (A : E → StrongDual ℝ E →L[ℝ] E) (x : E) :
    transferCoeff A (𝓛 x) = transferMat (A x) := by
  simp [transferCoeff]

lemma Internal.mul_comp_symm_apply (c u : E → ℝ) (x : E) :
    (c ∘ 𝓛') (𝓛 x) * (u ∘ 𝓛') (𝓛 x) = c x * u x := by
  simp

/-- **Operator identity.** The inner-product operator of the transferred data at `L x` is the
normed operator at `x`. -/
theorem nondivOperator_transfer (A : E → StrongDual ℝ E →L[ℝ] E) (b : E → E) (c : E → ℝ)
    (u : E → ℝ) (x : E) :
    Classical.nondivOperator (transferCoeff A) (transferDrift b) (c ∘ 𝓛') (u ∘ 𝓛') (𝓛 x) =
      nondivOperator A b c u x := by
  simp [Classical.nondivOperator, nondivOperator, transferCoeff, transferDrift,
    ← traceHessian_transfer, fderiv_comp_symm]

/-- The operator identity read at a point of the image. -/
lemma nondivOperator_transfer_symm (A : E → StrongDual ℝ E →L[ℝ] E) (b : E → E) (c : E → ℝ)
    (u : E → ℝ) (y : 𝔽) :
    Classical.nondivOperator (transferCoeff A) (transferDrift b) (c ∘ 𝓛') (u ∘ 𝓛') y =
      nondivOperator A b c u (𝓛' y) := by
  rw [← nondivOperator_transfer, ContinuousLinearEquiv.apply_symm_apply]

/-- **Ellipticity transfers** with constant `θ / max ‖L⁻¹‖ 1 ^ 2`. -/
theorem IsUniformlyElliptic.transfer {A : E → StrongDual ℝ E →L[ℝ] E} {U : Set E} {θ : ℝ}
    (hA : IsUniformlyElliptic A U θ) :
    Classical.IsUniformlyElliptic (transferCoeff A) (𝓛 '' U)
      (θ / (max ‖(𝓛' : 𝔽 →L[ℝ] E)‖ 1) ^ 2) where
  pos := div_pos hA.pos (pow_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) 2)
  symm := by
    rintro _ ⟨x, hx, rfl⟩ v w
    simpa [transferCoeff] using Internal.inner_transferMat_comm _ (hA.symm x hx) v w
  coercive := by
    rintro _ ⟨x, hx, rfl⟩ w
    simpa [transferCoeff] using Internal.coercive_transferMat _ hA.pos (hA.coercive x hx) w

omit [FiniteDimensional ℝ E] in
/-- A diagonal entry of a matrix on `F` in a unit vector is at most any bound on its norm. -/
lemma Internal.inner_apply_self_le {T : 𝔽 →L[ℝ] 𝔽} {K : ℝ} (hT : ‖T‖ ≤ K) {v : 𝔽}
    (hv : ‖v‖ = 1) : ⟪v, T v⟫ ≤ K :=
  (real_inner_le_norm _ _).trans (by
    rw [hv, one_mul]
    exact (T.le_opNorm v).trans (by rw [hv, mul_one]; exact hT))

omit [FiniteDimensional ℝ E] in
/-- The trace of a matrix on `F` is at most `dim F` times any bound on its norm. -/
lemma Internal.trace_le_of_norm_le {T : 𝔽 →L[ℝ] 𝔽} {K : ℝ} (hT : ‖T‖ ≤ K) :
    LinearMap.trace ℝ 𝔽 (T : 𝔽 →ₗ[ℝ] 𝔽) ≤ finrank ℝ 𝔽 * K :=
  calc LinearMap.trace ℝ 𝔽 (T : 𝔽 →ₗ[ℝ] 𝔽)
      = ∑ i, ⟪stdOrthonormalBasis ℝ 𝔽 i, T (stdOrthonormalBasis ℝ 𝔽 i)⟫ :=
        LinearMap.trace_eq_sum_inner _ _
    _ ≤ ∑ _i : Fin (finrank ℝ 𝔽), K :=
        Finset.sum_le_sum fun i _ =>
          Internal.inner_apply_self_le hT ((stdOrthonormalBasis ℝ 𝔽).norm_eq_one i)
    _ = finrank ℝ 𝔽 * K := by simp

/-- **Trace bound from a norm bound.** A bound on `‖A x‖` bounds the trace of the transferred
coefficient. -/
theorem trace_transferCoeff_le {A : E → StrongDual ℝ E →L[ℝ] E} {U : Set E} {Λ : ℝ}
    (hΛ : ∀ x ∈ U, ‖A x‖ ≤ Λ) :
    ∀ y ∈ 𝓛 '' U, LinearMap.trace ℝ 𝔽 (transferCoeff A y : 𝔽 →ₗ[ℝ] 𝔽) ≤
      finrank ℝ 𝔽 * (‖(𝓛 : E →L[ℝ] 𝔽)‖ * Λ * ‖(𝓛 : E →L[ℝ] 𝔽)‖) := by
  rintro _ ⟨x, hx, rfl⟩
  exact Internal.trace_le_of_norm_le ((norm_transferMat_le _).trans (by
    simp only [ContinuousLinearEquiv.symm_apply_apply]; gcongr; exact hΛ x hx))

/-- **Drift bound transfer**, with the factor `‖L‖`. -/
theorem norm_transferDrift_le {b : E → E} {U : Set E} {B : ℝ} (hb : ∀ x ∈ U, ‖b x‖ ≤ B) :
    ∀ y ∈ 𝓛 '' U, ‖transferDrift b y‖ ≤ ‖(𝓛 : E →L[ℝ] 𝔽)‖ * B := by
  rintro _ ⟨x, hx, rfl⟩
  simpa [transferDrift] using ((𝓛 : E →L[ℝ] 𝔽).le_opNorm (b x)).trans
    (mul_le_mul_of_nonneg_left (hb x hx) (norm_nonneg _))

/-- A uniformly elliptic coefficient on any finite-dimensional real normed space: the covector
`ξ` goes to `L⁻¹` of its transferred vector. -/
def canonicalCoeff : StrongDual ℝ E →L[ℝ] E := (𝓛' : 𝔽 →L[ℝ] E).comp covectorToEuclidean

lemma apply_canonicalCoeff (ξ η : StrongDual ℝ E) :
    η (canonicalCoeff ξ) = ⟪covectorToEuclidean ξ, covectorToEuclidean η⟫ :=
  (inner_covectorToEuclidean _ η).symm

lemma Internal.norm_le_norm_covectorToEuclidean (ξ : StrongDual ℝ E) :
    ‖ξ‖ ≤ max ‖(toEuclideanCovector : 𝔽 →L[ℝ] StrongDual ℝ E)‖ 1 * ‖covectorToEuclidean ξ‖ :=
  calc ‖ξ‖ = ‖toEuclideanCovector (covectorToEuclidean ξ)‖ :=
        congrArg norm (toEuclideanCovector_toDual_symm ξ).symm
    _ ≤ ‖(toEuclideanCovector : 𝔽 →L[ℝ] StrongDual ℝ E)‖ * ‖covectorToEuclidean ξ‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := by gcongr; exact le_max_left _ _

/-- **Uniform ellipticity of the canonical coefficient.** The ellipticity hypothesis of this
file is satisfiable on every finite-dimensional real normed space. -/
theorem isUniformlyElliptic_canonicalCoeff (U : Set E) :
    IsUniformlyElliptic (fun _ => canonicalCoeff) U
      (1 / (max ‖(toEuclideanCovector : 𝔽 →L[ℝ] StrongDual ℝ E)‖ 1) ^ 2) where
  pos := by positivity
  symm _ _ ξ η := by rw [apply_canonicalCoeff, apply_canonicalCoeff, real_inner_comm]
  coercive _ _ ξ := by
    rw [apply_canonicalCoeff, real_inner_self_eq_norm_sq, div_mul_eq_mul_div, one_mul,
      div_le_iff₀ (by positivity), ← mul_pow, mul_comm]
    exact pow_le_pow_left₀ (norm_nonneg _) (Internal.norm_le_norm_covectorToEuclidean ξ) 2

/-- The unit vector of `F` along a transferred nonzero covector. -/
def transferDir (ℓ : StrongDual ℝ E) : 𝔽 := ‖covectorToEuclidean ℓ‖⁻¹ • covectorToEuclidean ℓ

lemma covectorToEuclidean_ne_zero {ℓ : StrongDual ℝ E} (hℓ : ℓ ≠ 0) :
    covectorToEuclidean ℓ ≠ 0 :=
  fun h => hℓ ((covectorEquiv (E := E)).map_eq_zero_iff.1 h)

lemma norm_transferDir {ℓ : StrongDual ℝ E} (hℓ : ℓ ≠ 0) : ‖transferDir ℓ‖ = 1 :=
  norm_smul_inv_norm (covectorToEuclidean_ne_zero hℓ)

/-- **Transport bound transfer.** `ℓ (b x) ≤ B` on `U` becomes `⟪b', e⟫ ≤ B / ‖ℓ'‖` on the
image, along the unit vector `e = transferDir ℓ`. -/
theorem inner_transferDrift_le {b : E → E} {U : Set E} {B : ℝ} {ℓ : StrongDual ℝ E}
    (hb : ∀ x ∈ U, ℓ (b x) ≤ B) :
    ∀ y ∈ 𝓛 '' U, ⟪transferDrift b y, transferDir ℓ⟫ ≤ ‖covectorToEuclidean ℓ‖⁻¹ * B := by
  rintro _ ⟨x, hx, rfl⟩
  rw [transferDir, inner_smul_right, transferDrift, inner_covectorToEuclidean]
  simpa using mul_le_mul_of_nonneg_left (hb x hx) (inv_nonneg.2 (norm_nonneg _))

end Transfer

section Pullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {U : Set E}

local notation "𝔽" => EuclideanSpace ℝ (Fin (finrank ℝ E))
local notation "𝓛" => (toEuclidean (E := E))
local notation "𝓛'" => ContinuousLinearEquiv.symm (toEuclidean (E := E))

lemma Internal.isOpen_image (hU : IsOpen U) : IsOpen (𝓛 '' U) :=
  (toEuclidean (E := E)).toHomeomorph.isOpenMap _ hU

lemma Internal.isBounded_image (hUb : Bornology.IsBounded U) : Bornology.IsBounded (𝓛 '' U) :=
  (toEuclidean (E := E) : E →L[ℝ] 𝔽).lipschitzWith.isBounded_image hUb

lemma Internal.image_closure : 𝓛 '' closure U = closure (𝓛 '' U) :=
  (toEuclidean (E := E)).toHomeomorph.image_closure U

lemma Internal.image_frontier : 𝓛 '' frontier U = frontier (𝓛 '' U) :=
  (toEuclidean (E := E)).toHomeomorph.image_frontier U

/-- A statement on `U` read on the image. -/
lemma Internal.forall_image {V : Set E} {P : E → Prop} (h : ∀ x ∈ V, P x) :
    ∀ y ∈ 𝓛 '' V, P (𝓛' y) := by
  rintro _ ⟨x, hx, rfl⟩
  simpa using h x hx

/-- A statement on the closure of the image read on the closure of `U`. -/
lemma Internal.forall_closure_pullback {P : E → Prop} (h : ∀ y ∈ closure (𝓛 '' U), P (𝓛' y)) :
    ∀ x ∈ closure U, P x := fun x hx => by
  simpa using h (𝓛 x) (Internal.image_closure (U := U) ▸ mem_image_of_mem _ hx)

/-- A statement on the frontier of `U` read on the frontier of the image. -/
lemma Internal.forall_frontier_image {P : E → Prop} (h : ∀ x ∈ frontier U, P x) :
    ∀ y ∈ frontier (𝓛 '' U), P (𝓛' y) :=
  Internal.image_frontier (U := U) ▸ Internal.forall_image h

/-- A boundary extremum on the image pulls back to a boundary extremum on `U`. -/
lemma Internal.exists_frontier_pullback {R : ℝ → ℝ → Prop} {u : E → ℝ}
    (h : ∃ y ∈ frontier (𝓛 '' U), ∀ x ∈ closure (𝓛 '' U), R (u (𝓛' x)) (u (𝓛' y))) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, R (u x) (u y) := by
  obtain ⟨_, hy, h⟩ := h
  rw [← Internal.image_frontier] at hy
  obtain ⟨y, hy, rfl⟩ := hy
  exact ⟨y, hy, Internal.forall_closure_pullback fun x hx => by simpa using h x hx⟩

lemma Internal.contDiffOn_comp_symm {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) :
    ContDiffOn ℝ 2 (u ∘ 𝓛') (𝓛 '' U) :=
  hu.comp (𝓛').contDiff.contDiffOn fun y hy => Internal.forall_image (fun _ h => h) y hy

lemma Internal.continuousOn_closure_comp_symm {u : E → ℝ} (huc : ContinuousOn u (closure U)) :
    ContinuousOn (u ∘ 𝓛') (closure (𝓛 '' U)) :=
  Internal.image_closure (U := U) ▸ huc.comp (𝓛').continuous.continuousOn
    fun y hy => Internal.forall_image (fun _ h => h) y hy

lemma Internal.contDiffAt_comp_symm {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) :
    ContDiffAt ℝ 2 (u ∘ 𝓛') (𝓛 x) :=
  (by simpa using hu : ContDiffAt ℝ 2 u (𝓛' (𝓛 x))).comp _ (𝓛').contDiff.contDiffAt

lemma Internal.isLocalMax_comp_symm {u : E → ℝ} {x : E} (h : IsLocalMax u x) :
    IsLocalMax (u ∘ 𝓛') (𝓛 x) :=
  (by simpa using h : IsLocalMax u (𝓛' (𝓛 x))).comp_continuous (𝓛').continuous.continuousAt

end Pullback

namespace nondivOperator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {A : E → StrongDual ℝ E →L[ℝ] E} {b : E → E} {c : E → ℝ} {U : Set E} {θ B : ℝ}

local notation "𝔽" => EuclideanSpace ℝ (Fin (finrank ℝ E))
local notation "𝓛" => (toEuclidean (E := E))
local notation "𝓛'" => ContinuousLinearEquiv.symm (toEuclidean (E := E))

/-- **Weak maximum principle** (Evans §6.4.1 Theorem 1(i), Gilbarg and Trudinger Theorem 3.1), on
a finite-dimensional real normed space. Let `U` be a bounded open nonempty set, `L` a
non-divergence-form operator with symmetric uniformly elliptic coefficient, no zeroth-order term
and transport `b` with `ℓ (b x) ≤ B` for a nonzero covector `ℓ`, and `u` a function `C²` on `U`
and continuous on its closure with `L u ≤ 0` on `U`. Then the maximum of `u` over the closure is
attained on the boundary. -/
theorem weak_maximum_principle (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hA : IsUniformlyElliptic A U θ) {ℓ : StrongDual ℝ E} (hℓ : ℓ ≠ 0)
    (hb : ∀ x ∈ U, ℓ (b x) ≤ B) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U))
    (hsub : ∀ x ∈ U, nondivOperator A b (fun _ => 0) u x ≤ 0) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u x ≤ u y :=
  Internal.exists_frontier_pullback (R := (· ≤ ·))
    (Classical.nondivOperator.weak_maximum_principle (Internal.isOpen_image hU)
      (Internal.isBounded_image hUb) (hUne.image _) hA.transfer (norm_transferDir hℓ)
      (inner_transferDrift_le hb) (Internal.contDiffOn_comp_symm hu)
      (Internal.continuousOn_closure_comp_symm huc)
      fun y hy => (nondivOperator_transfer_symm A b (fun _ => 0) u y).trans_le
        (Internal.forall_image hsub y hy))

/-- **Weak minimum principle for supersolutions** (Evans §6.4.1 Theorem 1(ii)), on a
finite-dimensional real normed space: a supersolution attains its minimum over the closure on the
boundary. -/
theorem weak_minimum_principle (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hA : IsUniformlyElliptic A U θ) {ℓ : StrongDual ℝ E} (hℓ : ℓ ≠ 0)
    (hb : ∀ x ∈ U, ℓ (b x) ≤ B) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U))
    (hsup : ∀ x ∈ U, 0 ≤ nondivOperator A b (fun _ => 0) u x) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u y ≤ u x :=
  Internal.exists_frontier_pullback (R := fun a b => b ≤ a)
    (Classical.nondivOperator.weak_minimum_principle (Internal.isOpen_image hU)
      (Internal.isBounded_image hUb) (hUne.image _) hA.transfer (norm_transferDir hℓ)
      (inner_transferDrift_le hb) (Internal.contDiffOn_comp_symm hu)
      (Internal.continuousOn_closure_comp_symm huc)
      fun y hy => (Internal.forall_image hsup y hy).trans_eq
        (nondivOperator_transfer_symm A b (fun _ => 0) u y).symm)

/-- **Weak maximum principle with nonnegative zeroth-order coefficient** (Evans §6.4.1
Theorem 2(i), Gilbarg and Trudinger Corollary 3.2), on a finite-dimensional real normed space.
With `c ≥ 0`, a subsolution is bounded on the closure by the maximum of its positive part over the
boundary. -/
theorem weak_maximum_principle_of_nonneg (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUne : U.Nonempty) (hA : IsUniformlyElliptic A U θ) {ℓ : StrongDual ℝ E} (hℓ : ℓ ≠ 0)
    (hb : ∀ x ∈ U, ℓ (b x) ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, nondivOperator A b c u x ≤ 0) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u x ≤ max (u y) 0 :=
  Internal.exists_frontier_pullback (R := fun a b => a ≤ max b 0)
    (Classical.nondivOperator.weak_maximum_principle_of_nonneg (Internal.isOpen_image hU)
      (Internal.isBounded_image hUb) (hUne.image _) hA.transfer (norm_transferDir hℓ)
      (inner_transferDrift_le hb) (Internal.forall_image hc) (Internal.contDiffOn_comp_symm hu)
      (Internal.continuousOn_closure_comp_symm huc)
      fun y hy => (nondivOperator_transfer_symm A b c u y).trans_le
        (Internal.forall_image hsub y hy))

/-- **Weak minimum principle with nonnegative zeroth-order coefficient** (Evans §6.4.1
Theorem 2(ii)), on a finite-dimensional real normed space. With `c ≥ 0`, a supersolution is
bounded below on the closure by the minimum of its negative part over the boundary. -/
theorem weak_minimum_principle_of_nonneg (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUne : U.Nonempty) (hA : IsUniformlyElliptic A U θ) {ℓ : StrongDual ℝ E} (hℓ : ℓ ≠ 0)
    (hb : ∀ x ∈ U, ℓ (b x) ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsup : ∀ x ∈ U, 0 ≤ nondivOperator A b c u x) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, min (u y) 0 ≤ u x :=
  Internal.exists_frontier_pullback (R := fun a b => min b 0 ≤ a)
    (Classical.nondivOperator.weak_minimum_principle_of_nonneg (Internal.isOpen_image hU)
      (Internal.isBounded_image hUb) (hUne.image _) hA.transfer (norm_transferDir hℓ)
      (inner_transferDrift_le hb) (Internal.forall_image hc) (Internal.contDiffOn_comp_symm hu)
      (Internal.continuousOn_closure_comp_symm huc)
      fun y hy => (Internal.forall_image hsup y hy).trans_eq
        (nondivOperator_transfer_symm A b c u y).symm)

/-- **Bound by the boundary values** (Gilbarg and Trudinger Corollary 3.2, second clause), on a
finite-dimensional real normed space. With `c ≥ 0`, a solution of `L u = 0` on a bounded open set
is bounded in absolute value on the closure by the maximum of `|u|` over the boundary. -/
theorem abs_le_of_eq_zero (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUne : U.Nonempty) (hA : IsUniformlyElliptic A U θ) {ℓ : StrongDual ℝ E} (hℓ : ℓ ≠ 0)
    (hb : ∀ x ∈ U, ℓ (b x) ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsol : ∀ x ∈ U, nondivOperator A b c u x = 0) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, |u x| ≤ |u y| :=
  Internal.exists_frontier_pullback (R := fun a b => |a| ≤ |b|)
    (Classical.nondivOperator.abs_le_of_eq_zero (Internal.isOpen_image hU)
      (Internal.isBounded_image hUb) (hUne.image _) hA.transfer (norm_transferDir hℓ)
      (inner_transferDrift_le hb) (Internal.forall_image hc) (Internal.contDiffOn_comp_symm hu)
      (Internal.continuousOn_closure_comp_symm huc)
      fun y hy => (nondivOperator_transfer_symm A b c u y).trans (Internal.forall_image hsol y hy))

/-- **Comparison principle** (Gilbarg and Trudinger Theorem 3.3), on a finite-dimensional real
normed space. With `c ≥ 0`, if `L u ≤ L v` on the set and `u ≤ v` on the boundary, then `u ≤ v` on
the closure. -/
theorem comparison_principle (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hA : IsUniformlyElliptic A U θ) {ℓ : StrongDual ℝ E} (hℓ : ℓ ≠ 0)
    (hb : ∀ x ∈ U, ℓ (b x) ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x) {u v : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOperator A b c u x ≤ nondivOperator A b c v x)
    (hbd : ∀ x ∈ frontier U, u x ≤ v x) : ∀ x ∈ closure U, u x ≤ v x :=
  Internal.forall_closure_pullback (P := fun x => u x ≤ v x)
    (Classical.nondivOperator.comparison_principle (Internal.isOpen_image hU)
      (Internal.isBounded_image hUb) (hUne.image _) hA.transfer (norm_transferDir hℓ)
      (inner_transferDrift_le hb) (Internal.forall_image hc) (Internal.contDiffOn_comp_symm hu)
      (Internal.contDiffOn_comp_symm hv) (Internal.continuousOn_closure_comp_symm huc)
      (Internal.continuousOn_closure_comp_symm hvc)
      (fun y hy => (nondivOperator_transfer_symm A b c u y).trans_le
        ((Internal.forall_image hL y hy).trans_eq (nondivOperator_transfer_symm A b c v y).symm))
      (Internal.forall_frontier_image hbd))

/-- **Uniqueness for the Dirichlet problem** (Gilbarg and Trudinger Theorem 3.3), on a
finite-dimensional real normed space. With `c ≥ 0`, two functions with the same image under `L` on
the set and the same boundary values agree on the closure. -/
theorem dirichlet_unique (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hA : IsUniformlyElliptic A U θ) {ℓ : StrongDual ℝ E} (hℓ : ℓ ≠ 0)
    (hb : ∀ x ∈ U, ℓ (b x) ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x) {u v : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOperator A b c u x = nondivOperator A b c v x)
    (hbd : ∀ x ∈ frontier U, u x = v x) : ∀ x ∈ closure U, u x = v x := fun x hx =>
  le_antisymm
    (comparison_principle hU hUb hUne hA hℓ hb hc hu hv huc hvc (fun x hx => (hL x hx).le)
      (fun x hx => (hbd x hx).le) x hx)
    (comparison_principle hU hUb hUne hA hℓ hb hc hv hu hvc huc (fun x hx => (hL x hx).ge)
      (fun x hx => (hbd x hx).ge) x hx)

/-- **Strong maximum principle** (Evans §6.4.2 Theorem 3, Gilbarg and Trudinger Theorem 3.5), on
a finite-dimensional real normed space. A subsolution, `C²` on a connected open set, that attains
its maximum over the set at an interior point is constant on the set. The coefficient is bounded
in operator norm, the drift and the zeroth-order coefficient are bounded, `c ≥ 0`, and `c` times
the maximum is nonnegative, which covers the clause `c = 0` and the clause `c ≥ 0` with a
nonnegative maximum. -/
theorem strong_maximum_principle (hU : IsOpen U) (hUc : IsPreconnected U)
    (hA : IsUniformlyElliptic A U θ) {Λ : ℝ} (hΛ : ∀ x ∈ U, ‖A x‖ ≤ Λ)
    (hb : ∀ x ∈ U, ‖b x‖ ≤ B) (hc0 : ∀ x ∈ U, 0 ≤ c x) {C : ℝ} (hcC : ∀ x ∈ U, c x ≤ C)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (hsub : ∀ x ∈ U, nondivOperator A b c u x ≤ 0)
    {x₀ : E} (hx₀ : x₀ ∈ U) (hmax : ∀ x ∈ U, u x ≤ u x₀) (hcu : ∀ x ∈ U, 0 ≤ c x * u x₀) :
    ∀ x ∈ U, u x = u x₀ := fun x hx => by
  simpa using Classical.nondivOperator.strong_maximum_principle (Internal.isOpen_image hU)
    (hUc.image _ (𝓛 : E →L[ℝ] 𝔽).continuous.continuousOn) hA.transfer
    (trace_transferCoeff_le hΛ) (norm_transferDrift_le hb) (Internal.forall_image hc0)
    (Internal.forall_image hcC) (Internal.contDiffOn_comp_symm hu)
    (fun y hy => (nondivOperator_transfer_symm A b c u y).trans_le
      (Internal.forall_image hsub y hy))
    (mem_image_of_mem _ hx₀) (fun y hy => (Internal.forall_image hmax y hy).trans_eq (by simp))
    (fun y hy => (Internal.forall_image hcu y hy).trans_eq (by simp)) (𝓛 x)
    (mem_image_of_mem _ hx)

/-- **Strong maximum principle with nonnegative zeroth-order coefficient** (Evans §6.4.2
Theorem 3(ii)), on a finite-dimensional real normed space. With `c ≥ 0`, a subsolution that attains
a nonnegative maximum at an interior point of a connected open set is constant on the set. -/
theorem strong_maximum_principle_of_nonneg (hU : IsOpen U) (hUc : IsPreconnected U)
    (hA : IsUniformlyElliptic A U θ) {Λ : ℝ} (hΛ : ∀ x ∈ U, ‖A x‖ ≤ Λ)
    (hb : ∀ x ∈ U, ‖b x‖ ≤ B) (hc0 : ∀ x ∈ U, 0 ≤ c x) {C : ℝ} (hcC : ∀ x ∈ U, c x ≤ C)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (hsub : ∀ x ∈ U, nondivOperator A b c u x ≤ 0)
    {x₀ : E} (hx₀ : x₀ ∈ U) (hmax : ∀ x ∈ U, u x ≤ u x₀) (hu0 : 0 ≤ u x₀) :
    ∀ x ∈ U, u x = u x₀ :=
  strong_maximum_principle hU hUc hA hΛ hb hc0 hcC hu hsub hx₀ hmax
    fun x hx => mul_nonneg (hc0 x hx) hu0

/-- A symmetric covector coefficient transfers to a symmetric matrix. -/
lemma Internal.isSymmetric_transferMat {M : StrongDual ℝ E →L[ℝ] E}
    (h : ∀ ξ η : StrongDual ℝ E, η (M ξ) = ξ (M η)) :
    ((transferMat M : 𝔽 →L[ℝ] 𝔽) : 𝔽 →ₗ[ℝ] 𝔽).IsSymmetric :=
  fun v w => Internal.inner_transferMat_comm M h v w

/-- A positive semidefinite covector coefficient transfers to a positive semidefinite matrix. -/
lemma Internal.inner_transferMat_self_nonneg {M : StrongDual ℝ E →L[ℝ] E}
    (h : ∀ ξ : StrongDual ℝ E, 0 ≤ ξ (M ξ)) (w : 𝔽) : 0 ≤ ⟪transferMat M w, w⟫ :=
  (Internal.inner_transferMat_self M w).symm ▸ h _

/-- **Strict maximum principle** (first step of the proof of Gilbarg and Trudinger Theorem 3.1),
on a finite-dimensional real normed space. A strict subsolution, meaning `L u < 0` at a point, has
no local maximum there whenever `c u ≥ 0` at the point. -/
theorem not_isLocalMax_of_neg {x₀ : E}
    (hsymm : ∀ ξ η : StrongDual ℝ E, η (A x₀ ξ) = ξ (A x₀ η))
    (hpsd : ∀ ξ : StrongDual ℝ E, 0 ≤ ξ (A x₀ ξ)) {u : E → ℝ} (hu : ContDiffAt ℝ 2 u x₀)
    (hcu : 0 ≤ c x₀ * u x₀) (hstrict : nondivOperator A b c u x₀ < 0) : ¬ IsLocalMax u x₀ :=
  fun hmax => Classical.nondivOperator.not_isLocalMax_of_neg (b := transferDrift b)
    (c := c ∘ 𝓛') (A := transferCoeff A) (x₀ := 𝓛 x₀) (u := u ∘ 𝓛')
    (transferCoeff_apply_toEuclidean A x₀ ▸ Internal.isSymmetric_transferMat hsymm)
    (transferCoeff_apply_toEuclidean A x₀ ▸ Internal.inner_transferMat_self_nonneg hpsd)
    (Internal.contDiffAt_comp_symm hu) (Internal.mul_comp_symm_apply c u x₀ ▸ hcu)
    ((nondivOperator_transfer A b c u x₀).trans_lt hstrict) (Internal.isLocalMax_comp_symm hmax)

end nondivOperator

end NormedClassical

end EllipticPdes
