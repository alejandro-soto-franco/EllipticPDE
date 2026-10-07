/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Existence.StrongMaximumCorollaries

/-!
# Maximum principles for subharmonic functions

The Laplacian is the non-divergence operator with the identity as coefficient matrix and no
lower-order terms, up to sign. The classical weak and strong maximum principles and the
uniqueness of the Dirichlet problem specialise to subharmonic, superharmonic and harmonic
functions. They are stated on a finite-dimensional real inner product space with Mathlib's
Laplacian `Δ` (the contraction of the Hessian against the identity), and then on Euclidean
space for the sum of the second coordinate partials.

## Main declarations

* `EllipticPdes.Classical.traceHessian_one`: `tr (D²u) = Δ u`.
* `EllipticPdes.Classical.laplacianSum`: the sum of the second coordinate partials.
* `EllipticPdes.Classical.nondivOp_laplace`: the Laplacian as a non-divergence operator.
* `EllipticPdes.Classical.weak_maximum_principle_subharmonic`: the weak maximum principle.
* `EllipticPdes.Classical.strong_maximum_principle_subharmonic`: the strong maximum principle.
* `EllipticPdes.Classical.strong_minimum_principle_superharmonic`: the strong minimum principle.
* `EllipticPdes.Classical.harmonic_const_of_max`, `harmonic_const_of_min`: a harmonic function
  attaining its supremum or infimum in the interior is constant.
* `EllipticPdes.Classical.dirichlet_unique_harmonic`: uniqueness for the Dirichlet problem.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Lemma XI.1.5,
Corollary XI.1.6, Lemma XI.1.7 (p. 92) and Lemma XI.2.4 (p. 95).
-/

@[expose] public section

open Set Filter Topology Metric InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Classical

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The contraction of the Hessian against the identity is the Laplacian. -/
theorem traceHessian_one (u : E → ℝ) (x : E) :
    traceHessian (1 : E →L[ℝ] E) u x = Laplacian.laplacian u x := by
  rw [traceHessian_eq_sum_iteratedFDeriv (stdOrthonormalBasis ℝ E),
    congrFun (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis (E := E) u) x]
  simp

/-- The Laplacian is the negative of the operator with identity coefficient and no lower-order
terms. -/
theorem nondivOperator_one (u : E → ℝ) (x : E) :
    nondivOperator (fun _ => (1 : E →L[ℝ] E)) (fun _ => 0) (fun _ => 0) u x
      = -Laplacian.laplacian u x := by
  simp [nondivOperator, traceHessian_one]

omit [FiniteDimensional ℝ E] in
/-- The identity coefficient is uniformly elliptic with constant one. -/
theorem isUniformlyElliptic_one (U : Set E) :
    IsUniformlyElliptic (fun _ : E => (1 : E →L[ℝ] E)) U 1 :=
  ⟨one_pos, fun _ _ => fun _ _ => rfl, fun _ _ ξ => by simp⟩

/-- The trace of the identity is the dimension. -/
theorem trace_one_le (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    LinearMap.trace ℝ E (((1 : E →L[ℝ] E)) : E →ₗ[ℝ] E) ≤ Module.finrank ℝ E := by
  simp

namespace laplacian

/-- **Weak maximum principle for subharmonic functions** (Guo Lemma XI.1.7). -/
theorem weak_maximum_principle_subharmonic [Nontrivial E] {U : Set E} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUne : U.Nonempty) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, 0 ≤ Laplacian.laplacian u x) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u x ≤ u y := by
  obtain ⟨e, he⟩ := (NormedSpace.sphere_nonempty (E := E)).mpr (zero_le_one : (0 : ℝ) ≤ 1)
  replace he : ‖e‖ = 1 := mem_sphere_zero_iff_norm.mp he
  exact nondivOperator.weak_maximum_principle hU hUb hUne (isUniformlyElliptic_one U) he
    (B := 0) (fun x _ => (inner_zero_left e).le) hu huc fun x hx => by
      rw [nondivOperator_one]; linarith [hsub x hx]

/-- **Strong maximum principle for subharmonic functions** (Guo Lemma XI.1.5). -/
theorem strong_maximum_principle_subharmonic {U : Set E} (hU : IsOpen U) (hUc : IsPreconnected U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (hsub : ∀ x ∈ U, 0 ≤ Laplacian.laplacian u x)
    {x₀ : E} (hx₀ : x₀ ∈ U) (hmax : ∀ x ∈ U, u x ≤ u x₀) : ∀ x ∈ U, u x = u x₀ :=
  nondivOperator.strong_maximum_principle hU hUc (isUniformlyElliptic_one U)
    (fun _ _ => trace_one_le E) (B := 0) (fun _ _ => norm_zero.le) (fun _ _ => le_rfl)
    (C := 0) (fun _ _ => le_rfl) hu (fun x hx => by
      rw [nondivOperator_one]; linarith [hsub x hx]) hx₀ hmax fun _ _ => (zero_mul _).ge

/-- **Strong minimum principle for superharmonic functions** (Guo Corollary XI.1.6). -/
theorem strong_minimum_principle_superharmonic {U : Set E} (hU : IsOpen U)
    (hUc : IsPreconnected U) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hsup : ∀ x ∈ U, Laplacian.laplacian u x ≤ 0) {x₀ : E} (hx₀ : x₀ ∈ U)
    (hmin : ∀ x ∈ U, u x₀ ≤ u x) : ∀ x ∈ U, u x = u x₀ := by
  have h := strong_maximum_principle_subharmonic hU hUc hu.neg
    (fun x hx => by
      have := congrFun (laplacian_neg (E := E) (f := u)) x
      simp only [Pi.neg_apply] at this
      change 0 ≤ Laplacian.laplacian (-u) x
      rw [this]
      linarith [hsup x hx]) hx₀ (fun x hx => by linarith [hmin x hx])
  intro x hx
  linarith [h x hx]

/-- **Uniqueness for the Dirichlet problem for the Laplacian** (Guo Lemma XI.2.4). -/
theorem dirichlet_unique_harmonic [Nontrivial E] {U : Set E} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUne : U.Nonempty) {u v : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hv : ContDiffOn ℝ 2 v U) (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, Laplacian.laplacian u x = Laplacian.laplacian v x)
    (hbd : ∀ x ∈ frontier U, u x = v x) : ∀ x ∈ closure U, u x = v x := by
  obtain ⟨e, he⟩ := (NormedSpace.sphere_nonempty (E := E)).mpr (zero_le_one : (0 : ℝ) ≤ 1)
  replace he : ‖e‖ = 1 := mem_sphere_zero_iff_norm.mp he
  exact nondivOperator.dirichlet_unique hU hUb hUne (isUniformlyElliptic_one U) he (B := 0)
    (fun x _ => (inner_zero_left e).le) (fun _ _ => le_rfl) hu hv huc hvc
    (fun x hx => by rw [nondivOperator_one, nondivOperator_one, hL x hx]) hbd

end laplacian

end General

/-! ### Euclidean space -/

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- The sum of the second coordinate partials. -/
def laplacianSum (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, partialD i (partialD i u) x

/-- The identity coefficient matrix. -/
def idCoeff (i j : Fin d) : ℝ := if i = j then 1 else 0

/-- The Laplacian is the negative of the non-divergence operator with the identity as
coefficient matrix and no lower-order terms. -/
theorem nondivOp_laplace (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    nondivOp (fun _ => idCoeff) (fun _ _ => 0) (fun _ => 0) u x = -laplacianSum u x := by
  classical
  unfold nondivOp laplacianSum idCoeff
  simp [ite_mul, Finset.sum_ite_eq]

/-- The identity matrix is symmetric. -/
theorem idCoeff_symm (i j : Fin d) : idCoeff i j = idCoeff j i := by
  unfold idCoeff
  by_cases h : i = j
  · subst h
    rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

/-- The identity matrix is elliptic with constant one. -/
theorem idCoeff_ell (ξ : Fin d → ℝ) :
    1 * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, idCoeff i j * ξ i * ξ j := by
  classical
  unfold idCoeff
  simp [ite_mul, Finset.sum_ite_eq, sq]

/-- The identity matrix is bounded by one. -/
theorem idCoeff_bdd (i j : Fin d) : |idCoeff i j| ≤ 1 := by
  unfold idCoeff
  by_cases h : i = j
  · rw [ite_eq_left h, abs_one]
  · rw [ite_eq_right h, abs_zero]
    exact zero_le_one

/-- The sum of the second partials of a function `C²` at a point is its Laplacian. -/
theorem laplacianSum_eq_laplacian {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {x : EuclideanSpace ℝ (Fin d)} (hu : ContDiffAt ℝ 2 u x) :
    laplacianSum u x = Laplacian.laplacian u x := by
  have h := nondivOp_laplace (d := d) u x
  rw [nondivOp_eq (b := fun _ _ => 0) hu] at h
  have e : (fun y : EuclideanSpace ℝ (Fin d) => matrixCLM (idCoeff (d := d)))
      = fun _ => (1 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) := by
    ext1 y
    ext ξ i
    simp [matrixCLM_apply, idCoeff]
  have h0 : (fun y : EuclideanSpace ℝ (Fin d) => (WithLp.toLp 2 (fun _ : Fin d => (0 : ℝ))
      : EuclideanSpace ℝ (Fin d))) = fun _ => 0 := by
    ext1; ext1; rfl
  rw [e, h0, nondivOperator_one] at h
  linarith

/-- The sum of the second partials is negated with the function. -/
theorem laplacianSum_neg {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ U) : laplacianSum (fun y => -u y) x = -laplacianSum u x := by
  rw [laplacianSum_eq_laplacian (hu.contDiffAt (hU.mem_nhds hx)),
    laplacianSum_eq_laplacian (hu.neg.contDiffAt (hU.mem_nhds hx))]
  have := congrFun (laplacian_neg (E := EuclideanSpace ℝ (Fin d)) (f := u)) x
  exact this

/-- **Weak maximum principle for subharmonic functions** (Guo Lemma XI.1.7). A function `C²`
on a bounded open set, continuous on its closure, with nonnegative Laplacian on the set, attains
its maximum over the closure on the boundary. -/
theorem weak_maximum_principle_subharmonic (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, 0 ≤ laplacianSum u x) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u x ≤ u y := by
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) := ⟨⟨EuclideanSpace.single ⟨0, hd⟩ 1, 0, by simp⟩⟩
  exact laplacian.weak_maximum_principle_subharmonic hU hUb hUne hu huc fun x hx => by
    rw [← laplacianSum_eq_laplacian (hu.contDiffAt (hU.mem_nhds hx))]; exact hsub x hx

/-- **Strong maximum principle for subharmonic functions** (Guo Lemma XI.1.5). A function `C²`
on a connected open set with nonnegative Laplacian that attains its supremum over the set at an
interior point is constant. -/
theorem strong_maximum_principle_subharmonic (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hsub : ∀ x ∈ U, 0 ≤ laplacianSum u x)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : x₀ ∈ U) (hmax : ∀ x ∈ U, u x ≤ u x₀) :
    ∀ x ∈ U, u x = u x₀ := by
  have _ := hd
  exact laplacian.strong_maximum_principle_subharmonic hU hUc hu (fun x hx => by
    rw [← laplacianSum_eq_laplacian (hu.contDiffAt (hU.mem_nhds hx))]; exact hsub x hx) hx₀ hmax

/-- **Strong minimum principle for superharmonic functions** (Guo Corollary XI.1.6). A function
`C²` on a connected open set with nonpositive Laplacian that attains its infimum over the set at
an interior point is constant. -/
theorem strong_minimum_principle_superharmonic (hd : 0 < d)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (hUc : IsPreconnected U)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hsup : ∀ x ∈ U, laplacianSum u x ≤ 0)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : x₀ ∈ U) (hmin : ∀ x ∈ U, u x₀ ≤ u x) :
    ∀ x ∈ U, u x = u x₀ := by
  have _ := hd
  exact laplacian.strong_minimum_principle_superharmonic hU hUc hu (fun x hx => by
    rw [← laplacianSum_eq_laplacian (hu.contDiffAt (hU.mem_nhds hx))]; exact hsup x hx) hx₀ hmin

/-- **Harmonic functions attaining their supremum are constant** (Guo Corollary XI.1.6). -/
theorem harmonic_const_of_max (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hharm : ∀ x ∈ U, laplacianSum u x = 0)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : x₀ ∈ U) (hmax : ∀ x ∈ U, u x ≤ u x₀) :
    ∀ x ∈ U, u x = u x₀ :=
  strong_maximum_principle_subharmonic hd hU hUc hu (fun x hx => (hharm x hx).ge) hx₀ hmax

/-- **Harmonic functions attaining their infimum are constant** (Guo Corollary XI.1.6). -/
theorem harmonic_const_of_min (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hharm : ∀ x ∈ U, laplacianSum u x = 0)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : x₀ ∈ U) (hmin : ∀ x ∈ U, u x₀ ≤ u x) :
    ∀ x ∈ U, u x = u x₀ :=
  strong_minimum_principle_superharmonic hd hU hUc hu (fun x hx => (hharm x hx).le) hx₀ hmin

/-- **Uniqueness for the Dirichlet problem for the Laplacian** (Guo Lemma XI.2.4, the uniqueness
clause). Two functions `C²` on a bounded open set and continuous on its closure, with the same
Laplacian on the set and the same boundary values, agree on the closure. -/
theorem dirichlet_unique_harmonic (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, laplacianSum u x = laplacianSum v x)
    (hbd : ∀ x ∈ frontier U, u x = v x) : ∀ x ∈ closure U, u x = v x := by
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) := ⟨⟨EuclideanSpace.single ⟨0, hd⟩ 1, 0, by simp⟩⟩
  exact laplacian.dirichlet_unique_harmonic hU hUb hUne hu hv huc hvc (fun x hx => by
    rw [← laplacianSum_eq_laplacian (hu.contDiffAt (hU.mem_nhds hx)),
      ← laplacianSum_eq_laplacian (hv.contDiffAt (hU.mem_nhds hx))]; exact hL x hx) hbd

end EllipticPdes.Classical
