/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Existence.ClassicalMaximum

/-!
# Hopf's lemma and the strong maximum principle

Hopf's lemma: a `C²` subsolution on a ball, continuous on the closed ball, that is strictly
below its value at a boundary point `x₀` throughout the ball, has positive outward normal
derivative at `x₀`. The barrier `v = exp(-λ|x - y|²) - exp(-λ r²)` is a subsolution on the
annulus `r/2 < |x - y| < r` for `λ` large, vanishes on the outer sphere and is positive on the
inner one, so `u + ε v - u(x₀)` is nonpositive on the boundary of the annulus for `ε` small and,
by the weak maximum principle, on the annulus. Along the inward radius through `x₀` the
function `u + ε v` is therefore at most its value at `x₀`, and its one-sided derivative there,
which is `-∂_ν u(x₀) + ε ∂_ν(-v)(x₀)`, is nonpositive. The normal derivative of `v` is negative,
which gives the strict inequality.

The strong maximum principle: a `C²` subsolution on a connected open set that attains its
maximum at an interior point is constant. If not, the set where the function is below the
maximum is open, nonempty, and has a frontier point inside the set; a small ball about a
nearby point of it, of radius the distance to the level set of the maximum, lies in it and
touches the level set at a point where Hopf's lemma gives a nonzero gradient, though the point
is an interior maximum.

## Main declarations

* `EllipticPdes.Classical.hopf_lemma_ball`: Hopf's lemma on a ball.
* `EllipticPdes.Classical.hopf_lemma`: Hopf's lemma at a boundary point with the interior
  ball condition.
* `EllipticPdes.Classical.strong_maximum_principle`: the strong maximum principle.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.4.2 Lemma (Hopf's Lemma, p. 347)
and Theorem 3 (p. 349);
D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§3.2 Lemma 3.4 (p. 34) and Theorem 3.5 (p. 35).
-/

@[expose] public section

open Set Filter Topology Metric

noncomputable section

namespace EllipticPdes.Classical

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-! ### The barrier -/

/-- The squared distance to `y` as a sum of squares. -/
def sqDist (y x : EuclideanSpace ℝ (Fin d)) : ℝ := ∑ i, (x i - y i) ^ 2

/-- The squared distance is the squared norm of the difference. -/
theorem sqDist_eq (y x : EuclideanSpace ℝ (Fin d)) : sqDist y x = ‖x - y‖ ^ 2 := by
  rw [sqDist, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]

/-- The derivative of the squared distance. -/
theorem hasFDerivAt_sqDist (y x : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (sqDist y)
      (∑ i, (2 * (x i - y i)) • (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) x := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) => (z i - y i) ^ 2)
        ((2 * (x i - y i)) • (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) x := by
    intro i _
    have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) => z i - y i)
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) x :=
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).hasFDerivAt.sub_const (y i)
    have h2 := h1.pow 2
    refine h2.congr_fderiv ?_
    simp only [Nat.add_one_sub_one, pow_one, nsmul_eq_mul, Nat.cast_ofNat]
  refine (HasFDerivAt.sum h).congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
  simp [sqDist, Finset.sum_apply]

/-- The barrier's exponential part `exp (-λ |x - y|²)`. -/
def barrierExp (lam : ℝ) (y x : EuclideanSpace ℝ (Fin d)) : ℝ := Real.exp (-lam * sqDist y x)

/-- The exponential part is positive. -/
theorem barrierExp_pos (lam : ℝ) (y x : EuclideanSpace ℝ (Fin d)) : 0 < barrierExp lam y x :=
  Real.exp_pos _

/-- The derivative of the exponential part. -/
theorem hasFDerivAt_barrierExp (lam : ℝ) (y x : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (barrierExp lam y)
      (barrierExp lam y x • ((-lam) • ∑ i, (2 * (x i - y i))
        • (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))) x := by
  have h1 := (hasFDerivAt_sqDist y x).const_mul (-lam)
  exact (Real.hasDerivAt_exp (-lam * sqDist y x)).comp_hasFDerivAt x h1

/-- The value of the derivative of the exponential part on a vector. -/
theorem fderiv_barrierExp_apply (lam : ℝ) (y x ξ : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (barrierExp lam y) x ξ
      = barrierExp lam y x * (-lam * ∑ i, 2 * (x i - y i) * ξ i) := by
  rw [(hasFDerivAt_barrierExp lam y x).fderiv]
  simp only [_root_.smul_apply, _root_.sum_apply, smul_eq_mul,
    proj_apply', Finset.mul_sum]

/-- The first partials of the exponential part. -/
theorem partialD_barrierExp (lam : ℝ) (y : EuclideanSpace ℝ (Fin d)) (i : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    partialD i (barrierExp lam y) x = -2 * lam * (x i - y i) * barrierExp lam y x := by
  simp only [partialD, fderiv_barrierExp_apply, PiLp.single_apply]
  classical
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    ring
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The first partials of the exponential part, as functions. -/
theorem partialD_barrierExp_eq (lam : ℝ) (y : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    partialD i (barrierExp lam y) = fun x => (-2 * lam) * ((x i - y i) * barrierExp lam y x) := by
  funext x
  rw [partialD_barrierExp]
  ring

/-- The second partials of the exponential part. -/
theorem partialD_partialD_barrierExp (lam : ℝ) (y : EuclideanSpace ℝ (Fin d)) (i j : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    partialD i (partialD j (barrierExp lam y)) x
      = (-2 * lam * (if j = i then 1 else 0)
          + 4 * lam ^ 2 * (x j - y j) * (x i - y i)) * barrierExp lam y x := by
  rw [partialD_barrierExp_eq]
  simp only [partialD]
  have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) => z j - y j)
      (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).hasFDerivAt.sub_const (y j)
  have h2 : HasFDerivAt
      (fun z : EuclideanSpace ℝ (Fin d) => -2 * lam * ((z j - y j) * barrierExp lam y z))
      ((-2 * lam) • ((x j - y j) • (barrierExp lam y x • ((-lam) • ∑ i, (2 * (x i - y i))
        • (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)))
        + barrierExp lam y x • (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))) x :=
    (h1.mul (hasFDerivAt_barrierExp lam y x)).const_mul (-2 * lam)
  rw [h2.fderiv]
  simp only [_root_.smul_apply, _root_.add_apply, smul_eq_mul,
    proj_apply', _root_.sum_apply, PiLp.single_apply]
  classical
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    ring
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The barrier `exp (-λ |x - y|²) - exp (-λ r²)`. -/
def barrier (lam r : ℝ) (y x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  barrierExp lam y x - Real.exp (-lam * r ^ 2)

/-- The barrier is smooth. -/
theorem contDiff_barrier (lam r : ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    ContDiff ℝ 2 (barrier lam r y) := by
  have hq : ContDiff ℝ 2 (sqDist y) := by
    unfold sqDist
    exact ContDiff.sum fun i _ =>
      ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff.sub
        contDiff_const).pow 2
  have he : ContDiff ℝ 2 (barrierExp lam y) :=
    Real.contDiff_exp.comp (contDiff_const.mul hq)
  exact he.sub contDiff_const

/-- The partials of the barrier are those of its exponential part. -/
theorem partialD_barrier (lam r : ℝ) (y : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    partialD i (barrier lam r y) = partialD i (barrierExp lam y) := by
  funext x
  have e : barrier lam r y = fun z => barrierExp lam y z - Real.exp (-lam * r ^ 2) := rfl
  simp only [partialD]
  rw [e, fderiv_sub_const]

/-- **Operator on the barrier.** -/
theorem nondivOp_barrier (a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) (c : EuclideanSpace ℝ (Fin d) → ℝ) (lam r : ℝ)
    (y x : EuclideanSpace ℝ (Fin d)) :
    nondivOp a b c (barrier lam r y) x
      = barrierExp lam y x * (2 * lam * ∑ i, a x i i
          - 4 * lam ^ 2 * ∑ i, ∑ j, a x i j * (x i - y i) * (x j - y j)
          - 2 * lam * ∑ i, b x i * (x i - y i)) + c x * barrier lam r y x := by
  classical
  unfold nondivOp
  simp only [partialD_barrier, partialD_partialD_barrierExp, partialD_barrierExp]
  set w : ℝ := barrierExp lam y x with hw
  have hterm : ∀ i j, a x i j * ((-2 * lam * (if j = i then 1 else 0)
      + 4 * lam ^ 2 * (x j - y j) * (x i - y i)) * w)
      = (if j = i then -2 * lam * w * a x i i else 0)
        + 4 * lam ^ 2 * w * (a x i j * (x i - y i) * (x j - y j)) := by
    intro i j
    split_ifs with h
    · subst h
      ring
    · ring
  have hdiag : ∑ i, ∑ j, a x i j * ((-2 * lam * (if j = i then 1 else 0)
      + 4 * lam ^ 2 * (x j - y j) * (x i - y i)) * w)
      = -2 * lam * w * ∑ i, a x i i
        + 4 * lam ^ 2 * w * ∑ i, ∑ j, a x i j * (x i - y i) * (x j - y j) := by
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.mul_sum]
  have hbsum : ∑ i, b x i * (-2 * lam * (x i - y i) * w)
      = -2 * lam * w * ∑ i, b x i * (x i - y i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hdiag, hbsum]
  ring

/-- **Lower bound on a transport sum.** If `|bᵢ| ≤ B` then
`-(B (n + ∑ vᵢ²) / 2) ≤ ∑ bᵢ vᵢ`, since `|v| ≤ (1 + v²) / 2`. -/
theorem neg_le_sum_mul_of_abs_le {n : ℕ} {b v : Fin n → ℝ} {B : ℝ} (hb : ∀ i, |b i| ≤ B) :
    -(B * (n + ∑ i, v i ^ 2) / 2) ≤ ∑ i, b i * v i := by
  have hterm : ∀ i, -(B * (1 + v i ^ 2) / 2) ≤ b i * v i := by
    intro i
    have h1 : |b i * v i| ≤ B * |v i| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hb i) (abs_nonneg _)
    have h2 : |v i| ≤ (1 + v i ^ 2) / 2 := by nlinarith [sq_nonneg (|v i| - 1), sq_abs (v i)]
    have h3 := neg_abs_le (b i * v i)
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hb i)
    nlinarith
  have hsum : ∑ i, -(B * (1 + v i ^ 2) / 2) = -(B * (n + ∑ i, v i ^ 2) / 2) := by
    simp only [Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.mul_sum,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  rw [← hsum]
  exact Finset.sum_le_sum fun i _ => hterm i

/-- **Choice of the barrier constant.** For `λ ≥ (2 d A + B (d + r²) + C) / (θ r²) + 1` and
`r²/4 ≤ q ≤ r²`, `λ (2 d A + B (d + q)) + C ≤ 4 λ² θ q`. -/
theorem barrier_coefficient_le {d : ℕ} {θ A B C r q lam : ℝ} (hθ : 0 < θ) (hr : 0 < r)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C) (hq1 : r ^ 2 / 4 ≤ q) (hq2 : q ≤ r ^ 2)
    (hlam : (2 * d * A + B * (d + r ^ 2) + C) / (θ * r ^ 2) + 1 ≤ lam) :
    lam * (2 * d * A + B * (d + q)) + C - 4 * lam ^ 2 * θ * q ≤ 0 := by
  have hθr : 0 < θ * r ^ 2 := by positivity
  have hlam0 : 0 ≤ (2 * d * A + B * (d + r ^ 2) + C) / (θ * r ^ 2) :=
    div_nonneg (add_nonneg (add_nonneg (mul_nonneg (by positivity) hA0)
      (mul_nonneg hB0 (by positivity))) hC0) hθr.le
  have hlam_pos : 0 < lam := by linarith
  have hkey : (2 * d * A + B * (d + r ^ 2) + C) / (θ * r ^ 2) * (θ * r ^ 2)
      = 2 * d * A + B * (d + r ^ 2) + C := div_mul_cancel₀ _ hθr.ne'
  have h1 : lam * θ * r ^ 2 ≥ 2 * d * A + B * (d + r ^ 2) + C + θ * r ^ 2 := by
    have := mul_le_mul_of_nonneg_right hlam hθr.le
    nlinarith
  have h2 : 4 * lam * θ * q ≥ lam * θ * r ^ 2 := by
    have := mul_le_mul_of_nonneg_left hq1 (by positivity : 0 ≤ 4 * lam * θ)
    nlinarith
  have h3 : B * (d + q) ≤ B * (d + r ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hB0
  have h4 : lam * (4 * lam * θ * q) ≥ lam * (lam * θ * r ^ 2) :=
    mul_le_mul_of_nonneg_left h2 hlam_pos.le
  have h5 : lam * (lam * θ * r ^ 2) ≥ lam * (2 * d * A + B * (d + r ^ 2) + C + θ * r ^ 2) :=
    mul_le_mul_of_nonneg_left h1 hlam_pos.le
  have h6 : lam * C ≥ C := by nlinarith
  nlinarith

/-- **Barrier as a subsolution on the annulus** for `λ` large: with the bounds on the
coefficients and `r²/4 ≤ |x - y|² ≤ r²`. -/
theorem nondivOp_barrier_nonpos (hd : 0 < d)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ}
    {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ} {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ A B C : ℝ} (hθ : 0 < θ) {x y : EuclideanSpace ℝ (Fin d)}
    (hell : ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ i j, |a x i j| ≤ A) (hb : ∀ i, |b x i| ≤ B) (hc0 : 0 ≤ c x) (hcC : c x ≤ C)
    {r : ℝ} (hr : 0 < r) (hq1 : r ^ 2 / 4 ≤ sqDist y x) (hq2 : sqDist y x ≤ r ^ 2) {lam : ℝ}
    (hlam : (2 * d * A + B * (d + r ^ 2) + C) / (θ * r ^ 2) + 1 ≤ lam) :
    nondivOp a b c (barrier lam r y) x ≤ 0 := by
  rw [nondivOp_barrier]
  have hw := barrierExp_pos lam y x
  set i₀ : Fin d := ⟨0, hd⟩ with hi₀
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (ha i₀ i₀)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hb i₀)
  have hC0 : 0 ≤ C := hc0.trans hcC
  have hq0 : 0 ≤ sqDist y x := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- the three sums
  have hS1 : ∑ i, a x i i ≤ d * A := by
    calc ∑ i, a x i i ≤ ∑ _i : Fin d, A :=
          Finset.sum_le_sum fun i _ => (le_abs_self _).trans (ha i i)
      _ = d * A := by simp
  have hS2 : θ * sqDist y x ≤ ∑ i, ∑ j, a x i j * (x i - y i) * (x j - y j) := by
    have := hell fun i => x i - y i
    simpa [sqDist] using this
  have hS3 : -(B * (d + sqDist y x) / 2) ≤ ∑ i, b x i * (x i - y i) :=
    neg_le_sum_mul_of_abs_le (b := fun i => b x i) (v := fun i => x i - y i) hb
  -- the choice of `λ`
  have hθr : 0 < θ * r ^ 2 := by positivity
  have hlam0 : 0 ≤ (2 * d * A + B * (d + r ^ 2) + C) / (θ * r ^ 2) :=
    div_nonneg (add_nonneg (add_nonneg (mul_nonneg (by positivity) hA0)
      (mul_nonneg hB0 (by positivity))) hC0) hθr.le
  have hlam1 : 1 ≤ lam := by linarith
  have hlam_pos : 0 < lam := by linarith
  have hbr : lam * (2 * d * A + B * (d + sqDist y x)) + C - 4 * lam ^ 2 * θ * sqDist y x ≤ 0 :=
    barrier_coefficient_le hθ hr hA0 hB0 hC0 hq1 hq2 hlam
  -- the zeroth-order term is at most `C` times the exponential part
  have hbar_nonneg : 0 ≤ barrier lam r y x := by
    simp only [barrier, barrierExp, sub_nonneg]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hbar_le : barrier lam r y x ≤ barrierExp lam y x := by
    simp only [barrier, barrierExp]
    linarith [Real.exp_pos (-lam * r ^ 2)]
  have hcv : c x * barrier lam r y x ≤ C * barrierExp lam y x :=
    (mul_le_mul_of_nonneg_right hcC hbar_nonneg).trans (mul_le_mul_of_nonneg_left hbar_le hC0)
  have hX : 2 * lam * ∑ i, a x i i
      - 4 * lam ^ 2 * ∑ i, ∑ j, a x i j * (x i - y i) * (x j - y j)
      - 2 * lam * ∑ i, b x i * (x i - y i) + C ≤ 0 := by
    have e1 : 2 * lam * ∑ i, a x i i ≤ 2 * lam * (d * A) :=
      mul_le_mul_of_nonneg_left hS1 (by positivity)
    have e2 : 4 * lam ^ 2 * (θ * sqDist y x)
        ≤ 4 * lam ^ 2 * ∑ i, ∑ j, a x i j * (x i - y i) * (x j - y j) :=
      mul_le_mul_of_nonneg_left hS2 (by positivity)
    have e3 : 2 * lam * (-(B * (d + sqDist y x) / 2)) ≤ 2 * lam * ∑ i, b x i * (x i - y i) :=
      mul_le_mul_of_nonneg_left hS3 (by positivity)
    nlinarith
  calc barrierExp lam y x * (2 * lam * ∑ i, a x i i
        - 4 * lam ^ 2 * ∑ i, ∑ j, a x i j * (x i - y i) * (x j - y j)
        - 2 * lam * ∑ i, b x i * (x i - y i)) + c x * barrier lam r y x
      ≤ barrierExp lam y x * (2 * lam * ∑ i, a x i i
        - 4 * lam ^ 2 * ∑ i, ∑ j, a x i j * (x i - y i) * (x j - y j)
        - 2 * lam * ∑ i, b x i * (x i - y i)) + C * barrierExp lam y x := by linarith
    _ = barrierExp lam y x * (2 * lam * ∑ i, a x i i
        - 4 * lam ^ 2 * ∑ i, ∑ j, a x i j * (x i - y i) * (x j - y j)
        - 2 * lam * ∑ i, b x i * (x i - y i) + C) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw.le hX

/-! ### Steps of Hopf's lemma -/

section Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The frontier of an open annulus lies on its two boundary spheres. -/
theorem frontier_ball_sdiff_closedBall_subset (y : E) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    frontier (ball y r \ closedBall y s) ⊆ sphere y r ∪ sphere y s := by
  rw [sdiff_eq]
  refine (frontier_inter_subset _ _).trans ?_
  rw [frontier_compl, frontier_ball y hr.ne', frontier_closedBall y hs.ne']
  exact union_subset_union inter_subset_left inter_subset_right

/-- A function continuous on a closed ball and at most `c` on the open ball is at most `c` on
the sphere. -/
theorem le_of_forall_ball_le {u : E → ℝ} {y z : E} {r c : ℝ} (hr : 0 < r)
    (huc : ContinuousOn u (closedBall y r)) (h : ∀ x ∈ ball y r, u x ≤ c)
    (hz : dist z y = r) : u z ≤ c :=
  ContinuousWithinAt.closure_le (s := ball y r) (by rw [closure_ball y hr.ne']; exact hz.le)
    ((huc z (mem_closedBall.2 hz.le)).mono ball_subset_closedBall) continuousWithinAt_const h

end Topology

/-- A function continuous on a closed ball and strictly below `u x₀` on the open ball stays a
fixed margin `δ` below `u x₀` on each concentric sphere of smaller radius. -/
theorem exists_gap_on_sphere {E : Type*} [MetricSpace E] [ProperSpace E] {u : E → ℝ} {y x₀ : E}
    {r s : ℝ} (hsr : s < r) (huc : ContinuousOn u (closedBall y r))
    (hlt : ∀ x ∈ ball y r, u x < u x₀) (hne : (sphere y s).Nonempty) :
    ∃ δ > 0, ∀ z ∈ sphere y s, u z ≤ u x₀ - δ := by
  obtain ⟨p, hp, hpmax⟩ := (isCompact_sphere y s).exists_isMaxOn hne
    (huc.mono (sphere_subset_closedBall.trans (closedBall_subset_closedBall hsr.le)))
  have hpb : p ∈ ball y r := by rw [mem_ball, mem_sphere.1 hp]; exact hsr
  exact ⟨u x₀ - u p, sub_pos.2 (hlt p hpb),
    fun z hz => by linarith [(show u z ≤ u p from hpmax hz)]⟩

/-- The barrier vanishes on the outer sphere. -/
theorem barrier_eq_zero (lam : ℝ) {r : ℝ} {y z : EuclideanSpace ℝ (Fin d)} (hz : dist z y = r) :
    barrier lam r y z = 0 := by
  simp only [barrier, barrierExp, sqDist_eq]
  rw [← dist_eq_norm, hz, sub_self]

/-- The maximum `exp (-λ (r/2)²) - exp (-λ r²)` of the barrier outside the inner ball. -/
def barrierMax (lam r : ℝ) : ℝ := Real.exp (-lam * (r / 2) ^ 2) - Real.exp (-lam * r ^ 2)

/-- The maximum of the barrier outside the inner ball is positive. -/
theorem barrierMax_pos {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) : 0 < barrierMax lam r := by
  rw [barrierMax, sub_pos]
  apply Real.exp_lt_exp.mpr
  have hsq : (r / 2) ^ 2 < r ^ 2 := by nlinarith
  nlinarith [mul_lt_mul_of_pos_left hsq hlam]

/-- Outside the inner ball of radius `r / 2` the barrier is at most `barrierMax`. -/
theorem barrier_le_barrierMax {lam r : ℝ} (hlam : 0 ≤ lam) (hr : 0 ≤ r)
    {y z : EuclideanSpace ℝ (Fin d)} (hz : r / 2 ≤ dist z y) :
    barrier lam r y z ≤ barrierMax lam r := by
  simp only [barrier, barrierExp, sqDist_eq, barrierMax]
  rw [← dist_eq_norm]
  have h1 : (r / 2) ^ 2 ≤ dist z y ^ 2 := by nlinarith
  have : -lam * dist z y ^ 2 ≤ -lam * (r / 2) ^ 2 := by nlinarith
  linarith [Real.exp_le_exp.mpr this]

/-- **Radial derivative of the barrier.** At a point of the outer sphere the derivative of the
barrier along the inward radius is `2 λ r² exp (-λ r²)`. -/
theorem fderiv_barrier_radial (lam r : ℝ) {y x₀ : EuclideanSpace ℝ (Fin d)}
    (hx₀ : dist x₀ y = r) :
    fderiv ℝ (barrier lam r y) x₀ (y - x₀) = 2 * lam * r ^ 2 * barrierExp lam y x₀ := by
  have hfv : fderiv ℝ (barrier lam r y) x₀ = fderiv ℝ (barrierExp lam y) x₀ :=
    fderiv_sub_const _
  rw [hfv, fderiv_barrierExp_apply]
  have hsq : ∑ i, (x₀ i - y i) ^ 2 = r ^ 2 := by
    have := sqDist_eq y x₀
    rwa [sqDist, ← dist_eq_norm, hx₀] at this
  have hsum : ∑ i, 2 * (x₀ i - y i) * (y - x₀) i = -2 * r ^ 2 := by
    calc ∑ i, 2 * (x₀ i - y i) * (y - x₀) i = ∑ i, -2 * (x₀ i - y i) ^ 2 :=
          Finset.sum_congr rfl fun i _ => by rw [PiLp.sub_apply]; ring
      _ = -2 * r ^ 2 := by rw [← Finset.mul_sum, hsq]
  rw [hsum]
  ring

/-- **The perturbed function is a subsolution on the annulus.** At a point `z` of the annulus
`r/2 < |z - y| < r` where `u` is a subsolution and `λ` is large, `u + ε v - k` is a subsolution
for every `ε ≥ 0`, with `v` the barrier. -/
theorem nondivOp_perturbation_nonpos (hd : 0 < d)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ}
    {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ} {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ A B C : ℝ} (hθ : 0 < θ) {R : Set (EuclideanSpace ℝ (Fin d))} (hRo : IsOpen R)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u R) {z y : EuclideanSpace ℝ (Fin d)}
    (hz : z ∈ R) (hell : ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a z i j * ξ i * ξ j)
    (ha : ∀ i j, |a z i j| ≤ A) (hb : ∀ i, |b z i| ≤ B) (hc0 : 0 ≤ c z) (hcC : c z ≤ C)
    {r : ℝ} (hr : 0 < r) (hq1 : r ^ 2 / 4 ≤ sqDist y z) (hq2 : sqDist y z ≤ r ^ 2)
    {lam : ℝ} (hlam : (2 * d * A + B * (d + r ^ 2) + C) / (θ * r ^ 2) + 1 ≤ lam)
    (hsub : nondivOp a b c u z ≤ 0) {k ε : ℝ} (hε : 0 ≤ ε) (hck : 0 ≤ c z * k) :
    nondivOp a b c (fun x => u x + ε * barrier lam r y x - k) z ≤ 0 := by
  have hvC := (contDiff_barrier lam r y).contDiffOn (s := R)
  have hgC2 : ContDiffOn ℝ 2 (fun x => u x + ε * barrier lam r y x) R :=
    hu.add (contDiffOn_const.mul hvC)
  rw [nondivOp_sub_const hRo hgC2 a b c k hz, nondivOp_add_smul hRo hu hvC a b c ε hz]
  have h2 := nondivOp_barrier_nonpos hd hθ hell ha hb hc0 hcC hr hq1 hq2 hlam
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hε h2]

/-- **The perturbed function is below `u x₀` on the boundary of the annulus.** On the outer
sphere `v` vanishes and `u ≤ u x₀`; on the inner sphere `u ≤ u x₀ - δ` and `ε v ≤ δ / 2`. -/
theorem add_mul_barrier_le_of_mem_frontier {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {y x₀ z : EuclideanSpace ℝ (Fin d)} {r lam δ ε : ℝ} (hr : 0 < r) (hlam : 0 ≤ lam)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hεv : ε * barrierMax lam r ≤ δ / 2)
    (huc : ContinuousOn u (closedBall y r))
    (hlt : ∀ x ∈ ball y r, u x < u x₀) (hgap : ∀ z ∈ sphere y (r / 2), u z ≤ u x₀ - δ)
    (hz : z ∈ frontier (ball y r \ closedBall y (r / 2))) :
    u z + ε * barrier lam r y z ≤ u x₀ := by
  rcases frontier_ball_sdiff_closedBall_subset y hr (half_pos hr) hz with hz | hz
  · have huz := le_of_forall_ball_le hr huc (fun x hx => (hlt x hx).le) (mem_sphere.1 hz)
    rw [barrier_eq_zero lam (mem_sphere.1 hz), mul_zero, add_zero]
    exact huz
  · have h3 : ε * barrier lam r y z ≤ δ / 2 :=
      (mul_le_mul_of_nonneg_left (barrier_le_barrierMax hlam hr.le (mem_sphere.1 hz).ge) hε).trans
        hεv
    linarith [hgap z hz]

/-- A point moved from `x₀` towards the centre `y` by the fraction `s ≤ 1` of the radius is at
distance `(1 - s) r` from the centre. -/
theorem dist_add_smul_sub_center {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x₀ y : E}
    {r s : ℝ} (hx₀ : dist x₀ y = r) (hs : s ≤ 1) : dist (x₀ + s • (y - x₀)) y = (1 - s) * r := by
  have e : x₀ + s • (y - x₀) - y = (1 - s) • (x₀ - y) := by
    simp only [sub_smul, one_smul, smul_sub]
    abel
  rw [dist_eq_norm, e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), ← dist_eq_norm,
    hx₀]

/-- **Hopf's lemma on a ball** (Evans §6.4.2 Lemma, Gilbarg and Trudinger Lemma 3.4). A
subsolution on a ball, continuous on the closed ball, strictly below its value at a point
`x₀` of the sphere throughout the ball, and differentiable at `x₀`, has positive derivative
at `x₀` in the outward radial direction `x₀ - y`. The zeroth-order coefficient is nonnegative
and bounded, and `c u(x₀) ≥ 0`, which covers the clause `c = 0` and the clause `c ≥ 0` with
`u(x₀) ≥ 0`. -/
theorem hopf_lemma_ball (hd : 0 < d) {y : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 < r)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ A B C : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ ball y r, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ ball y r, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ ball y r, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ ball y r, ∀ i, |b x i| ≤ B)
    (hc0 : ∀ x ∈ ball y r, 0 ≤ c x) (hcC : ∀ x ∈ ball y r, c x ≤ C)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u (ball y r))
    (huc : ContinuousOn u (closedBall y r))
    (hsub : ∀ x ∈ ball y r, nondivOp a b c u x ≤ 0)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : dist x₀ y = r) (hlt : ∀ x ∈ ball y r, u x < u x₀)
    (hcu : ∀ x ∈ ball y r, 0 ≤ c x * u x₀) (hdiff : DifferentiableAt ℝ u x₀) :
    0 < fderiv ℝ u x₀ (x₀ - y) := by
  classical
  set i₀ : Fin d := ⟨0, hd⟩ with hi₀
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (ha y (mem_ball_self hr) i₀ i₀)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hb y (mem_ball_self hr) i₀)
  have hC0 : 0 ≤ C := (hc0 y (mem_ball_self hr)).trans (hcC y (mem_ball_self hr))
  set R : Set (EuclideanSpace ℝ (Fin d)) := ball y r \ closedBall y (r / 2) with hRdef
  have hRo : IsOpen R := isOpen_ball.sdiff isClosed_closedBall
  have hRsub : R ⊆ ball y r := sdiff_subset
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) := ⟨⟨e i₀, 0, by simp [e]⟩⟩
  obtain ⟨p, hp⟩ : (sphere y (3 * r / 4)).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by positivity)
  have hRne : R.Nonempty := ⟨p, by
    rw [mem_sphere] at hp
    exact ⟨mem_ball.2 (by linarith), by rw [mem_closedBall, not_le]; linarith⟩⟩
  have hclR : closure R ⊆ closedBall y r :=
    (closure_mono hRsub).trans (closure_ball y hr.ne').subset
  -- the inner sphere: `u` is below `u x₀` by a margin `δ`
  obtain ⟨δ, hδ, hgap⟩ := exists_gap_on_sphere (u := u) (y := y) (x₀ := x₀) (s := r / 2)
    (by linarith) huc hlt (NormedSpace.sphere_nonempty.mpr (by positivity))
  -- the barrier constants
  set lam : ℝ := (2 * d * A + B * (d + r ^ 2) + C) / (θ * r ^ 2) + 1 with hlam
  have hlam_pos : 0 < lam := by
    have : 0 ≤ (2 * d * A + B * (d + r ^ 2) + C) / (θ * r ^ 2) :=
      div_nonneg (add_nonneg (add_nonneg (mul_nonneg (by positivity) hA0)
        (mul_nonneg hB0 (by positivity))) hC0) (by positivity)
    linarith
  have hvmax := barrierMax_pos hlam_pos hr
  set ε : ℝ := δ / (2 * barrierMax lam r) with hε
  have hεpos : 0 < ε := by positivity
  -- `u + ε v` is a subsolution on the annulus, and the weak maximum principle applies
  have hvC : ContDiff ℝ 2 (barrier lam r y) := contDiff_barrier lam r y
  have hgC2 : ContDiffOn ℝ 2 (fun x => u x + ε * barrier lam r y x - u x₀) R :=
    ((hu.mono hRsub).add (contDiffOn_const.mul hvC.contDiffOn)).sub contDiffOn_const
  have hgsub : ∀ z ∈ R, nondivOp a b c (fun x => u x + ε * barrier lam r y x - u x₀) z ≤ 0 := by
    intro z hz
    have hzb := hRsub hz
    refine nondivOp_perturbation_nonpos hd hθ hRo (hu.mono hRsub) hz (hell z hzb) (ha z hzb)
      (hb z hzb) (hc0 z hzb) (hcC z hzb) hr ?_ ?_ le_rfl (hsub z hzb) hεpos.le (hcu z hzb)
    · rw [sqDist_eq, ← dist_eq_norm]
      have := hz.2
      rw [mem_closedBall, not_le] at this
      nlinarith
    · rw [sqDist_eq, ← dist_eq_norm]
      have := hz.1
      rw [mem_ball] at this
      nlinarith [dist_nonneg (x := z) (y := y)]
  have hgc : ContinuousOn (fun x => u x + ε * barrier lam r y x - u x₀) (closure R) :=
    ((huc.mono hclR).add (continuousOn_const.mul hvC.continuous.continuousOn)).sub
      continuousOn_const
  obtain ⟨z, hzfr, hzmax⟩ := weak_maximum_principle_of_nonneg hd hRo
    (isBounded_ball.subset hRsub) hRne hθ (fun x hx => hsymm x (hRsub hx))
    (fun x hx => hell x (hRsub hx)) (fun x hx => hb x (hRsub hx)) (fun x hx => hc0 x (hRsub hx))
    hgC2 hgc hgsub
  have hgbound : ∀ x ∈ closure R, u x + ε * barrier lam r y x ≤ u x₀ := by
    intro x hx
    have hz' : u z + ε * barrier lam r y z - u x₀ ≤ 0 := by
      have hεv : ε * barrierMax lam r ≤ δ / 2 := by rw [hε]; field_simp; rfl
      linarith [add_mul_barrier_le_of_mem_frontier hr hlam_pos.le hδ.le hεpos.le hεv huc hlt hgap
        hzfr]
    have := hzmax x hx
    rw [max_eq_right hz'] at this
    linarith
  -- the one-sided derivative along the inward radius
  have hgd : HasFDerivAt (fun x => u x + ε * barrier lam r y x)
      (fderiv ℝ u x₀ + ε • fderiv ℝ (barrier lam r y) x₀) x₀ :=
    hdiff.hasFDerivAt.add ((hvC.differentiable (by simp) x₀).hasFDerivAt.const_mul ε)
  have hmax : IsLocalMaxOn (fun x => u x + ε * barrier lam r y x) (insert x₀ R) x₀ := by
    refine (isMaxOn_iff.2 fun x hx => ?_).isLocalMaxOn
    rcases hx with rfl | hx
    · exact le_rfl
    · rw [barrier_eq_zero lam hx₀, mul_zero, add_zero]
      exact hgbound x (subset_closure hx)
  have hseg : (1 / 4 : ℝ) • (y - x₀) ∈ posTangentConeAt (insert x₀ R) x₀ := by
    refine mem_posTangentConeAt_of_segment_subset ?_
    rw [segment_eq_image']
    rintro _ ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · simp [← h0]
    · simp only [add_sub_cancel_left, smul_smul]
      refine Or.inr ⟨?_, ?_⟩
      · rw [mem_ball, dist_add_smul_sub_center hx₀ (by nlinarith [ht.2])]
        nlinarith [ht.2]
      · rw [mem_closedBall, not_le, dist_add_smul_sub_center hx₀ (by nlinarith [ht.2])]
        nlinarith [ht.2]
  have hder := hmax.hasFDerivWithinAt_nonpos hgd.hasFDerivWithinAt hseg
  simp only [_root_.add_apply, _root_.smul_apply, map_smul, smul_eq_mul,
    fderiv_barrier_radial lam r hx₀] at hder
  have hfu : fderiv ℝ u x₀ (y - x₀) = -fderiv ℝ u x₀ (x₀ - y) := by
    rw [← neg_sub, map_neg]
  rw [hfu] at hder
  have hpos : 0 < ε * (2 * lam * r ^ 2 * barrierExp lam y x₀) := by
    have := barrierExp_pos lam y x₀
    positivity
  linarith

/-- **Hopf's lemma** (Evans §6.4.2 Lemma, Gilbarg and Trudinger Lemma 3.4). A subsolution on
an open set, continuous on its closure, strictly below its value at a point `x₀` throughout the
set, and differentiable at `x₀`, has positive derivative at `x₀` in the outward direction of any
ball inside the set whose sphere passes through `x₀`. The zeroth-order coefficient is
nonnegative and bounded with `c u(x₀) ≥ 0`, which covers both clauses of the sources. -/
theorem hopf_lemma (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {θ A B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    {c : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ} (hc0 : ∀ x ∈ U, 0 ≤ c x) (hcC : ∀ x ∈ U, c x ≤ C)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, nondivOp a b c u x ≤ 0)
    {x₀ y : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 < r) (hball : ball y r ⊆ U)
    (hx₀ : dist x₀ y = r) (hlt : ∀ x ∈ U, u x < u x₀) (hcu : ∀ x ∈ U, 0 ≤ c x * u x₀)
    (hdiff : DifferentiableAt ℝ u x₀) :
    0 < fderiv ℝ u x₀ (x₀ - y) := by
  have hcl : closedBall y r ⊆ closure U := by
    rw [← closure_ball y hr.ne']
    exact closure_mono hball
  exact hopf_lemma_ball hd hr hθ (fun x hx => hsymm x (hball hx)) (fun x hx => hell x (hball hx))
    (fun x hx => ha x (hball hx)) (fun x hx => hb x (hball hx)) (fun x hx => hc0 x (hball hx))
    (fun x hx => hcC x (hball hx)) (hu.mono hball) (huc.mono hcl)
    (fun x hx => hsub x (hball hx)) hx₀ (fun x hx => hlt x (hball hx))
    (fun x hx => hcu x (hball hx)) hdiff

/-! ### The strong maximum principle -/

/-- **Strong maximum principle** (Evans §6.4.2 Theorem 3, Gilbarg and Trudinger Theorem 3.5).
A subsolution, `C²` on a connected open set, that attains its maximum over the set at an
interior point is constant on the set. The zeroth-order coefficient is nonnegative and bounded
with `c` times the maximum nonnegative, which covers the clause `c = 0` and the clause `c ≥ 0`
with a nonnegative maximum. -/
theorem strong_maximum_principle (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ A B C : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    (hc0 : ∀ x ∈ U, 0 ≤ c x) (hcC : ∀ x ∈ U, c x ≤ C)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hsub : ∀ x ∈ U, nondivOp a b c u x ≤ 0)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : x₀ ∈ U) (hmax : ∀ x ∈ U, u x ≤ u x₀)
    (hcu : ∀ x ∈ U, 0 ≤ c x * u x₀) :
    ∀ x ∈ U, u x = u x₀ := by
  classical
  by_contra hne
  simp only [not_forall, exists_prop] at hne
  obtain ⟨x₁, hx₁U, hx₁⟩ := hne
  -- the set where `u` is below the maximum
  set V : Set (EuclideanSpace ℝ (Fin d)) := U ∩ u ⁻¹' Iio (u x₀) with hVdef
  have hVo : IsOpen V := hu.continuousOn.isOpen_inter_preimage hU isOpen_Iio
  have hVU : V ⊆ U := inter_subset_left
  have hx₁V : x₁ ∈ V := ⟨hx₁U, lt_of_le_of_ne (hmax x₁ hx₁U) hx₁⟩
  -- a point of the set on the frontier of `V`
  have hnot : ¬ U ⊆ V := fun h => by
    have : u x₀ < u x₀ := (h hx₀).2
    exact lt_irrefl _ this
  have hex : ∃ z ∈ U, z ∈ closure V ∧ z ∉ V := by
    by_contra hcon
    apply hnot
    refine hUc.subset_of_closure_inter_subset hVo ⟨x₁, hx₁U, hx₁V⟩ fun z hz => ?_
    by_contra hzV
    exact hcon ⟨z, hz.2, hz.1, hzV⟩
  obtain ⟨z, hzU, hzcl, hzV⟩ := hex
  have hzM : u z = u x₀ := le_antisymm (hmax z hzU) (not_lt.mp fun h => hzV ⟨hzU, h⟩)
  -- a ball about `z` in the set, and a point of `V` near `z`
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hU z hzU
  obtain ⟨y, hyV, hyz⟩ := Metric.mem_closure_iff.mp hzcl (ρ / 2) (by positivity)
  have hyM : u y < u x₀ := hyV.2
  have hcb : closedBall y (ρ / 2) ⊆ U :=
    (closedBall_subset_ball' (by rw [dist_comm]; linarith)).trans hρU
  -- the level set of the maximum near `y`
  set K : Set (EuclideanSpace ℝ (Fin d)) := closedBall y (ρ / 2) ∩ u ⁻¹' {u x₀} with hKdef
  have hKclosed : IsClosed K :=
    (hu.continuousOn.mono hcb).preimage_isClosed_of_isClosed isClosed_closedBall
      isClosed_singleton
  have hKc : IsCompact K :=
    (isCompact_closedBall y (ρ / 2)).of_isClosed_subset hKclosed inter_subset_left
  have hzy : dist z y ≤ ρ / 2 := hyz.le
  have hKne : K.Nonempty := ⟨z, mem_closedBall.mpr hzy, hzM⟩
  obtain ⟨x₂, hx₂K, hx₂d⟩ := hKc.exists_infDist_eq_dist hKne y
  set r : ℝ := infDist y K with hr
  have hyK : y ∉ K := fun h => hyM.ne h.2
  have hzK : z ∈ K := ⟨mem_closedBall.mpr hzy, hzM⟩
  have hrpos : 0 < r := by
    rw [hr]
    refine (infDist_pos_iff_notMem_closure hKne).mp ?_
    rw [hKclosed.closure_eq]
    exact hyK
  have hrle : r ≤ ρ / 2 := by
    rw [hr]
    exact (infDist_le_dist_of_mem hzK).trans (by rw [dist_comm]; exact hzy)
  -- the ball of radius `r` about `y` lies below the maximum
  have hballU : ball y r ⊆ U :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hrle)).trans hcb
  have hballV : ∀ x ∈ ball y r, u x < u x₀ := by
    intro x hx
    have hxU : x ∈ U := hballU hx
    rcases lt_or_eq_of_le (hmax x hxU) with h | h
    · exact h
    · exfalso
      have hxK : x ∈ K := ⟨mem_closedBall.mpr ((mem_ball.mp hx).le.trans hrle), h⟩
      have : infDist y K ≤ dist y x := infDist_le_dist_of_mem hxK
      rw [← hr, dist_comm] at this
      exact absurd (mem_ball.mp hx) (not_lt.mpr this)
  -- Hopf's lemma at the touching point
  have hx₂dist : dist x₂ y = r := by
    rw [dist_comm]
    exact hx₂d.symm
  have hx₂M : u x₂ = u x₀ := hx₂K.2
  have hx₂U : x₂ ∈ U := hcb hx₂K.1
  have hdiff : DifferentiableAt ℝ u x₂ :=
    (hu.contDiffAt (hU.mem_nhds hx₂U)).differentiableAt (by simp)
  have hhopf := hopf_lemma_ball hd hrpos hθ (fun x hx => hsymm x (hballU hx))
    (fun x hx => hell x (hballU hx)) (fun x hx => ha x (hballU hx))
    (fun x hx => hb x (hballU hx)) (fun x hx => hc0 x (hballU hx))
    (fun x hx => hcC x (hballU hx)) (hu.mono hballU)
    (hu.continuousOn.mono ((closedBall_subset_closedBall hrle).trans hcb))
    (fun x hx => hsub x (hballU hx)) hx₂dist (fun x hx => by rw [hx₂M]; exact hballV x hx)
    (fun x hx => by rw [hx₂M]; exact hcu x (hballU hx)) hdiff
  -- but `x₂` is an interior maximum, so the gradient vanishes there
  have hloc : IsLocalMax u x₂ := by
    have hmax' : IsMaxOn u U x₂ := fun x hx => by
      rw [hx₂M]
      exact hmax x hx
    exact hmax'.isLocalMax (hU.mem_nhds hx₂U)
  rw [hloc.fderiv_eq_zero] at hhopf
  simp at hhopf

/-- **Strong maximum principle with nonnegative zeroth-order coefficient** (Evans §6.4.2
Theorem 3(ii)). With `c ≥ 0`, a subsolution that attains a nonnegative maximum at an interior
point of a connected open set is constant on the set. -/
theorem strong_maximum_principle_of_nonneg (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ A B C : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    (hc0 : ∀ x ∈ U, 0 ≤ c x) (hcC : ∀ x ∈ U, c x ≤ C)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hsub : ∀ x ∈ U, nondivOp a b c u x ≤ 0)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : x₀ ∈ U) (hmax : ∀ x ∈ U, u x ≤ u x₀)
    (hu0 : 0 ≤ u x₀) : ∀ x ∈ U, u x = u x₀ :=
  strong_maximum_principle hd hU hUc hθ hsymm hell ha hb hc0 hcC hu hsub hx₀ hmax
    fun x hx => mul_nonneg (hc0 x hx) hu0

end EllipticPdes.Classical
