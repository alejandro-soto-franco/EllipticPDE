/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.GagliardoNirenberg
public import EllipticPdes.Embedding.WeakDerivBridge

/-!
# Interior Hölder continuity of a weak solution

The interior `H²` estimate and the Morrey embedding are joined here, so that a weak solution of
`L u = f` is shown to have a Hölder continuous representative on a ball compactly contained in
the domain, with the Hölder constant controlled by `‖f‖ + ‖u‖`.

Three dimensions are covered, each with Hölder exponent `1/2`.

* `d = 1`. Morrey applies at `p = 2 > 1 = d` to the first-order weak gradient, so the
  first-order energy estimate alone suffices and the exponent is `1 - 1/2 = 1/2`.
* `d = 2`. The Sobolev conjugate of `2` degenerates at `d = 2`, so the bootstrap of
  `EllipticPdes.Embedding.GagliardoNirenberg` takes its step at `p = 4/3`, whose conjugate is
  `4`. The ball has finite measure, so the `L²` second derivatives of the interior `H²` estimate
  are `L^{4/3}` data, and Morrey applies at `p = 4 > 2 = d` with exponent `1 - 2/4 = 1/2`.
* `d = 3`. Morrey needs `p > 3`, and the interior `H²` estimate supplies second derivatives in
  `L²`. The bootstrap raises the gradient from `L²` to `L⁶`, and Morrey then applies at `p = 6 >
  3 = d` with exponent `1 - 3/6 = 1/2`.

For `d ≥ 4` one Sobolev step from the `L²` second derivatives does not reach Morrey. The
admissible exponents satisfy `d/2 < p ≤ 2`, since `1/p' = 1/p - 1/d` gives `p' > d` exactly when
`p > d/2` and the ball turns `L²` data into `Lᵖ` data only for `p ≤ 2`, and that range is empty
once `d ≥ 4`. The iterated ladder of `EllipticPdes.Embedding.exists_const_ladder` is what
covers those dimensions.

## Main declarations

* `interior_holder_estimate_one`: the one-dimensional statement.
* `interior_holder_estimate_of_conjugate`: the statement in dimension `n + 1` for one exponent
  pair `(p, P)` with `1/P = 1/p - 1/(n + 1)`, `p ≤ 2` and `P > n + 1`.
* `interior_holder_estimate_two`: the two-dimensional statement.
* `interior_holder_estimate`: the three-dimensional statement.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev EllipticPdes.Regularity

variable {d : ℕ}

/-! ### Restriction of a whole-space `L²` class to a ball -/

/-- The `L²` seminorm of a class against a smaller measure is at most the class norm. -/
theorem eLpNorm_le_enorm_of_le {α : Type*} {m : MeasurableSpace α} {μ ν : Measure α} (h : ν ≤ μ)
    (X : Lp ℝ 2 μ) : eLpNorm (X : α → ℝ) 2 ν ≤ ‖X‖ₑ := by
  rw [Lp.enorm_def]
  exact eLpNorm_mono_measure _ h

/-- The extension by zero of a class of norm at most `B` has `L²` seminorm at most `B` against
any restriction of the measure. -/
theorem eLpNorm_extendL2_le {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    (v : L2D Ω) {B : ℝ≥0} (h : ‖v‖ ≤ B) (S : Set (EuclideanSpace ℝ (Fin d))) :
    eLpNorm (extendL2 hΩm v : EuclideanSpace ℝ (Fin d) → ℝ) 2 (volume.restrict S) ≤ B :=
  (eLpNorm_le_enorm_of_le Measure.restrict_le_self _).trans
    (enorm_le_coe.mpr (by rwa [← NNReal.coe_le_coe, coe_nnnorm, norm_extendL2]))

/-- The extension by zero of an `H₀¹` class has the extensions of its components as weak
gradient on every set. -/
theorem hasWeakGradOn_extendL2 {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩm : MeasurableSet Ω) (u : H01 Ω) (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) :
    HasWeakGradOn B (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
      (fun k => (extendL2 hΩm ((u : H1amb Ω) k.succ) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)) :=
  (hasWeakGradOn_of_hasWeakDerivOn fun k =>
    hasWeakDerivOn_of_hasWeakDeriv k (hasWeakDeriv_extendL2_of_mem_H01 hΩm k u.2)).congr_ae
    (coeFn_restrictL2 _) (fun _ => coeFn_restrictL2 _)

/-- **Bound of the `L²` seminorm over a smaller set.** If the norm of the class is at most `B`
then its `L²` seminorm over any set below `T` is at most `B`. -/
theorem eLpNorm_restrict_le_of_norm_le {S T : Set (EuclideanSpace ℝ (Fin d))} (hST : S ⊆ T)
    {X : Lp ℝ 2 (volume.restrict T)} {B : ℝ≥0} (h : ‖X‖ ≤ B) :
    eLpNorm (X : EuclideanSpace ℝ (Fin d) → ℝ) 2 (volume.restrict S) ≤ B :=
  (eLpNorm_le_enorm_of_le (Measure.restrict_mono hST le_rfl) X).trans
    (enorm_le_coe.mpr (by rwa [← NNReal.coe_le_coe, coe_nnnorm]))

/-! ### One-dimensional estimate -/

/-- **Interior Hölder estimate in one dimension (Evans, *Partial Differential Equations*
(2nd ed.), §5.6.2 Thm 5).** A weak solution `u ∈ H₀¹(Ω)` of `L u = f` has, on every ball, a
representative that is Hölder continuous with exponent `1/2` and constant a multiple of
`‖f‖ + ‖u‖`, the multiplier being quantified before the solution and the datum, so it depends
only on the operator and the ball. In one dimension the first-order weak gradient already lies
in `L²` and `2 > 1`, so Morrey applies to it directly and only the first-order energy estimate
is used: neither the interior `H²` estimate nor any hypothesis on the geometry of `Ω` is
needed. -/
theorem interior_holder_estimate_one (Op : FullEllipticOp 1)
    {Ω : Set (EuclideanSpace ℝ (Fin 1))} (hΩm : MeasurableSet Ω)
    (c : EuclideanSpace ℝ (Fin 1)) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ≥0, ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∃ u' : EuclideanSpace ℝ (Fin 1) → ℝ,
        u' =ᵐ[volume.restrict (Metric.ball c r)]
            (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin 1) → ℝ) ∧
          HolderOnWith (C * Real.toNNReal (‖f‖ + ‖(u : H1amb Ω) 0‖)) (1 / 2 : ℝ≥0) u'
            (Metric.ball c r) := by
  have hd0 : (0 : ℝ) ≤ Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam)) := Real.sqrt_nonneg _
  obtain ⟨C₀, hC₀⟩ := morrey_ball (d := 1) one_pos (by norm_num : ((1 : ℕ) : ℝ) < 2) c hr
  refine ⟨C₀ * Real.toNNReal (Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam))),
    fun u f hu => ?_⟩
  obtain ⟨u', hu'ae, hHol⟩ := hC₀ _ _
    ((((Lp.memLp (extendL2 hΩm ((u : H1amb Ω) 0))).restrict _)).integrable (by norm_num))
    (fun k => by
      rw [show ENNReal.ofReal (2 : ℝ) = 2 by simp]
      exact (Lp.memLp (extendL2 hΩm ((u : H1amb Ω) k.succ))).restrict _)
    (hasWeakGradOn_extendL2 hΩm u (Metric.ball c r))
  refine ⟨u', hu'ae, ?_⟩
  have hγ : morreyExponent 1 2 = (1 / 2 : ℝ≥0) := by
    simpa using morreyExponent_two_mul (d := 1) one_pos
  rw [← hγ]
  refine hHol.mono_const ?_
  have hbd : ∀ k : Fin 1, eLpNorm (extendL2 hΩm ((u : H1amb Ω) k.succ) :
      EuclideanSpace ℝ (Fin 1) → ℝ) (ENNReal.ofReal 2) (volume.restrict (Metric.ball c r))
      ≤ ((Real.toNNReal (Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam)))
        * Real.toNNReal (‖f‖ + ‖(u : H1amb Ω) 0‖) : ℝ≥0) : ℝ≥0∞) := fun k => by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by simp]
    refine eLpNorm_extendL2_le hΩm _ ?_ _
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hd0, Real.coe_toNNReal _ (by positivity)]
    exact firstOrder_gradNorm_le Op u f hu k
  calc _ ≤ C₀ * (1 * (Real.toNNReal (Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam)))
          * Real.toNNReal (‖f‖ + ‖(u : H1amb Ω) 0‖))) := by
        simpa using mul_le_mul_right (sum_toNNReal_eLpNorm_le hbd) C₀
    _ = _ := by simp [mul_assoc]

/-! ### Estimate in dimension `n + 1` -/

/-- **Interior Hölder estimate in dimension `n + 1` at one exponent pair (Evans, *Partial
Differential Equations* (2nd ed.), §5.6.2 Thm 5, applied to the interior `H²` estimate of §6.3.1
Thm 1).** A weak solution `u ∈ H₀¹(Ω)` of `L u = f` with `W^{1,∞}` principal coefficients has, on
every ball `B(c, r)` with `r < R` and `closedBall c R ⊆ Ω`, a representative that is Hölder
continuous with exponent `1/2` and constant a multiple of `‖f‖ + ‖u‖`, the multiplier being
quantified before the solution and the datum. The interior `H²` estimate puts the second
derivatives in `L²`, hence in `Lᵖ` for `p ≤ 2` on the ball. One Sobolev step with
`1/P = 1/p - 1/(n + 1)` raises the gradient to `L^P`, and `morrey_ball` applies at `P > n + 1`
with the exponent `morreyExponent (n + 1) P = 1/2`. -/
theorem interior_holder_estimate_of_conjugate {n : ℕ} (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA : IsLipCoeff Op.toEllipticCoeff) (c : EuclideanSpace ℝ (Fin (n + 1))) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRΩ : Metric.closedBall c R ⊆ Ω) {p P : ℝ≥0} (hp : 1 ≤ p)
    (hp2 : p ≤ 2) (hPd : ((n + 1 : ℕ) : ℝ) < P)
    (hpP : (P : ℝ)⁻¹ = (p : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹)
    (hγ : morreyExponent (n + 1) (P : ℝ) = 1 / 2) :
    ∃ C : ℝ≥0, ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∃ u' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
        u' =ᵐ[volume.restrict (Metric.ball c r)]
            (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) ∧
          HolderOnWith (C * Real.toNNReal (‖f‖ + ‖(u : H1amb Ω) 0‖)) (1 / 2 : ℝ≥0) u'
            (Metric.ball c r) := by
  have hd0 : (0 : ℝ) ≤ Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam)) := Real.sqrt_nonneg _
  have hballV : Metric.ball c R ⊆ Metric.closedBall c R := Metric.ball_subset_closedBall
  obtain ⟨C₁, hC₁0, hC₁⟩ := interior_H2_estimate Op hΩm hΩo hA (isCompact_closedBall c R) hRΩ
  obtain ⟨K, hK⟩ := exists_eLpNorm_sobolevConj_le_of_le n.succ_pos c hp (q := 2)
    (by exact_mod_cast hp2) hpP hr hrR
  obtain ⟨C₀, hC₀⟩ := morrey_ball n.succ_pos hPd c hr
  set D : ℝ≥0 := Real.toNNReal (Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam)) + C₁) with hD
  refine ⟨C₀ * (((n + 1 : ℕ) : ℝ≥0) * (K * ((((n + 1 : ℕ) : ℝ≥0) + 1) * D))), fun u f hu => ?_⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = ‖f‖ + ‖(u : H1amb Ω) 0‖ := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by rw [hN]; exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  choose W hW hWb using hC₁ u f hu
  rw [← hN] at hWb
  -- Every `L²` seminorm over the outer ball is at most `D * N`.
  have hDN : ((D * N.toNNReal : ℝ≥0) : ℝ) = (Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam))
      + C₁) * N := by
    rw [NNReal.coe_mul, hD, Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ hN0]
  have hXb : ∀ i : Fin (n + 1), eLpNorm (extendL2 hΩm ((u : H1amb Ω) i.succ) :
      EuclideanSpace ℝ (Fin (n + 1)) → ℝ) 2 (volume.restrict (Metric.ball c R))
      ≤ ((D * N.toNNReal : ℝ≥0) : ℝ≥0∞) := fun i => by
    refine eLpNorm_extendL2_le hΩm _ ?_ _
    rw [hDN]
    have := firstOrder_gradNorm_le Op u f hu i
    rw [← hN] at this
    nlinarith
  have hWb' : ∀ k i : Fin (n + 1), eLpNorm (W k i : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) 2
      (volume.restrict (Metric.ball c R)) ≤ ((D * N.toNNReal : ℝ≥0) : ℝ≥0∞) := fun k i => by
    refine eLpNorm_restrict_le_of_norm_le hballV ?_
    rw [hDN]
    nlinarith [hWb k i, norm_nonneg (restrictL2 (Ω := Metric.closedBall c R)
      (extendL2 hΩm ((u : H1amb Ω) i.succ))), norm_nonneg (restrictL2 (Ω := Metric.closedBall c R)
      (extendL2 hΩm ((u : H1amb Ω) 0)))]
  have hrung : ∀ i : Fin (n + 1), MemLp (extendL2 hΩm ((u : H1amb Ω) i.succ) :
        EuclideanSpace ℝ (Fin (n + 1)) → ℝ) P (volume.restrict (Metric.ball c r)) ∧
      eLpNorm (extendL2 hΩm ((u : H1amb Ω) i.succ) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) P
        (volume.restrict (Metric.ball c r))
        ≤ ((K * ((((n + 1 : ℕ) : ℝ≥0) + 1) * (D * N.toNNReal)) : ℝ≥0) : ℝ≥0∞) := fun i => by
    obtain ⟨hmem, hbd⟩ := hK _ (fun k => (W k i : EuclideanSpace ℝ (Fin (n + 1)) → ℝ))
      ((Lp.memLp (extendL2 hΩm ((u : H1amb Ω) i.succ))).restrict _)
      (fun k => (Lp.memLp (W k i)).mono_measure (Measure.restrict_mono hballV le_rfl))
      (((hasWeakGradOn_of_hasWeakDerivOn fun k => hW k i).congr_ae (coeFn_restrictL2 _)
        (fun k => Filter.EventuallyEq.rfl)).mono hballV)
    refine ⟨by simpa using hmem, ?_⟩
    simpa using hbd.trans (mul_le_mul_right (add_sum_le_of_le (hXb i) fun k => hWb' k i) _)
  obtain ⟨u', hu'ae, hHol⟩ := hC₀ _ _
    ((Lp.memLp (extendL2 hΩm ((u : H1amb Ω) 0))).restrict _ |>.integrable (by norm_num))
    (fun i => by rw [ENNReal.ofReal_coe_nnreal]; exact (hrung i).1)
    (hasWeakGradOn_extendL2 hΩm u _)
  refine ⟨u', hu'ae, ?_⟩
  rw [← hN, ← hγ]
  refine hHol.mono_const ?_
  calc _ ≤ C₀ * (((n + 1 : ℕ) : ℝ≥0) * (K * ((((n + 1 : ℕ) : ℝ≥0) + 1) * (D * N.toNNReal)))) :=
        mul_le_mul_right (sum_toNNReal_eLpNorm_le fun i => by
          rw [ENNReal.ofReal_coe_nnreal]; exact (hrung i).2) _
    _ = _ := by ring

/-! ### Two and three dimensions -/

/-- **Interior Hölder estimate in two dimensions (Evans, *Partial Differential Equations*
(2nd ed.), §5.6.2 Thm 5, applied to the interior `H²` estimate of §6.3.1 Thm 1).** On every ball
`B(c, r)` with `r < R` and `closedBall c R ⊆ Ω`, a weak solution has a representative that is
Hölder continuous with exponent `1/2`, with a multiplier quantified before the solution. At
`d = 2` the Sobolev conjugate of `2` degenerates, so the step is taken at `p = 4/3` and raises the
gradient from `L²` to `L⁴`; `morrey_ball` then applies at `p = 4 > 2 = d`. -/
theorem interior_holder_estimate_two (Op : FullEllipticOp 2)
    {Ω : Set (EuclideanSpace ℝ (Fin 2))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA : IsLipCoeff Op.toEllipticCoeff)
    (c : EuclideanSpace ℝ (Fin 2)) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hRΩ : Metric.closedBall c R ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∃ u' : EuclideanSpace ℝ (Fin 2) → ℝ,
        u' =ᵐ[volume.restrict (Metric.ball c r)]
            (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin 2) → ℝ) ∧
          HolderOnWith (C * Real.toNNReal (‖f‖ + ‖(u : H1amb Ω) 0‖)) (1 / 2 : ℝ≥0) u'
            (Metric.ball c r) :=
  interior_holder_estimate_of_conjugate (n := 1) Op hΩm hΩo hA c hr hrR hRΩ (p := 4 / 3) (P := 4)
    (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    (by rw [← NNReal.coe_le_coe]; push_cast; norm_num) (by push_cast; norm_num)
    (by push_cast; norm_num)
    (by
      rw [show (((4 : ℝ≥0)) : ℝ) = 2 * ((1 + 1 : ℕ) : ℝ) by norm_num]
      exact morreyExponent_two_mul (by norm_num))

/-- **Interior Hölder estimate in three dimensions (Evans, *Partial Differential Equations*
(2nd ed.), §5.6.2 Thm 5, applied to the interior `H²` estimate of §6.3.1 Thm 1).** A weak
solution `u ∈ H₀¹(Ω)` of `L u = f` with `W^{1,∞}` principal coefficients has, on every ball
`B(c, r)` with `r < R` and `closedBall c R ⊆ Ω`, a representative that is Hölder continuous with
exponent `1/2` and constant a multiple of `‖f‖ + ‖u‖`, the multiplier being quantified before
the solution and the datum, so it depends only on the operator and the two radii. The interior
`H²` estimate puts the second derivatives in `L²`, the Gagliardo-Nirenberg-Sobolev step raises
the gradient from `L²` to `L⁶`, and `morrey_ball` applies at `p = 6 > 3 = d`, so the weak
solution is classically differentiable in the Hölder sense. -/
theorem interior_holder_estimate (Op : FullEllipticOp 3)
    {Ω : Set (EuclideanSpace ℝ (Fin 3))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA : IsLipCoeff Op.toEllipticCoeff)
    (c : EuclideanSpace ℝ (Fin 3)) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hRΩ : Metric.closedBall c R ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∃ u' : EuclideanSpace ℝ (Fin 3) → ℝ,
        u' =ᵐ[volume.restrict (Metric.ball c r)]
            (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin 3) → ℝ) ∧
          HolderOnWith (C * Real.toNNReal (‖f‖ + ‖(u : H1amb Ω) 0‖)) (1 / 2 : ℝ≥0) u'
            (Metric.ball c r) :=
  interior_holder_estimate_of_conjugate (n := 2) Op hΩm hΩo hA c hr hrR hRΩ (p := 2) (P := 6)
    (by norm_num) le_rfl (by push_cast; norm_num) (by push_cast; norm_num)
    (by
      rw [show (((6 : ℝ≥0)) : ℝ) = 2 * ((2 + 1 : ℕ) : ℝ) by norm_num]
      exact morreyExponent_two_mul (by norm_num))

end EllipticPdes.Embedding

