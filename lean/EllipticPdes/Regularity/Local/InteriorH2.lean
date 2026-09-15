/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Regularity.Local.Reduction
import EllipticPdes.Regularity.TestFnCut

/-!
# Interior `H²` estimate for a weak solution in `H¹`

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 1 (p. 327): for
`a^{ij} ∈ C¹(U)`, `b^i, c ∈ L^∞(U)`, `f ∈ L²(U)` and a weak solution `u ∈ H¹(U)` of `L u = f`,
`u ∈ H²_loc(U)` with `‖u‖_{H²(V)} ≤ C (‖f‖_{L²(U)} + ‖u‖_{L²(U)})` for `V ⋐ U`.

The statement here asks nothing of `u` at the boundary. It is read off the `H₀¹` estimate
`interior_H2_estimate` through the cutoff reduction: for `η` equal to `1` near `V` and supported
in `Ω`, the element `η U ∈ H₀¹(Ω)` solves an equation whose datum `redDatum` is bounded by
`K (‖f‖ + ‖U‖)` (`exists_norm_redDatum_le`), and the cutoff is invisible on `V`.

The right-hand side has the full `H¹(Ω)` norm `‖U‖` where Evans has `‖u‖_{L²(U)}`. Evans
removes the gradient with the Caccioppoli inequality (the display before (8) in the proof), which
is not ported to `W12` solutions here.

## Main declarations

* `exists_norm_redDatum_le`: the bound on the reduction datum.
* `interior_H2_estimate_W12`: Theorem 1 with `‖U‖_{H¹(Ω)}` on the right.
-/

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev EllipticPdes.Embedding EllipticPdes.Extension

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

theorem norm_double_sum_le {m : ℕ} (T : Fin m → Fin m → L2D Ω) (K : Fin m → Fin m → ℝ) (N : ℝ)
    (h : ∀ i j, ‖T i j‖ ≤ K i j * N) :
    ‖∑ i, ∑ j, T i j‖ ≤ (∑ i, ∑ j, K i j) * N := by
  calc ‖∑ i, ∑ j, T i j‖ ≤ ∑ i, ‖∑ j, T i j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖T i j‖ := Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, K i j * N :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = (∑ i, ∑ j, K i j) * N := by simp only [Finset.sum_mul]

theorem norm_single_sum_le {m : ℕ} (T : Fin m → L2D Ω) (K : Fin m → ℝ) (N : ℝ)
    (h : ∀ i, ‖T i‖ ≤ K i * N) :
    ‖∑ i, T i‖ ≤ (∑ i, K i) * N := by
  calc ‖∑ i, T i‖ ≤ ∑ i, ‖T i‖ := norm_sum_le _ _
    _ ≤ ∑ i, K i * N := Finset.sum_le_sum fun i _ => h i
    _ = (∑ i, K i) * N := by simp only [Finset.sum_mul]

theorem norm_six_le (a b c e g h : L2D Ω) :
    ‖a - b - c - e - g + h‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖e‖ + ‖g‖ + ‖h‖ := by
  have h1 := norm_add_le (a - b - c - e - g) h
  have h2 := norm_sub_le (a - b - c - e) g
  have h3 := norm_sub_le (a - b - c) e
  have h4 := norm_sub_le (a - b) c
  have h5 := norm_sub_le a b
  linarith

/-- **Bound on the reduction datum.** `‖F‖ ≤ K (‖f‖ + ‖U‖)`, with `K` depending on the
coefficients and the cutoff alone. -/
theorem exists_norm_redDatum_le (Op : FullEllipticOp d) (D : CoeffWeakGrad Op.toEllipticCoeff)
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U : H1amb Ω) (f : L2D Ω),
      ‖redDatum Op D hη U f‖ ≤ K * (‖f‖ + ‖U‖) := by
  classical
  set Mη : ℝ := (exists_abs_bound hη).choose
  have hMη : 0 ≤ Mη := le_trans (abs_nonneg _) ((exists_abs_bound hη).choose_spec 0)
  set K1 : Fin d → Fin d → ℝ := fun _ j => max Op.Λ 0 *
    ((hη.hasCompactSupport_partialD j).exists_bound_of_continuous
      (hη.continuous_partialD j)).choose
  set K2 : Fin d → Fin d → ℝ := fun i _ => max D.bound 0 *
    ((hη.hasCompactSupport_partialD i).exists_bound_of_continuous
      (hη.continuous_partialD i)).choose
  set K4 : Fin d → Fin d → ℝ := fun i j => max Op.Λ 0 *
    (((isTestFn_partialD hη i).hasCompactSupport_partialD j).exists_bound_of_continuous
      ((isTestFn_partialD hη i).continuous_partialD j)).choose
  set K5 : Fin d → ℝ := fun i => max Op.Bsup 0 *
    ((hη.hasCompactSupport_partialD i).exists_bound_of_continuous
      (hη.continuous_partialD i)).choose
  have hK1 : ∀ i j, 0 ≤ K1 i j := fun _ j => weightL_bound_nonneg
    (hη.continuous_partialD j) (hη.hasCompactSupport_partialD j)
  have hK2 : ∀ i j, 0 ≤ K2 i j := fun i _ => weightL_bound_nonneg
    (hη.continuous_partialD i) (hη.hasCompactSupport_partialD i)
  have hK4 : ∀ i j, 0 ≤ K4 i j := fun i j => weightL_bound_nonneg
    ((isTestFn_partialD hη i).continuous_partialD j)
    ((isTestFn_partialD hη i).hasCompactSupport_partialD j)
  have hK5 : ∀ i, 0 ≤ K5 i := fun i => weightL_bound_nonneg
    (hη.continuous_partialD i) (hη.hasCompactSupport_partialD i)
  set S1 := ∑ i, ∑ j, K1 i j
  set S2 := ∑ i, ∑ j, K2 i j
  set S4 := ∑ i, ∑ j, K4 i j
  set S5 := ∑ i, K5 i
  have hS1 : 0 ≤ S1 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hK1 i j
  have hS2 : 0 ≤ S2 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hK2 i j
  have hS4 : 0 ≤ S4 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hK4 i j
  have hS5 : 0 ≤ S5 := Finset.sum_nonneg fun i _ => hK5 i
  refine ⟨Mη + S1 + S2 + S1 + S4 + S5, by positivity, fun U f => ?_⟩
  have hUc : ∀ j, ‖U j‖ ≤ ‖U‖ := fun j => PiLp.norm_apply_le U j
  have t0 : ‖mulTest hη f‖ ≤ Mη * ‖f‖ := norm_mulTest_le hη f
  have t1 := norm_double_sum_le (fun i j => weightL Ω (Op.measurable i j) (Op.bdd i j)
      (hη.continuous_partialD j) (hη.hasCompactSupport_partialD j) (U i.succ)) K1 ‖U‖
    (fun i j => (norm_weightL_le _ _ _ _ _).trans
      (mul_le_mul_of_nonneg_left (hUc _) (hK1 i j)))
  have t2 := norm_double_sum_le (fun i j => weightL Ω (D.measurable j i j) (D.ae_abs_le j i j)
      (hη.continuous_partialD i) (hη.hasCompactSupport_partialD i) (U 0)) K2 ‖U‖
    (fun i j => (norm_weightL_le _ _ _ _ _).trans
      (mul_le_mul_of_nonneg_left (hUc _) (hK2 i j)))
  have t3 := norm_double_sum_le (fun i j => weightL Ω (Op.measurable i j) (Op.bdd i j)
      (hη.continuous_partialD i) (hη.hasCompactSupport_partialD i) (U j.succ))
      (fun i j => K1 j i) ‖U‖
    (fun i j => (norm_weightL_le _ _ _ _ _).trans
      (mul_le_mul_of_nonneg_left (hUc _) (hK1 j i)))
  have hS3 : (∑ i : Fin d, ∑ j : Fin d, K1 j i) = S1 := Finset.sum_comm
  have t4 := norm_double_sum_le (fun i j => weightL Ω (Op.measurable i j) (Op.bdd i j)
      ((isTestFn_partialD hη i).continuous_partialD j)
      ((isTestFn_partialD hη i).hasCompactSupport_partialD j) (U 0)) K4 ‖U‖
    (fun i j => (norm_weightL_le _ _ _ _ _).trans
      (mul_le_mul_of_nonneg_left (hUc _) (hK4 i j)))
  have t5 := norm_single_sum_le (fun i => weightL Ω (Op.b_meas i) (Op.b_bdd i)
      (hη.continuous_partialD i) (hη.hasCompactSupport_partialD i) (U 0)) K5 ‖U‖
    (fun i => (norm_weightL_le _ _ _ _ _).trans
      (mul_le_mul_of_nonneg_left (hUc _) (hK5 i)))
  rw [hS3] at t3
  have hf0 := norm_nonneg f
  have hU0 := norm_nonneg U
  rw [redDatum]
  refine (norm_six_le _ _ _ _ _ _).trans ?_
  simp only at t1 t2 t3 t4 t5
  nlinarith [t0, t1, t2, t3, t4, t5, mul_nonneg hMη hU0, mul_nonneg hS1 hf0,
    mul_nonneg hS2 hf0, mul_nonneg hS4 hf0, mul_nonneg hS5 hf0]

/-- The function coordinate of `η U` is `η U₀`. -/
theorem cutoffMul_zero_ae {η : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω η)
    (U : H1amb Ω) :
    ((cutoffMul hη U) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => η x * (U 0 x : ℝ) := by
  rw [cutoffMul_apply_zero]; exact mulTest_coeFn hη (U 0)

/-- The gradient coordinates of `η U` are `η U_{i+1} + ∂_i η U₀`. -/
theorem cutoffMul_succ_ae {η : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω η)
    (U : H1amb Ω) (i : Fin d) :
    ((cutoffMul hη U) i.succ : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => η x * (U i.succ x : ℝ) + partialD i η x * (U 0 x : ℝ) := by
  rw [cutoffMul_apply_succ]
  filter_upwards [Lp.coeFn_add (mulTest hη (U i.succ)) (mulTestPartial hη i (U 0)),
    mulTest_coeFn hη (U i.succ), mulTestPartial_coeFn hη i (U 0)] with x h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3]

/-- **Invisibility of the cutoff where it is one.** If `η = 1` near `V ⊆ Ω`, every coordinate of
`η U`, cut down to `V`, is the same coordinate of `U`. -/
theorem restrictL2_extendL2_cutoffMul {V : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    (hVm : MeasurableSet V) (hVΩ : V ⊆ Ω) {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hη : IsTestFn Ω η) (hη1 : ∀ᶠ x in 𝓝ˢ V, η x = 1) (U : H1amb Ω) (j : Fin (d + 1)) :
    restrictL2 (Ω := V) (extendL2 hΩm ((cutoffMul hη U) j))
      = restrictL2 (Ω := V) (extendL2 hΩm (U j)) := by
  apply Lp.ext
  have hcoord : ((cutoffMul hη U) j : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict V] (U j : EuclideanSpace ℝ (Fin d) → ℝ) := by
    refine Fin.cases ?_ (fun i => ?_) j
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset hVΩ (cutoffMul_zero_ae hη U),
        ae_restrict_mem hVm] with x h1 h2
      rw [h1, hη1.self_of_nhdsSet x h2, one_mul]
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset hVΩ (cutoffMul_succ_ae hη U i),
        ae_restrict_mem hVm] with x h1 h2
      rw [h1, hη1.self_of_nhdsSet x h2, partialD_eq_zero_of_eventually_one hη1 h2 i]
      ring
  filter_upwards [coeFn_restrictL2 (Ω := V) (extendL2 hΩm ((cutoffMul hη U) j)),
    coeFn_restrictL2 (Ω := V) (extendL2 hΩm (U j)),
    ae_restrict_of_ae (coeFn_extendL2 hΩm ((cutoffMul hη U) j)),
    ae_restrict_of_ae (coeFn_extendL2 hΩm (U j)), hcoord, ae_restrict_mem hVm]
    with x h1 h2 h3 h4 h5 h6
  rw [h1, h2, h3, h4, Set.indicator_of_mem (hVΩ h6), Set.indicator_of_mem (hVΩ h6), h5]

/-- **Interior `H²` estimate for a weak solution in `H¹(Ω)` (Evans, *Partial Differential
Equations* (2nd ed.), §6.3.1, Theorem 1, p. 327), with `‖U‖_{H¹(Ω)}` on the right.** For `C¹`
principal coefficients with a bounded derivative and a local weak solution `U ∈ W12 Ω` of
`L U = f`, with no boundary condition, each gradient coordinate of `U` has every weak first
derivative on a compact `V ⊆ Ω`, bounded by `C (‖f‖ + ‖U‖)` with `C` quantified before `U` and
`f`. -/
theorem interior_H2_estimate_W12 {n : ℕ} (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩo : IsOpen Ω)
    (hA : IsC1Coeff Op.toEllipticCoeff)
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hVc : IsCompact V) (hVΩ : V ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : H1amb Ω) (f : L2D Ω), IsLocalWeakSolution Op Ω U f →
      ∀ k i : Fin (n + 1), ∃ wki : Lp ℝ 2 (volume.restrict V),
        HasWeakDerivOn V k
            (restrictL2 (Ω := V) (extendL2 hΩo.measurableSet (U i.succ))) wki ∧
          ‖wki‖ ≤ C * (‖f‖ + ‖U‖) := by
  classical
  have hΩm : MeasurableSet Ω := hΩo.measurableSet
  have hVm : MeasurableSet V := hVc.isClosed.measurableSet
  obtain ⟨η, hη, hη1, -⟩ := exists_isTestFn_one_nhdsSet_of_isCompact hVc hΩo hVΩ
  obtain ⟨C, hC0, hC⟩ := interior_H2_estimate Op hΩm hΩo hA hVc hVΩ
  obtain ⟨K, hK0, hK⟩ := exists_norm_redDatum_le Op hA.coeffWeakGrad hη
  set Mη : ℝ := (exists_abs_bound hη).choose
  have hMη : 0 ≤ Mη := le_trans (abs_nonneg _) ((exists_abs_bound hη).choose_spec 0)
  refine ⟨C * (K + Mη), mul_nonneg hC0 (add_nonneg hK0 hMη), fun U f hsol k i => ?_⟩
  set W : H01 Ω := ⟨cutoffMul hη U, cutoffMul_mem_H01_of_mem_W12 hΩo hη hsol.1⟩ with hWdef
  obtain ⟨wki, hwd, hbd⟩ := hC W (redDatum Op hA.coeffWeakGrad hη U f)
    (reduction_weakForm Op hA.coeffWeakGrad hη hΩo hsol) k i
  have hid := restrictL2_extendL2_cutoffMul hΩm hVm hVΩ hη hη1 U i.succ
  refine ⟨wki, hid ▸ hwd, ?_⟩
  have hW0 : ‖(W : H1amb Ω) 0‖ ≤ Mη * ‖U‖ := by
    change ‖(cutoffMul hη U) 0‖ ≤ _
    rw [cutoffMul_apply_zero]
    exact (norm_mulTest_le hη _).trans
      (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le U 0) hMη)
  have hF := hK U f
  have h1 := norm_nonneg (restrictL2 (Ω := V) (extendL2 hΩm ((W : H1amb Ω) i.succ)))
  have h2 := norm_nonneg (restrictL2 (Ω := V) (extendL2 hΩm ((W : H1amb Ω) 0)))
  have hf0 := norm_nonneg f
  have hU0 := norm_nonneg U
  calc ‖wki‖ ≤ C * (‖redDatum Op hA.coeffWeakGrad hη U f‖ + ‖(W : H1amb Ω) 0‖) := by linarith
    _ ≤ C * (K * (‖f‖ + ‖U‖) + Mη * ‖U‖) :=
        mul_le_mul_of_nonneg_left (add_le_add hF hW0) hC0
    _ ≤ C * (K + Mη) * (‖f‖ + ‖U‖) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (by nlinarith) hC0

end EllipticPdes.Regularity
