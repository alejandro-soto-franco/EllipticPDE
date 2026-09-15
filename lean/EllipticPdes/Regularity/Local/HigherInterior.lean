/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Regularity.Local.Datum
import EllipticPdes.Regularity.HigherInterior

/-!
# Higher interior regularity for a weak solution in `H¹`

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2 (p. 332): for
`a^{ij}, b^i, c ∈ C^{m+1}(U)`, `f ∈ H^m(U)` and a weak solution `u ∈ H¹(U)` of `L u = f`,
`u ∈ H^{m+2}_loc(U)` with `‖u‖_{H^{m+2}(V)} ≤ C (‖f‖_{H^m(U)} + ‖u‖_{L²(U)})` for `V ⋐ U`.

The statement here is for a local weak solution `U ∈ W12 Ω` with no boundary condition. It is
read off `higher_interior_regularity`, stated for `H₀¹` solutions, through the cutoff reduction,
by induction on the order.

* Order `k` at `V`. Take `η = 1` near `V`, supported in `Ω`. `η U ∈ H₀¹(Ω)` solves an equation
  whose datum pairs `f` and the coordinates of `U` against weights supported in `tsupport η`
  (`reduction_testFn`). If every coordinate of `U` has `k` weak derivatives on `tsupport η`, the
  datum has `k` weak derivatives on `Ω` (`exists_reductionDatum`), the `H₀¹` theorem at order
  `k` gives `η U₀` in `H^{k+2}(V)`, and `η = 1` on `V`
  (`restrictL2_extendL2_cutoffMul`) makes that `U₀`.
* The hypothesis at order `k + 1` on a compact `W` is the conclusion at order `k` on
  `tsupport θ` for `θ = 1` near `W`: `U₀` has `k + 2` weak derivatives there, and on `W` the
  first of them are the gradient coordinates of `U` by uniqueness of the weak derivative after
  the cutoff `θ` (`exists_collarFamily_of_weakDerivOn`). At order `0` the hypothesis asks
  nothing.

The bound has `‖U‖_{H¹(Ω)}` where Evans has `‖u‖_{L²(U)}`, as in `interior_H2_estimate_W12`.

## Main declarations

* `LocalRegularityAt`: the order-`k` conclusion for local weak solutions.
* `LocalFamiliesAt`: the order-`k` hypothesis on the coordinates of the solution.
* `localRegularityAt_of_localFamiliesAt`, `localFamiliesAt_zero`, `localFamiliesAt_succ`.
* `higher_interior_regularity_W12`: the theorem.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {n : ℕ}

/-- **Order-`k` interior conclusion for local weak solutions.** For every compact `V ⊆ Ω` there
is a constant, quantified before the solution and the datum, bounding every weak derivative of
`U₀` of order at most `k + 2` on `V` by `M + ‖U‖`, for a datum with `k` weak derivatives
bounded by `M`. -/
def LocalRegularityAt (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (k : ℕ) : Prop :=
  ∀ {V : Set (EuclideanSpace ℝ (Fin (n + 1)))}, IsCompact V → V ⊆ Ω →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : H1amb Ω) (f : L2D Ω) (M : ℝ)
      (hfk : HasIteratedWeakDerivOn Ω k f), IteratedL2Bound hfk M →
      IsLocalWeakSolution Op Ω U f →
      ∃ hu : HasIteratedWeakDerivOn V (k + 2) (restrictL2 (Ω := V) (extendL2 hΩm (U 0))),
        IteratedL2Bound hu (C * (M + ‖U‖))

/-- **Order-`k` hypothesis on the coordinates.** For every compact `W ⊆ Ω` every coordinate of
a local weak solution, the function and its gradient alike, has `k` weak derivatives on `W`,
bounded by `M + ‖U‖` with a constant quantified before the solution and the datum. -/
def LocalFamiliesAt (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (k : ℕ) : Prop :=
  ∀ {W : Set (EuclideanSpace ℝ (Fin (n + 1)))}, IsCompact W → W ⊆ Ω →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : H1amb Ω) (f : L2D Ω) (M : ℝ)
      (hfk : HasIteratedWeakDerivOn Ω k f), IteratedL2Bound hfk M →
      IsLocalWeakSolution Op Ω U f →
      ∀ j : Fin (n + 2),
        ∃ H : HasIteratedWeakDerivOn W k (restrictL2 (Ω := W) (extendL2 hΩm (U j))),
          IteratedL2Bound H (C * (M + ‖U‖))

/-- At order zero the hypothesis on the coordinates asks only for their `L²` norms, which
`‖U‖` bounds. -/
theorem localFamiliesAt_zero (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) :
    LocalFamiliesAt Op hΩm 0 := by
  intro W _ _
  refine ⟨1, zero_le_one, fun U f M hfk hM _ j => ⟨HasIteratedWeakDerivOn.zero _, ?_⟩⟩
  intro α _
  have hM0 : 0 ≤ M := le_trans (norm_nonneg f) hM.norm_le
  change ‖restrictL2 (Ω := W) (extendL2 hΩm (U j))‖ ≤ _
  calc ‖restrictL2 (Ω := W) (extendL2 hΩm (U j))‖ ≤ ‖extendL2 hΩm (U j)‖ :=
        norm_restrictL2_le _
    _ = ‖U j‖ := norm_extendL2 hΩm _
    _ ≤ ‖U‖ := PiLp.norm_apply_le U j
    _ ≤ 1 * (M + ‖U‖) := by linarith

/-- **Hypothesis at `k + 1` from the conclusion at `k`.** For a compact `W`, the conclusion at
order `k` on `tsupport θ`, with `θ = 1` near `W`, gives `U₀` its `k + 2` weak derivatives on
`W`, whose first entries are the gradient coordinates of `U` by
`exists_collarFamily_of_weakDerivOn`. Each coordinate then has `k + 1`. -/
theorem localFamiliesAt_succ (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    {k : ℕ} (hk : LocalRegularityAt Op hΩm k) :
    LocalFamiliesAt Op hΩm (k + 1) := by
  classical
  intro W hWc hWΩ
  obtain ⟨θ, hθ, hθ1, -⟩ := exists_isTestFn_one_nhdsSet_of_isCompact hWc hΩo hWΩ
  have hθN : Set.EqOn θ 1 W := fun x hx => hθ1.self_of_nhdsSet x hx
  have hWT : W ⊆ tsupport θ := fun x hx =>
    subset_tsupport _ (by rw [Function.mem_support, hθN hx]; exact one_ne_zero)
  have hTm : MeasurableSet (tsupport θ) := (isClosed_tsupport θ).measurableSet
  have hWm : MeasurableSet W := hWc.isClosed.measurableSet
  have hθT : IsTestFn (tsupport θ) θ := ⟨hθ.1, hθ.2.1, subset_rfl⟩
  obtain ⟨C, hC0, hC⟩ := hk hθ.2.1 hθ.2.2
  refine ⟨C, hC0, fun U f M hfk hM hsol j => ?_⟩
  obtain ⟨HuT, hHuT⟩ :=
    hC U f M (hfk.mono (Nat.le_succ k)) (hM.mono_order (Nat.le_succ k)) hsol
  have hDT : ∀ i : Fin (n + 1), HasWeakDerivOn (tsupport θ) i
      (restrictL2 (Ω := tsupport θ) (extendL2 hΩm (U 0)))
      (restrictL2 (Ω := tsupport θ) (extendL2 hΩm (U i.succ))) := fun i =>
    (hasWeakDerivOn_of_mem_W12 hsol.1 i).restrict hΩm hTm hθ.2.2
  obtain ⟨HuW, hHuW, hDW⟩ := exists_collarFamily_of_weakDerivOn (Dg := fun i => U i.succ)
    hΩm hTm hWm hWT hθT hθN hDT (m := k + 1) HuT hHuT
  refine Fin.cases ?_ (fun i => ?_) j
  · exact ⟨HuW.mono (Nat.le_succ _), hHuW.mono_order (Nat.le_succ _)⟩
  · exact ⟨(HuW.deriv i).congr (hDW i), (hHuW.deriv i).congr⟩

/-- **Conclusion at order `k` from the hypothesis at order `k`.** The step that reads the
`H₀¹` theorem `higher_interior_regularity` off the cutoff reduction: for `η = 1` near `V`, the
datum of `η U` has `k` weak derivatives once the coordinates of `U` have them on `tsupport η`,
and the conclusion for `η U` on `V` is the conclusion for `U`. -/
theorem localRegularityAt_of_localFamiliesAt (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsC1Coeff Op.toEllipticCoeff) {k : ℕ}
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 3)) (hbc : IsWkInftyLower Op (k + 2))
    (hfam : LocalFamiliesAt Op hΩm k) :
    LocalRegularityAt Op hΩm k := by
  classical
  intro V hVc hVΩ
  have hVm : MeasurableSet V := hVc.isClosed.measurableSet
  obtain ⟨η, hη, hη1, -⟩ := exists_isTestFn_one_nhdsSet_of_isCompact hVc hΩo hVΩ
  have hWm : MeasurableSet (tsupport η) := (isClosed_tsupport η).measurableSet
  have hηW : IsTestFn (tsupport η) η := ⟨hη.1, hη.2.1, subset_rfl⟩
  have hA' : IsWkInftyCoeff Op.toEllipticCoeff (k + 1) := hA.mono (by omega)
  obtain ⟨CW, hCW0, hW⟩ := hfam hη.2.1 hη.2.2
  obtain ⟨K, hK0, hDat⟩ :=
    exists_reductionDatum Op hΩm hWm hη.2.2 hA' (hbc.mono (by omega)) hηW
  obtain ⟨CV, hCV0, hH01⟩ := higher_interior_regularity Op hΩm hΩo hA1 k hA hbc hVc hVΩ
  obtain ⟨Mη, hMη⟩ := exists_abs_bound hη
  have hMη0 : 0 ≤ Mη := le_trans (abs_nonneg _) (hMη 0)
  refine ⟨CV * (K * (CW + 1) + Mη),
    mul_nonneg hCV0 (add_nonneg (mul_nonneg hK0 (by linarith)) hMη0),
    fun U f M hfk hM hsol => ?_⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg f) hM.norm_le
  have hU0 : 0 ≤ ‖U‖ := norm_nonneg U
  have hMU : 0 ≤ M + ‖U‖ := add_nonneg hM0 hU0
  set B : ℝ := (CW + 1) * (M + ‖U‖) with hB
  choose H hH using hW U f M hfk hM hsol
  obtain ⟨F, HF, hFbd, hFpair⟩ := hDat U f H hfk B
    (fun j => (hH j).mono_const (by rw [hB]; nlinarith))
    (hM.mono_const (by rw [hB]; nlinarith))
  have hweak : ∀ w : H01 Ω,
      Op.fullBilin Ω ⟨cutoffMul hη U, cutoffMul_mem_H01_of_mem_W12 hΩo hη hsol.1⟩ w
        = ∫ x in Ω, (F x : ℝ) * ((w : H1amb Ω) 0 x : ℝ) := by
    refine weakForm_of_testFn Op _ F (fun v hv => ?_)
    rw [reduction_testFn Op hΩo hA'.coeffWeakGrad hsol hη hv, hFpair v hv.1 hv.2.1]
  obtain ⟨hu, hub⟩ := hH01 ⟨cutoffMul hη U, cutoffMul_mem_H01_of_mem_W12 hΩo hη hsol.1⟩ F
    (K * B) HF hFbd hweak
  refine ⟨hu.congr (restrictL2_extendL2_cutoffMul hΩm hVm hVΩ hη hη1 U 0), ?_⟩
  refine hub.congr.mono_const ?_
  have hη0 : ‖(cutoffMul hη U) 0‖ ≤ Mη * ‖U‖ := by
    rw [cutoffMul_apply_zero]
    exact le_trans (norm_le_of_ae_mul hη.continuous.measurable (Eventually.of_forall hMη)
        (mulTest_coeFn hη (U 0)))
      (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le U 0) hMη0)
  change CV * (K * B + ‖(cutoffMul hη U) 0‖) ≤ _
  have h1 : K * B + ‖(cutoffMul hη U) 0‖ ≤ (K * (CW + 1) + Mη) * (M + ‖U‖) := by
    rw [hB]
    nlinarith [mul_nonneg hMη0 hM0]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 hCV0

/-- **Higher interior regularity for a weak solution in `H¹` (Evans, *Partial Differential
Equations* (2nd ed.), §6.3.1, Theorem 2, p. 332).** A local weak solution `U ∈ W12 Ω` of
`L U = f`, with no boundary condition, `W^{k+3,∞}` principal coefficients, `W^{k+2,∞}`
lower-order coefficients and a datum with `k` weak derivatives bounded by `M`, has weak
derivatives of every order up to `k + 2` on each compact `V ⊆ Ω`, bounded by `C (M + ‖U‖)`
with `C` quantified before the solution and the datum. -/
theorem higher_interior_regularity_W12 (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsC1Coeff Op.toEllipticCoeff) (k : ℕ)
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 3))
    (hbc : IsWkInftyLower Op (k + 2)) :
    LocalRegularityAt Op hΩm k := by
  induction k with
  | zero =>
    exact localRegularityAt_of_localFamiliesAt Op hΩm hΩo hA1 hA hbc
      (localFamiliesAt_zero Op hΩm)
  | succ j ih =>
    exact localRegularityAt_of_localFamiliesAt Op hΩm hΩo hA1 hA hbc
      (localFamiliesAt_succ Op hΩm hΩo (ih (hA.mono (by omega)) (hbc.mono (by omega))))

end EllipticPdes.Regularity
