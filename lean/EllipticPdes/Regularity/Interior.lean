/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Regularity.Interior.NormBound

/-!
# The interior H² estimate

The capstone of the interior regularity chain. Section D4 passes to the limit in the uniform
difference-quotient bound of `EllipticPdes.Regularity.Interior.NormBound` to produce the
second weak derivative, and §4 assembles the coordinates into the interior H² estimate.

This module keeps the import path `EllipticPdes.Regularity.Interior` and re-exports the whole
chain, so dependents see the same API as before the file was split.

## Main declarations

* `interior_secondWeakDeriv`: existence of the interior second weak derivative.
* `HasWeakDerivOn`: the region-restricted weak derivative.
* `interior_H2_estimate`: the interior H² estimate.
-/

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### D4: existence of the second weak derivative -/

/-- **Existence of the interior second weak derivative (Evans §6.3.1, VIII.2.1).** For each
`(k, i)`, the whole-space extension of `ζ · ∂ᵢu` has an `L²` weak `k`-derivative `w`, bounded
by the data: this is the weak-limit converse `weakDeriv_of_diffQuot_bounded` fed with the
uniform difference-quotient bound `interior_diffQuot_norm_bound`. Because `ζ ≡ 1` on `V`, the
restriction of `w` to `V` is the genuine `∂ₖ∂ᵢu` there. -/
theorem interior_secondWeakDeriv (Op : FullEllipticOp d) (hΩm : MeasurableSet Ω)
    (hA : IsC1Coeff Op.toEllipticCoeff)
    (hb0 : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc0 : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x)
    {V : Set (EuclideanSpace ℝ (Fin d))} (T : CutoffTower Ω V)
    (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) (k i : Fin d) :
    ∃ w : EucL2 d,
      HasWeakDeriv k (extendL2 hΩm (mulTest T.hζ ((u : H1amb Ω) i.succ))) w
      ∧ ∃ Cd : ℝ, ‖w‖ ≤ Cd * (‖f‖ + ‖(u : H1amb Ω) 0‖) := by
  obtain ⟨M, _hM0, hMbd, Cd, hMCd⟩ :=
    interior_diffQuot_norm_bound Op hΩm hA hb0 hc0 T u f hu k i
  obtain ⟨w, hw, hwn⟩ :=
    weakDeriv_of_diffQuot_bounded k (extendL2 hΩm (mulTest T.hζ ((u : H1amb Ω) i.succ))) M hMbd
  exact ⟨w, hw, Cd, le_trans hwn hMCd⟩

/-! ### §4: the interior H² estimate -/

/-- **Weak derivative on an open region.** `g'` is the weak `k`-derivative of `g` on `V` if
integration by parts holds against every test function supported in `V`. This is the
`V`-restricted analogue of `HasWeakDeriv`, and is the `L²`-level statement of `∂ₖ g = g'` on
`V`. -/
def HasWeakDerivOn (V : Set (EuclideanSpace ℝ (Fin d))) (k : Fin d)
    (g g' : Lp ℝ 2 (volume.restrict V)) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ V →
    ∫ x in V, (g x : ℝ) * partialD k φ x = - ∫ x in V, (g' x : ℝ) * φ x

/-- A whole-space weak derivative restricts to a weak derivative on any measurable `V`: test
functions supported in `V` see only the restricted classes, and the whole-space
integration-by-parts identity localises because both integrands vanish off `V`. -/
theorem hasWeakDerivOn_of_hasWeakDeriv {V : Set (EuclideanSpace ℝ (Fin d))}
    (k : Fin d) {g w : EucL2 d} (h : HasWeakDeriv k g w) :
    HasWeakDerivOn V k (restrictL2 g) (restrictL2 w) := by
  intro φ hφc hφcs hφV
  have hzero_dk : ∀ x ∉ V, (g x : ℝ) * partialD k φ x = 0 := by
    intro x hx
    rw [show partialD k φ x = 0 from image_eq_zero_of_notMem_tsupport
      (fun hc => hx (hφV (tsupport_partialD_subset k φ hc))), mul_zero]
  have hzero_phi : ∀ x ∉ V, (w x : ℝ) * φ x = 0 := by
    intro x hx
    rw [show φ x = 0 from image_eq_zero_of_notMem_tsupport (fun hc => hx (hφV hc)), mul_zero]
  calc ∫ x in V, (restrictL2 g x : ℝ) * partialD k φ x
      = ∫ x in V, (g x : ℝ) * partialD k φ x := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_restrictL2 g] with x hx; rw [hx]
    _ = ∫ x, (g x : ℝ) * partialD k φ x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero hzero_dk
    _ = - ∫ x, (w x : ℝ) * φ x := h φ hφc hφcs
    _ = - ∫ x in V, (w x : ℝ) * φ x := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero_phi]
    _ = - ∫ x in V, (restrictL2 w x : ℝ) * φ x := by
        refine congrArg Neg.neg (integral_congr_ae ?_)
        filter_upwards [coeFn_restrictL2 w] with x hx; rw [hx]

/-- **First-order gradient bound.** Each gradient component of a weak solution with vanishing
transport and nonnegative zeroth-order coefficient is bounded in `L²` by the data:
`‖∂ᵢu‖ ≤ (1 / (2 √λ)) (‖f‖ + ‖u₀‖)`. This is the first-order energy estimate
`firstOrder_energy_le` combined with the arithmetic-geometric mean inequality. -/
private lemma firstOrder_gradNorm_le (Op : FullEllipticOp d)
    (hb0 : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc0 : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x) (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) (i : Fin d) :
    ‖(u : H1amb Ω) i.succ‖
      ≤ 1 / (2 * Real.sqrt Op.lam) * (‖f‖ + ‖(u : H1amb Ω) 0‖) := by
  have hlam : (0 : ℝ) < Op.lam := Op.toEllipticCoeff.lam_pos
  set P : ℝ := ‖f‖ + ‖(u : H1amb Ω) 0‖ with hPdef
  have hfo : Op.lam * ∑ j : Fin d, ‖(u : H1amb Ω) j.succ‖ ^ 2 ≤ ‖f‖ * ‖(u : H1amb Ω) 0‖ :=
    firstOrder_energy_le Op hb0 hc0 u f hu
  have hdisqm : ‖(u : H1amb Ω) i.succ‖ ^ 2 * Op.lam ≤ ‖f‖ * ‖(u : H1amb Ω) 0‖ := by
    have hle : ‖(u : H1amb Ω) i.succ‖ ^ 2 ≤ ∑ j : Fin d, ‖(u : H1amb Ω) j.succ‖ ^ 2 :=
      single_le_sum_fin (fun j => ‖(u : H1amb Ω) j.succ‖ ^ 2) (fun j => sq_nonneg _) i
    nlinarith only [mul_le_mul_of_nonneg_left hle hlam.le, hfo]
  have hamgm : ‖f‖ * ‖(u : H1amb Ω) 0‖ ≤ P ^ 2 / 4 := by
    rw [hPdef]; nlinarith only [sq_nonneg (‖f‖ - ‖(u : H1amb Ω) 0‖)]
  have hdiP : ‖(u : H1amb Ω) i.succ‖ ^ 2 ≤ P ^ 2 / (4 * Op.lam) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * Op.lam)]
    nlinarith only [hdisqm, hamgm]
  have hsq : (1 / (2 * Real.sqrt Op.lam) * P) ^ 2 = P ^ 2 / (4 * Op.lam) := by
    rw [mul_pow, div_pow, one_pow, mul_pow, Real.sq_sqrt hlam.le]; ring
  have hval : Real.sqrt (P ^ 2 / (4 * Op.lam)) = 1 / (2 * Real.sqrt Op.lam) * P := by
    rw [← hsq]; exact Real.sqrt_sq (by positivity)
  rw [show ‖(u : H1amb Ω) i.succ‖ = Real.sqrt (‖(u : H1amb Ω) i.succ‖ ^ 2) from
    (Real.sqrt_sq (norm_nonneg _)).symm, ← hval]
  exact Real.sqrt_le_sqrt hdiP

set_option maxHeartbeats 400000 in
-- The final assembly loops the per-`(k, i)` localised second-derivative statement over the
-- finite index square and threads the cutoff-tower construction, whose elaboration (unfolding
-- the tower definition and the difference-quotient bounds) exceeds the default budget.
/-- **Interior H² estimate (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1;
Gilbarg-Trudinger, *Elliptic Partial Differential Equations of Second Order*, Theorem 8.8).**
For a concrete-model weak solution `u ∈ H₀¹(Ω)` of `L u = f` with `C¹` principal coefficients,
vanishing transport, and nonnegative zeroth-order coefficient, and for any compact `V ⋐ Ω`,
the second weak derivatives exist in `L²(V)` and are bounded by the data: for every direction
pair `(k, i)` there is a weak `k`-derivative `wki` of `∂ᵢu` on `V` (that is, `∂ₖ∂ᵢu ∈ L²(V)`)
with `‖∂ₖ∂ᵢu‖_{L²(V)} + ‖∂ᵢu‖_{L²(V)} + ‖u‖_{L²(V)} ≤ C (‖f‖ + ‖u‖)`, the constant `C`
depending only on the data (`λ, Λ, A₁, d`, the cutoff tower for `V ⋐ Ω`), not on `∇u`. This is
the `L²`-level statement that `u ∈ H²_loc(Ω)` with the interior estimate. -/
theorem interior_H2_estimate {n : ℕ} (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA : IsC1Coeff Op.toEllipticCoeff)
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x)
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hVc : IsCompact V) (hVΩ : V ⊆ Ω)
    (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k i : Fin (n + 1),
      ∃ wki : Lp ℝ 2 (volume.restrict V),
        HasWeakDerivOn V k
            (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))) wki ∧
          ‖wki‖
            + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))‖
            + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))‖
          ≤ C * (‖f‖ + ‖(u : H1amb Ω) 0‖) := by
  classical
  have hVm : MeasurableSet V := hVc.isClosed.measurableSet
  set T := cutoffTowerOfIsCompactSubsetIsOpen hVc hΩo hVΩ with hT
  set P : ℝ := ‖f‖ + ‖(u : H1amb Ω) 0‖ with hPdef
  have hP0 : (0 : ℝ) ≤ P := by rw [hPdef]; positivity
  set dcoef : ℝ := 1 / (2 * Real.sqrt Op.lam) with hdcoefdef
  have hdcoef0 : (0 : ℝ) ≤ dcoef := by rw [hdcoefdef]; positivity
  have hdiu : ∀ i : Fin (n + 1), ‖(u : H1amb Ω) i.succ‖ ≤ dcoef * P := fun i =>
    firstOrder_gradNorm_le Op hb hc u f hu i
  -- Per-`(k, i)` localised statement with a data-only growth constant. The `V`-restriction of
  -- the cutoff class `ζ · ∂ᵢu` coincides with that of `∂ᵢu`, because `ζ ≡ 1` on `V`.
  have hstep : ∀ k i : Fin (n + 1), ∃ G : ℝ, ∃ wki : Lp ℝ 2 (volume.restrict V),
      HasWeakDerivOn V k (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))) wki ∧
      ‖wki‖ + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))‖
          + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))‖ ≤ G * P := by
    intro k i
    obtain ⟨w, hw, Cd, hwCd⟩ := interior_secondWeakDeriv Op hΩm hA hb hc T u f hu k i
    have hAB : (extendL2 hΩm (mulTest T.hζ ((u : H1amb Ω) i.succ))
          : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
        =ᵐ[volume.restrict V]
        (extendL2 hΩm ((u : H1amb Ω) i.succ) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) := by
      have hmt : (mulTest T.hζ ((u : H1amb Ω) i.succ)
            : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
          =ᵐ[volume.restrict V] fun x => T.ζ x * ((u : H1amb Ω) i.succ x : ℝ) :=
        (mulTest_coeFn T.hζ ((u : H1amb Ω) i.succ)).filter_mono
          (ae_mono (Measure.restrict_mono hVΩ le_rfl))
      filter_upwards [ae_restrict_of_ae
          (coeFn_extendL2 hΩm (mulTest T.hζ ((u : H1amb Ω) i.succ))),
        ae_restrict_of_ae (coeFn_extendL2 hΩm ((u : H1amb Ω) i.succ)), hmt,
        ae_restrict_mem hVm] with x he1 he2 hmtx hxV
      rw [he1, he2, Set.indicator_of_mem (hVΩ hxV), Set.indicator_of_mem (hVΩ hxV), hmtx]
      simp [T.zeta_eqOn_one hxV]
    have hDiuEq : restrictL2 (Ω := V) (extendL2 hΩm (mulTest T.hζ ((u : H1amb Ω) i.succ)))
        = restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ)) := by
      apply Lp.ext
      filter_upwards [coeFn_restrictL2 (Ω := V)
          (extendL2 hΩm (mulTest T.hζ ((u : H1amb Ω) i.succ))),
        coeFn_restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ)), hAB] with x h1 h2 h3
      rw [h1, h2, h3]
    refine ⟨Cd + dcoef + 1, restrictL2 w, ?_, ?_⟩
    · rw [← hDiuEq]; exact hasWeakDerivOn_of_hasWeakDeriv k hw
    · have h1 : ‖restrictL2 (Ω := V) w‖ ≤ Cd * P := le_trans (norm_restrictL2_le w) hwCd
      have h2 : ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))‖ ≤ dcoef * P := by
        refine le_trans (norm_restrictL2_le _) ?_
        rw [norm_extendL2]; exact hdiu i
      have h3 : ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))‖ ≤ 1 * P := by
        refine le_trans (norm_restrictL2_le _) ?_
        rw [norm_extendL2, one_mul, hPdef]
        linarith only [norm_nonneg f]
      calc ‖restrictL2 (Ω := V) w‖ + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))‖
              + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))‖
          ≤ Cd * P + dcoef * P + 1 * P := add_le_add (add_le_add h1 h2) h3
        _ = (Cd + dcoef + 1) * P := by ring
  choose G wki hHWD hbound using hstep
  refine ⟨∑ k : Fin (n + 1), ∑ i : Fin (n + 1), |G k i|,
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)), ?_⟩
  intro k i
  refine ⟨wki k i, hHWD k i, le_trans (hbound k i) ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ hP0
  calc G k i ≤ |G k i| := le_abs_self _
    _ ≤ ∑ i' : Fin (n + 1), |G k i'| :=
        Finset.single_le_sum (f := fun i' => |G k i'|)
          (fun i' _ => abs_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ k' : Fin (n + 1), ∑ i' : Fin (n + 1), |G k' i'| :=
        Finset.single_le_sum (f := fun k' => ∑ i' : Fin (n + 1), |G k' i'|)
          (fun k' _ => Finset.sum_nonneg (fun i' _ => abs_nonneg _)) (Finset.mem_univ k)

end EllipticPdes.Regularity
