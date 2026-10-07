/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Spectrum.RellichW12
public import EllipticPdes.Embedding.ConstOfGradZero
public import EllipticPdes.Extension.BallChart

/-!
# Poincaré's inequality with the mean subtracted

On a bounded connected open domain with `C¹` boundary, an element of `H¹(Ω)` is within a
constant times the `L²` norm of its gradient of its mean. This is Evans §5.8.1 Theorem 1 at
`p = 2`. Only the gradient appears on the right, which is what distinguishes it from the
Poincaré inequality on `H₀¹(Ω)` the library runs existence on, where the boundary condition
replaces the subtraction of the mean.

The proof is Evans's, by contradiction. Were the estimate false, a sequence of elements of unit
`L²` norm, zero mean and gradient tending to zero would exist; Rellich-Kondrachov on the graph
space makes a subsequence converge in `L²`, the limit has zero weak gradient because the graph
space is closed, so it is constant on the connected domain, its mean is zero, so it vanishes,
against its unit norm.

## Main declarations

* `EllipticPdes.Sobolev.constGraph`: the graph of a constant, with zero gradient, and
  `constGraph_mem_W12`.
* `EllipticPdes.Sobolev.meanL2`: the mean over the domain as a continuous linear functional on
  `L²(Ω)`.
* `EllipticPdes.Sobolev.poincare_wirtinger`: the inequality.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.8.1 Theorem 1 (p. 290).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Sobolev

open EllipticPdes.Embedding (HasWeakGradOn isFiniteMeasure_restrict_of_isBounded
  ae_const_of_hasWeakGradOn_zero)
open EllipticPdes.Extension (HasC1Boundary hasWeakGradOn_of_mem_W12 inner_L2D_eq_integral
  hasC1Boundary_ball)

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### Constants -/

section Constants

variable (hΩb : Bornology.IsBounded Ω)

/-- The class of a constant in `L²(Ω)`. -/
def constL2 (c : ℝ) : L2D Ω :=
  haveI := isFiniteMeasure_restrict_of_isBounded hΩb
  (memLp_const c).toLp _

/-- `constL2 hΩb c` is almost everywhere equal to the constant `c` on `Ω`. -/
theorem coeFn_constL2 (c : ℝ) :
    (constL2 hΩb c : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume.restrict Ω] fun _ => c :=
  haveI := isFiniteMeasure_restrict_of_isBounded hΩb
  (memLp_const c).coeFn_toLp

/-- `constL2 hΩb 0` is zero. -/
theorem constL2_zero : constL2 hΩb 0 = 0 :=
  Lp.ext ((coeFn_constL2 hΩb 0).trans (Lp.coeFn_zero ℝ 2 _).symm)

/-- The graph of a constant: the constant as function coordinate and zero as gradient. -/
def constGraph (c : ℝ) : H1amb Ω :=
  WithLp.toLp 2 (Fin.cons (constL2 hΩb c) fun _ => 0)

/-- The function coordinate of `constGraph hΩb c` is `constL2 hΩb c`. -/
@[simp] theorem constGraph_zero (c : ℝ) : constGraph hΩb c 0 = constL2 hΩb c := by
  rw [constGraph, PiLp.toLp_apply, Fin.cons_zero]

/-- Every gradient coordinate of `constGraph hΩb c` is zero. -/
@[simp] theorem constGraph_succ (c : ℝ) (k : Fin d) : constGraph hΩb c k.succ = 0 := by
  rw [constGraph, PiLp.toLp_apply, Fin.cons_succ]

/-- **Membership of a constant in the graph space**, with zero weak gradient: a test
function's partial derivative integrates to zero. -/
theorem constGraph_mem_W12 (c : ℝ) : constGraph hΩb c ∈ W12 Ω := by
  have := isFiniteMeasure_restrict_of_isBounded hΩb
  rw [mem_W12_iff]
  intro ψ g i
  rw [constGraph_zero, constGraph_succ, inner_zero_right, add_zero]
  simp only [IsTestFn.partialCls, constL2]
  rw [inner_toLp_eq]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport
      (fun hc => hx (g.2.2 (tsupport_partialD_subset i ψ hc))), zero_mul])]
  simp only [partialD]
  have hib := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : EuclideanSpace ℝ (Fin d) => c) (g := ψ) (v := EuclideanSpace.single i 1)
    (by simp) (by
      have : Continuous fun x => c * partialD i ψ x :=
        continuous_const.mul (g.continuous_partialD i)
      exact this.integrable_of_hasCompactSupport (g.hasCompactSupport_partialD i).mul_left)
    ((continuous_const.mul g.continuous).integrable_of_hasCompactSupport g.2.1.mul_left)
    (fun x _ => differentiableAt_const _)
    (fun x _ => (g.1.differentiable (by simp)).differentiableAt)
  simp only [fderiv_fun_const, Pi.zero_apply, _root_.zero_apply, zero_mul,
    integral_zero, neg_zero] at hib
  rw [← hib]
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

/-- **Mean as a functional.** The mean over `Ω` of an `L²(Ω)` class, read as the inner
product against the constant one over the measure of the domain. -/
def meanL2 : L2D Ω →L[ℝ] ℝ :=
  ((volume Ω).toReal)⁻¹ • innerSL ℝ (constL2 hΩb 1)

/-- `meanL2 hΩb f` is the integral of `f` over `Ω` divided by the volume of `Ω`. -/
theorem meanL2_apply (f : L2D Ω) :
    meanL2 hΩb f = ((volume Ω).toReal)⁻¹ * ∫ x in Ω, f x := by
  simp only [meanL2, _root_.smul_apply, innerSL_apply_apply, smul_eq_mul]
  congr 1
  rw [inner_L2D_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_constL2 hΩb 1] with x hx
  rw [hx, one_mul]

/-- `meanL2 hΩb` takes the constant `c` to `c` when `Ω` has nonzero volume. -/
theorem meanL2_constL2 (hΩ0 : volume Ω ≠ 0) (c : ℝ) : meanL2 hΩb (constL2 hΩb c) = c := by
  have := isFiniteMeasure_restrict_of_isBounded hΩb
  rw [meanL2_apply, integral_congr_ae (coeFn_constL2 hΩb c), setIntegral_const, smul_eq_mul,
    measureReal_def]
  have htop : volume Ω ≠ ⊤ := by
    rw [← Measure.restrict_apply_univ]; exact measure_ne_top _ _
  have hm : (volume Ω).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hΩ0, htop⟩
  field_simp

end Constants

/-! ### The inequality -/

/-- **A limit of elements with vanishing gradient is constant.** If `V k ∈ W12 Ω` have gradient
coordinates bounded by `γ k → 0` and a subsequence of their function coordinates converges in
`L²(Ω)` to `v`, then `v` is a constant class on a connected open set: the limit graph
`(v, 0, …, 0)` lies in the closed subspace `W12 Ω`, so `v` has zero weak gradient. -/
theorem exists_eq_constL2_of_tendsto_zero_gradient (hΩopen : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hconn : IsPreconnected Ω) {V : ℕ → W12 Ω} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) {v : L2D Ω} (hlim : Tendsto (fun j => embW12 Ω (V (φ j))) atTop (𝓝 v))
    {γ : ℕ → ℝ} (hγ : Tendsto γ atTop (𝓝 0))
    (hle : ∀ k (j : Fin d), ‖((V k : W12 Ω) : H1amb Ω) j.succ‖ ≤ γ k) :
    ∃ c : ℝ, v = constL2 hΩb c := by
  have := isFiniteMeasure_restrict_of_isBounded hΩb
  -- the limit in the graph space
  set Vlim : H1amb Ω := WithLp.toLp 2 (Fin.cons v fun _ => 0) with hVlim
  have hVlim0 : Vlim 0 = v := by rw [hVlim, PiLp.toLp_apply, Fin.cons_zero]
  have hVlimsucc : ∀ j : Fin d, Vlim j.succ = 0 := fun j => by
    rw [hVlim, PiLp.toLp_apply, Fin.cons_succ]
  have htend : Tendsto (fun j => ((V (φ j) : W12 Ω) : H1amb Ω)) atTop (𝓝 Vlim) := by
    have hcoord : Tendsto (fun j => WithLp.toLp 2 fun i => ((V (φ j) : W12 Ω) : H1amb Ω) i)
        atTop (𝓝 (WithLp.toLp 2 (Fin.cons v fun _ => 0))) := by
      refine ((PiLp.continuous_toLp 2 _).tendsto _).comp (tendsto_pi_nhds.mpr ?_)
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        have : (fun j => ((V (φ j) : W12 Ω) : H1amb Ω) 0) = fun j => embW12 Ω (V (φ j)) := by
          funext j; rw [embW12_apply]
        rw [this]
        exact hlim
      · simp only [Fin.cons_succ]
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
          (hγ.comp hφ.tendsto_atTop) (fun k => norm_nonneg _) fun k => ?_
        exact hle (φ k) j
    simpa only [WithLp.toLp_ofLp] using hcoord
  have hclosed : IsClosed ((W12 Ω : Submodule ℝ (H1amb Ω)) : Set (H1amb Ω)) :=
    Submodule.isClosed_orthogonal _
  have hVlimW : Vlim ∈ W12 Ω :=
    hclosed.mem_of_tendsto htend (Eventually.of_forall fun j => (V (φ j)).2)
  -- the limit has zero weak gradient, so it is constant
  have hwg : HasWeakGradOn Ω (fun x => (v : EuclideanSpace ℝ (Fin d) → ℝ) x) fun _ _ => 0 := by
    have h := hasWeakGradOn_of_mem_W12 hVlimW
    rw [hVlim0] at h
    simp only [hVlimsucc] at h
    exact h.congr_ae EventuallyEq.rfl fun _ => Lp.coeFn_zero ℝ 2 _
  obtain ⟨c, hc⟩ := ae_const_of_hasWeakGradOn_zero hΩopen hconn
    ((Lp.memLp v).integrable one_le_two) hwg
  exact ⟨c, Lp.ext (hc.trans (coeFn_constL2 hΩb c).symm)⟩

/-- **Normalisation of a violator of Poincaré's inequality.** If `c` times the gradient norm of
`U` is below the distance of `U` from its mean, subtracting the mean and dividing by that
distance gives an element of `W12 Ω` whose function part has norm one and mean zero, whose
gradient coordinates are at most `1 / c`, and which has norm at most two when `1 ≤ c`. -/
theorem exists_normalised_of_lt_poincare (hΩb : Bornology.IsBounded Ω)
    (hΩ0 : volume Ω ≠ 0) {c : ℝ} (hc : 1 ≤ c) {U : W12 Ω}
    (hU : c * Real.sqrt (∑ k : Fin d, ‖(U : H1amb Ω) k.succ‖ ^ 2)
      < ‖embW12 Ω U - constL2 hΩb (meanL2 hΩb (embW12 Ω U))‖) :
    ∃ V : W12 Ω, ‖embW12 Ω V‖ = 1 ∧ meanL2 hΩb (embW12 Ω V) = 0 ∧
      (∀ j : Fin d, ‖(V : H1amb Ω) j.succ‖ ≤ 1 / c) ∧ ‖V‖ ≤ 2 := by
  have := isFiniteMeasure_restrict_of_isBounded hΩb
  set g : ℝ := Real.sqrt (∑ k : Fin d, ‖(U : H1amb Ω) k.succ‖ ^ 2) with hg
  set P : L2D Ω := embW12 Ω U - constL2 hΩb (meanL2 hΩb (embW12 Ω U)) with hP
  have hg0 : 0 ≤ g := Real.sqrt_nonneg _
  have hPpos : 0 < ‖P‖ := lt_of_le_of_lt (mul_nonneg (by linarith) hg0) hU
  set V : W12 Ω := ‖P‖⁻¹ •
    (U - ⟨constGraph hΩb (meanL2 hΩb (embW12 Ω U)), constGraph_mem_W12 hΩb _⟩) with hVdef
  have hV0 : embW12 Ω V = ‖P‖⁻¹ • P := by
    simp only [hVdef, map_smul, map_sub]
    congr 2
  have hVnorm : ‖embW12 Ω V‖ = 1 := by
    rw [hV0, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hPpos.ne']
  have hVsucc : ∀ j : Fin d, (V : H1amb Ω) j.succ = ‖P‖⁻¹ • (U : H1amb Ω) j.succ := fun j => by
    simp only [hVdef, Submodule.coe_smul, Submodule.coe_sub, PiLp.smul_apply, PiLp.sub_apply,
      constGraph_succ, sub_zero]
  have hgV : Real.sqrt (∑ k : Fin d, ‖(V : H1amb Ω) k.succ‖ ^ 2) = ‖P‖⁻¹ * g := by
    simp only [hg, hVsucc, norm_smul, norm_inv, norm_norm, mul_pow, ← Finset.mul_sum]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hgle : ‖P‖⁻¹ * g ≤ 1 / c := by
    rw [inv_mul_eq_div, div_le_div_iff₀ hPpos (by linarith)]
    nlinarith [hU]
  refine ⟨V, hVnorm, ?_, fun j => ?_, ?_⟩
  · rw [hV0, map_smul, hP, map_sub, meanL2_constL2 hΩb hΩ0, sub_self, smul_zero]
  · refine le_trans ?_ (hgV.trans_le hgle)
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum
      (f := fun i : Fin d => ‖(V : H1amb Ω) i.succ‖ ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j))
  · have hsq : ‖V‖ ^ 2 = 1 + (‖P‖⁻¹ * g) ^ 2 := by
      rw [show ‖V‖ = ‖(V : H1amb Ω)‖ from rfl, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ,
        ← embW12_apply, hVnorm, one_pow, ← hgV, Real.sq_sqrt (Finset.sum_nonneg fun _ _ =>
          sq_nonneg _)]
    have hg1 : ‖P‖⁻¹ * g ≤ 1 := hgle.trans ((div_le_one (by linarith)).2 hc)
    exact le_of_sq_le_sq (by rw [hsq]; nlinarith [mul_nonneg (inv_nonneg.2 hPpos.le) hg0])
      (by norm_num)

/-- **Poincaré's inequality with the mean subtracted** (Evans §5.8.1 Theorem 1 at `p = 2`).
On a bounded, connected, open domain with `C¹` boundary, one constant bounds the `L²`
distance of every element of `H¹(Ω)` from its mean by the `L²` norm of its gradient. -/
theorem poincare_wirtinger (hd : 0 < d) (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) (hconn : IsPreconnected Ω) (hne : Ω.Nonempty) :
    ∃ C : ℝ, ∀ U : W12 Ω,
      ‖embW12 Ω U - constL2 hΩb (meanL2 hΩb (embW12 Ω U))‖
        ≤ C * Real.sqrt (∑ k : Fin d, ‖(U : H1amb Ω) k.succ‖ ^ 2) := by
  classical
  have hΩ0 : volume Ω ≠ 0 := (hΩopen.measure_pos volume hne).ne'
  by_contra hC
  simp only [not_exists, not_forall, not_le] at hC
  choose Useq hU using fun k : ℕ => hC ((k : ℝ) + 1)
  choose V hV1 hVmean hVsucc hVbdd using fun k : ℕ =>
    exists_normalised_of_lt_poincare hΩb hΩ0 (c := (k : ℝ) + 1)
      (by linarith [k.cast_nonneg (α := ℝ)]) (hU k)
  -- Rellich-Kondrachov: a subsequence converges in `L²`
  have hcpt := (embW12_isCompact hd hΩopen hΩb hC1).isCompact_closure_image_closedBall 2
  have hmem : ∀ k, embW12 Ω (V k) ∈ closure (embW12 Ω '' closedBall (0 : W12 Ω) 2) :=
    fun k => subset_closure ⟨V k, mem_closedBall_zero_iff.mpr (hVbdd k), rfl⟩
  obtain ⟨v, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq hmem
  -- the limit has zero weak gradient, so it is constant
  obtain ⟨c, hvc⟩ := exists_eq_constL2_of_tendsto_zero_gradient hΩopen hΩb hconn hφ hlim
    tendsto_one_div_add_atTop_nhds_zero_nat hVsucc
  -- its mean is zero, so the constant is zero
  have hmean : meanL2 hΩb v = 0 :=
    tendsto_nhds_unique (((meanL2 hΩb).continuous.tendsto v).comp hlim)
      (tendsto_const_nhds.congr fun j => (hVmean (φ j)).symm)
  rw [hvc, meanL2_constL2 hΩb hΩ0] at hmean
  rw [hmean, constL2_zero] at hvc
  -- against the unit norm of the limit
  have hnorm1 : ‖v‖ = 1 :=
    tendsto_nhds_unique hlim.norm (tendsto_const_nhds.congr fun j => (hV1 (φ j)).symm)
  rw [hvc, norm_zero] at hnorm1
  exact zero_ne_one hnorm1

/-- **Inequality on the unit ball**, every hypothesis discharged: the ball is open, bounded,
convex hence connected, nonempty, and has `C¹` boundary. -/
theorem poincare_wirtinger_ball (hd : 0 < d) :
    ∃ C : ℝ, ∀ U : W12 (ball (0 : EuclideanSpace ℝ (Fin d)) 1),
      ‖embW12 _ U - constL2 isBounded_ball (meanL2 isBounded_ball (embW12 _ U))‖
        ≤ C * Real.sqrt (∑ k : Fin d, ‖(U : H1amb (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
          k.succ‖ ^ 2) :=
  poincare_wirtinger hd isOpen_ball isBounded_ball (hasC1Boundary_ball hd)
    (convex_ball _ _).isPreconnected ⟨0, mem_ball_self one_pos⟩

end EllipticPdes.Sobolev
