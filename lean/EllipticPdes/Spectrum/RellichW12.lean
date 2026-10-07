/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.GlobalApproximation
public import EllipticPdes.Extension.LinearOperator
public import EllipticPdes.Spectrum.RellichDischarge
public import EllipticPdes.Embedding.H01Sobolev
public import EllipticPdes.Extension.BallChart
public import EllipticPdes.Regularity.RestrictedDiffQuotient

/-!
# Rellich-Kondrachov on the whole graph space

`EllipticPdes.Sobolev.embL2_isCompact` is the compact embedding of `H₀¹(Ω)` into `L²(Ω)` on a
bounded measurable domain. Its proof extends each class by zero and applies the
Fréchet-Kolmogorov criterion to the extensions, whose translation modulus is bounded by the
gradient because a class in `H₀¹(Ω)` is a limit of test functions. An element of the graph
space `W12 Ω`, the `H¹(Ω)` of this development, has no such approximation: extended by zero it
jumps at the boundary, and the translation modulus is lost.

The extension operator restores it. On a bounded open domain with `C¹` boundary,
`EllipticPdes.Extension.exists_extLinear` puts every element of `W12 Ω` on the whole space, with
compact support in a fixed ball, a weak gradient on `ℝᵈ`, and a bound by the norm of the
element. The whole-space translation estimate for a class with a weak gradient,
`transL2_toLp_sub_le_of_hasWeakGradOn_univ`, proved by mollifying the class and passing the
smooth estimate to the limit, gives the modulus, and the Fréchet-Kolmogorov criterion gives
total boundedness of the extensions. Restricting back to `Ω`, through the restriction map of
the regularity chapter, is continuous, so the image of the unit ball of `W12 Ω` in `L²(Ω)` is
totally bounded and the embedding is compact.

## Main declarations

* `EllipticPdes.Sobolev.transL2_toLp_sub_le_of_hasWeakGradOn_univ`: the translation modulus
  of a whole-space class with an `L²` weak gradient.
* `EllipticPdes.Sobolev.embW12`: the embedding `W12 Ω →L[ℝ] L²(Ω)`.
* `EllipticPdes.Sobolev.embW12_isCompact`: that embedding is compact on a bounded open domain
  with `C¹` boundary.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.7 Theorem 1 (p. 286);
Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem IV.2.10.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal Convolution

noncomputable section

namespace EllipticPdes.Sobolev

open EllipticPdes.Embedding (HasWeakGradOn partialD_convolution_eq_of_hasWeakGradOn
  tendsto_eLpNorm_convolution_sub eLpNorm_convolution_le isFiniteMeasure_restrict_of_isBounded)
open EllipticPdes.Extension (HasC1Boundary exists_extLinear SobolevPair hasWeakGradOn_of_mem_W12
  hasC1Boundary_ball)

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### The translation modulus of a whole-space Sobolev class -/

/-- The squared `L²` norm of the `L²` class of a function is the integral of the square. -/
theorem norm_toLp_sq_eq_integral_sq {F : EuclideanSpace ℝ (Fin d) → ℝ}
    (hF : MemLp F 2 volume) : ‖hF.toLp F‖ ^ 2 = ∫ x, F x ^ 2 := by
  rw [norm_sq_eq_integral_sq]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp] with x hx
  rw [hx]

/-- A bound `‖f‖₂ ≤ K X` with `X ≤ ofReal n` gives the real bound `‖f‖₂ ≤ K n`. -/
theorem toReal_eLpNorm_le_of_le {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {f : α → ℝ} {K : ℝ≥0} {n : ℝ} {X : ℝ≥0∞} (hn : 0 ≤ n) (h : eLpNorm f 2 μ ≤ (K : ℝ≥0∞) * X)
    (hX : X ≤ ENNReal.ofReal n) : (eLpNorm f 2 μ).toReal ≤ K * n := by
  have := h.trans (by gcongr : (K : ℝ≥0∞) * X ≤ K * ENNReal.ofReal n)
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg] at this
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) this

/-- A smooth compactly supported function has square-integrable partial derivatives. -/
theorem memLp_partialD_of_contDiff {v : EuclideanSpace ℝ (Fin d) → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvcs : HasCompactSupport v) (k : Fin d) :
    MemLp (partialD k v) 2 volume := by
  have hc : Continuous (partialD k v) :=
    (hv.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : HasCompactSupport (partialD k v) :=
    hvcs.fderiv (𝕜 := ℝ) |>.comp_left (g := fun T : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ =>
      T (EuclideanSpace.single k 1)) (by simp)
  exact hc.memLp_of_hasCompactSupport hcs

/-- **Gradient energy of a mollification.** If the partial derivatives of a smooth compactly
supported `v` are the convolutions of `L²` functions `G k` with a nonnegative mollifier of
integral one, then `∫ ‖∇v‖² ≤ (∑ ‖G k‖_{L²})²`. -/
theorem integral_norm_fderiv_sq_le_of_partialD_eq_convolution
    {v ρ : EuclideanSpace ℝ (Fin d) → ℝ} {G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvcs : HasCompactSupport v) (hρ0 : 0 ≤ ρ)
    (hρm : AEStronglyMeasurable ρ volume) (hρ1 : ∫ y, ρ y ∂volume = 1)
    (hG : ∀ k, MemLp (G k) 2 volume)
    (hpartial : ∀ k, partialD k v = (G k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ)) :
    ∫ x, ‖fderiv ℝ v x‖ ^ 2 ≤ (∑ k, (eLpNorm (G k) 2 volume).toReal) ^ 2 := by
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hpt : (fun x => ‖fderiv ℝ v x‖ ^ 2) = fun x => ∑ k, (partialD k v x) ^ 2 := by
    funext x
    rw [norm_sq_clm_eq_sum_apply_single (fderiv ℝ v x)]
    rfl
  rw [hpt, integral_finsetSum Finset.univ
    (fun k _ => (memLp_partialD_of_contDiff hv hvcs k).integrable_sq)]
  refine le_trans (Finset.sum_le_sum fun k _ => ?_)
    (Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => ENNReal.toReal_nonneg)
  have hmemk := memLp_partialD_of_contDiff hv hvcs k
  rw [← norm_toLp_sq_eq_integral_sq hmemk]
  have hle : eLpNorm (partialD k v) 2 volume ≤ eLpNorm (G k) 2 volume := by
    rw [hpartial k]
    have := eLpNorm_convolution_le one_le_two hρ0 hρm hρ1 (h := G k) (by rw [h2]; exact hG k)
    rwa [h2] at this
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  rw [Lp.norm_def]
  refine ENNReal.toReal_mono (hG k).eLpNorm_lt_top.ne ?_
  exact (eLpNorm_congr_ae hmemk.coeFn_toLp).trans_le hle

/-- **Translation modulus of a smooth compactly supported class.** If the gradient energy of a
smooth compactly supported `v` is at most `S²`, its class in `L²` moves under translation by `h`
by at most `S ‖h‖`. -/
theorem norm_transL2_sub_le_of_contDiff {v : EuclideanSpace ℝ (Fin d) → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvcs : HasCompactSupport v) (hvmem : MemLp v 2 volume) {S : ℝ}
    (hS : 0 ≤ S) (hgrad : ∫ x, ‖fderiv ℝ v x‖ ^ 2 ≤ S ^ 2) (h : EuclideanSpace ℝ (Fin d)) :
    ‖transL2 h (hvmem.toLp v) - hvmem.toLp v‖ ≤ S * ‖h‖ := by
  refine le_of_sq_le_sq ?_ (mul_nonneg hS (norm_nonneg _))
  rw [norm_sq_transL2_sub]
  have hcomp : ∀ᵐ x ∂volume,
      (hvmem.toLp v : EuclideanSpace ℝ (Fin d) → ℝ) (x + h) = v (x + h) :=
    ((measurePreserving_add_right volume h).quasiMeasurePreserving.tendsto_ae).eventually
      hvmem.coeFn_toLp
  have hae : (fun x => (((hvmem.toLp v : EuclideanSpace ℝ (Fin d) → ℝ) (x + h)
      - (hvmem.toLp v : EuclideanSpace ℝ (Fin d) → ℝ) x) ^ 2))
      =ᵐ[volume] fun x => (v (x + h) - v x) ^ 2 := by
    filter_upwards [hcomp, hvmem.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  rw [integral_congr_ae hae]
  calc ∫ x, (v (x + h) - v x) ^ 2
      ≤ ‖h‖ ^ 2 * ∫ x, ‖fderiv ℝ v x‖ ^ 2 :=
        integral_sq_sub_translation_le (hv.of_le (by exact_mod_cast le_top)) hvcs h
    _ ≤ ‖h‖ ^ 2 * S ^ 2 := mul_le_mul_of_nonneg_left hgrad (sq_nonneg _)
    _ = (S * ‖h‖) ^ 2 := by ring

/-- **Translation modulus of a whole-space class with a weak gradient.** A compactly supported
class on `ℝᵈ` with an `L²` weak gradient moves under translation by at most the length of the
translation times the sum of the `L²` norms of its gradient components. The class is
mollified, the smooth estimate `integral_sq_sub_translation_le` applies to each mollification,
whose gradient is the mollified weak gradient and is bounded in `L²` by the weak gradient
itself, and the estimate passes to the `L²` limit. -/
theorem transL2_toLp_sub_le_of_hasWeakGradOn_univ {F : EuclideanSpace ℝ (Fin d) → ℝ}
    {G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hFcs : HasCompactSupport F)
    (hFint : Integrable F volume) (hF : MemLp F 2 volume) (hG : ∀ k, MemLp (G k) 2 volume)
    (hwg : HasWeakGradOn Set.univ F G) (h : EuclideanSpace ℝ (Fin d)) :
    ‖transL2 h (hF.toLp F) - hF.toLp F‖
      ≤ (∑ k, (eLpNorm (G k) 2 volume).toReal) * ‖h‖ := by
  classical
  set L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ) with hL
  let φb : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := fun n =>
    { rIn := 1 / (n + 1 : ℝ) / 2
      rOut := 1 / (n + 1 : ℝ)
      rIn_pos := half_pos (by positivity)
      rIn_lt_rOut := half_lt_self (by positivity) }
  have hφrOut : Tendsto (fun n => (φb n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hφratio : ∀ᶠ n in atTop, (φb n).rOut ≤ 2 * (φb n).rIn :=
    Eventually.of_forall fun n => le_of_eq (by simp [φb]; ring)
  set v : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun n => F ⋆[L, volume] (φb n).normed volume with hvdef
  have hFli : LocallyIntegrable F volume := hFint.locallyIntegrable
  have hvsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n) := fun n =>
    (φb n).hasCompactSupport_normed.contDiff_convolution_right (L := L) hFli
      (φb n).contDiff_normed
  have hvcs : ∀ n, HasCompactSupport (v n) := fun n =>
    HasCompactSupport.convolution (L := L) hFcs (φb n).hasCompactSupport_normed
  have hpartial : ∀ (n : ℕ) (k : Fin d),
      partialD k (v n) = (G k ⋆[L, volume] (φb n).normed volume) := fun n k => by
    funext x
    simpa only [indicator_univ] using partialD_convolution_eq_of_hasWeakGradOn
      MeasurableSet.univ hFint.integrableOn hwg (φb n) k (x := x) (subset_univ _)
  have hvmem : ∀ n, MemLp (v n) 2 volume := fun n =>
    (hvsmooth n).continuous.memLp_of_hasCompactSupport (hvcs n)
  -- the mollifications are in `L²` and converge to the class
  have hconv := tendsto_eLpNorm_convolution_sub one_le_two (h := F)
    (by rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]; exact hF) hφrOut hφratio
  rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num] at hconv
  have htend : Tendsto (fun n => (hvmem n).toLp (v n)) atTop (𝓝 (hF.toLp F)) := by
    rw [tendsto_iff_edist_tendsto_0]
    exact hconv.congr fun n => by rw [Lp.edist_toLp_toLp]
  exact transL2_sub_le_of_tendsto htend (fun n h => norm_transL2_sub_le_of_contDiff (hvsmooth n)
    (hvcs n) (hvmem n) (Finset.sum_nonneg fun k _ => ENNReal.toReal_nonneg)
    (integral_norm_fderiv_sq_le_of_partialD_eq_convolution (hvsmooth n) (hvcs n)
      (fun x => (φb n).nonneg_normed x)
      ((φb n).contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) _).continuous.aestronglyMeasurable
      (φb n).integral_normed hG (hpartial n)) h) h

/-! ### The embedding of the graph space -/

/-- The coordinate-`0` embedding `H¹(Ω) ↪ L²(Ω)`, `U ↦ U 0`, on the graph space `W12 Ω`. -/
def embW12 (Ω : Set (EuclideanSpace ℝ (Fin d))) : W12 Ω →L[ℝ] L2D Ω :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d + 1) => L2D Ω) (0 : Fin (d + 1))).comp (W12 Ω).subtypeL

/-- `embW12 Ω U` is the function coordinate of `U`. -/
@[simp] lemma embW12_apply (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : W12 Ω) :
    embW12 Ω U = (U : H1amb Ω) 0 := by
  simp only [embW12, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, PiLp.proj_apply]

/-- The pair of a function and its gradient components that an element of the graph space
presents to the extension operator. -/
def graphPair (U : W12 Ω) : SobolevPair d :=
  (fun x => ((U : H1amb Ω) 0 : L2D Ω) x, fun (k : Fin d) x => ((U : H1amb Ω) k.succ : L2D Ω) x)

/-- The seminorms of the pair of an element of the graph space are bounded by its norm. -/
theorem eLpNorm_graphPair_le (U : W12 Ω) :
    eLpNorm (graphPair U).1 2 (volume.restrict Ω)
      + ∑ i, eLpNorm ((graphPair U).2 i) 2 (volume.restrict Ω)
      ≤ ENNReal.ofReal ((d + 1) * ‖U‖) := by
  have h0 : eLpNorm (graphPair U).1 2 (volume.restrict Ω) = ENNReal.ofReal ‖(U : H1amb Ω) 0‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_lt_top _).ne]
    rfl
  have hk : ∀ k : Fin d, eLpNorm ((graphPair U).2 k) 2 (volume.restrict Ω)
      = ENNReal.ofReal ‖(U : H1amb Ω) k.succ‖ := fun k => by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_lt_top _).ne]
    rfl
  rw [h0]
  simp_rw [hk]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _),
    ← ENNReal.ofReal_add (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hU : ‖U‖ = ‖(U : H1amb Ω)‖ := rfl
  calc ‖(U : H1amb Ω) 0‖ + ∑ k : Fin d, ‖(U : H1amb Ω) k.succ‖
      ≤ ‖U‖ + ∑ _k : Fin d, ‖U‖ := by
        rw [hU]
        exact add_le_add (PiLp.norm_apply_le _ _)
          (Finset.sum_le_sum fun k _ => PiLp.norm_apply_le _ _)
    _ = (d + 1) * ‖U‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **Rellich-Kondrachov on `H¹(Ω)`** (Evans §5.7 Theorem 1 at `p = q = 2`, Guo Theorem
IV.2.10). On a bounded open domain with `C¹` boundary, the embedding of the graph space
`W12 Ω` into `L²(Ω)` is a compact operator. -/
theorem embW12_isCompact (hd : 0 < d) (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) : IsCompactOperator (embW12 Ω) := by
  classical
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict_of_isBounded hΩb
  obtain ⟨R₀, hR₀⟩ := hΩb.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  have hsub : closure Ω ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) (R₀ + 1) :=
    (closure_minimal hR₀ isClosed_closedBall).trans (closedBall_subset_ball (by linarith))
  obtain ⟨T, K, hT⟩ := exists_extLinear hd hΩopen hΩb hC1 isOpen_ball hsub (p := 2) one_le_two
  let w : W12 Ω → SobolevPair d := graphPair
  have hw : ∀ U : W12 Ω,
      HasWeakGradOn Set.univ (T (w U)).1 (T (w U)).2 ∧ HasCompactSupport (T (w U)).1 ∧
        tsupport (T (w U)).1 ⊆ ball 0 (R₀ + 1) ∧ Integrable (T (w U)).1 volume ∧
        (∀ k, Integrable ((T (w U)).2 k) volume) ∧
        (∀ y ∈ Ω, (T (w U)).1 y = (w U).1 y) ∧
        eLpNorm (T (w U)).1 2 volume ≤ (K : ℝ≥0∞) * (eLpNorm (w U).1 2 (volume.restrict Ω)
          + ∑ i, eLpNorm ((w U).2 i) 2 (volume.restrict Ω)) ∧
        ∀ k, eLpNorm ((T (w U)).2 k) 2 volume ≤ (K : ℝ≥0∞) * (eLpNorm (w U).1 2
          (volume.restrict Ω) + ∑ i, eLpNorm ((w U).2 i) 2 (volume.restrict Ω)) := fun U =>
    hT (w U) ((Lp.memLp _).integrable one_le_two) (fun k => (Lp.memLp _).integrable one_le_two)
      (hasWeakGradOn_of_mem_W12 U.2)
  have hN : ∀ U : W12 Ω, eLpNorm (w U).1 2 (volume.restrict Ω)
      + ∑ i, eLpNorm ((w U).2 i) 2 (volume.restrict Ω) ≤ ENNReal.ofReal ((d + 1) * ‖U‖) :=
    eLpNorm_graphPair_le
  have hKfin : ∀ U : W12 Ω, (K : ℝ≥0∞) * (eLpNorm (w U).1 2 (volume.restrict Ω)
      + ∑ i, eLpNorm ((w U).2 i) 2 (volume.restrict Ω)) < ⊤ := fun U =>
    ENNReal.mul_lt_top ENNReal.coe_lt_top (lt_of_le_of_lt (hN U) ENNReal.ofReal_lt_top)
  have hMF : ∀ U : W12 Ω, MemLp (T (w U)).1 2 volume := fun U =>
    lt_of_le_of_lt (hw U).2.2.2.2.2.2.1 (hKfin U)
  have hMG : ∀ U : W12 Ω, ∀ k, MemLp ((T (w U)).2 k) 2 volume := fun U k =>
    lt_of_le_of_lt ((hw U).2.2.2.2.2.2.2 k) (hKfin U)
  -- the real bounds on the extension and its gradient
  have hFb : ∀ U : W12 Ω, (eLpNorm (T (w U)).1 2 volume).toReal ≤ K * ((d + 1) * ‖U‖) := fun U =>
    toReal_eLpNorm_le_of_le (by positivity) (hw U).2.2.2.2.2.2.1 (hN U)
  have hGb : ∀ U : W12 Ω, ∀ k, (eLpNorm ((T (w U)).2 k) 2 volume).toReal
      ≤ K * ((d + 1) * ‖U‖) := fun U k =>
    toReal_eLpNorm_le_of_le (by positivity) ((hw U).2.2.2.2.2.2.2 k) (hN U)
  -- the extensions of the unit ball, as a family in `L²(ℝᵈ)`
  set Φ : W12 Ω → EucL2 d := fun U => (hMF U).toLp (T (w U)).1 with hΦ
  set S : Set (EucL2 d) := Φ '' closedBall 0 1 with hS
  have hSTB : TotallyBounded S := by
    refine totallyBounded_of_lipschitz_translation S (R := R₀ + 1) (M := K * (d + 1))
      (Λ := d * (K * (d + 1))) ?_ ?_ ?_
    · rintro g ⟨U, hU, rfl⟩
      rw [mem_closedBall, dist_zero_right] at hU
      rw [Lp.norm_def, eLpNorm_congr_ae (hMF U).coeFn_toLp]
      calc (eLpNorm (T (w U)).1 2 volume).toReal ≤ K * ((d + 1) * ‖U‖) := hFb U
        _ ≤ K * ((d + 1) * 1) := by gcongr
        _ = K * (d + 1) := by ring
    · rintro g ⟨U, hU, rfl⟩
      filter_upwards [(hMF U).coeFn_toLp] with x hx hxR
      rw [hx]
      refine image_eq_zero_of_notMem_tsupport fun hc => hxR ?_
      exact ball_subset_closedBall ((hw U).2.2.1 hc)
    · rintro g ⟨U, hU, rfl⟩ h
      rw [mem_closedBall, dist_zero_right] at hU
      refine (transL2_toLp_sub_le_of_hasWeakGradOn_univ (hw U).2.1 (hw U).2.2.2.1 (hMF U)
        (hMG U) (hw U).1 h).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      calc ∑ k, (eLpNorm ((T (w U)).2 k) 2 volume).toReal
          ≤ ∑ _k : Fin d, K * ((d + 1) * ‖U‖) := Finset.sum_le_sum fun k _ => hGb U k
        _ = d * (K * ((d + 1) * ‖U‖)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ d * (K * ((d + 1) * 1)) := by gcongr
        _ = d * (K * (d + 1)) := by ring
  -- the image of the unit ball in `L²(Ω)` is the restriction of that family
  have himg : embW12 Ω '' closedBall (0 : W12 Ω) 1
      ⊆ Regularity.restrictL2 (Ω := Ω) '' S := by
    rintro f ⟨U, hU, rfl⟩
    refine ⟨Φ U, ⟨U, hU, rfl⟩, ?_⟩
    rw [embW12_apply]
    apply Lp.ext
    have h1 := Regularity.coeFn_restrictL2 (Ω := Ω) (Φ U)
    have h2 : ((hMF U).toLp (T (w U)).1 : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] (T (w U)).1 := ae_restrict_of_ae (hMF U).coeFn_toLp
    have h3 : (T (w U)).1 =ᵐ[volume.restrict Ω]
        fun x => ((U : H1amb Ω) 0 : L2D Ω) x :=
      (ae_restrict_iff' hΩopen.measurableSet).mpr
        (Eventually.of_forall fun y hy => (hw U).2.2.2.2.2.1 y hy)
    exact (h1.trans h2).trans h3
  have hTB : TotallyBounded (embW12 Ω '' closedBall (0 : W12 Ω) 1) :=
    (hSTB.image (Regularity.restrictL2 (Ω := Ω)).uniformContinuous).subset himg
  exact (isCompactOperator_iff_isCompact_closure_image_closedBall (embW12 Ω).toLinearMap
    one_pos).mpr (hTB.closure.isCompact_of_isClosed isClosed_closure)

/-- **Rellich-Kondrachov on `H¹` of the unit ball**, every hypothesis discharged. -/
theorem embW12_isCompact_ball (hd : 0 < d) :
    IsCompactOperator (embW12 (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :=
  embW12_isCompact hd isOpen_ball isBounded_ball (hasC1Boundary_ball hd)

end EllipticPdes.Sobolev
