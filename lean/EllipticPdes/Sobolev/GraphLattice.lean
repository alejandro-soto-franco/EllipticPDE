/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Analysis.Mollifier
public import EllipticPdes.Embedding.Convolution
public import EllipticPdes.Embedding.WeakDerivChain
public import EllipticPdes.Sobolev.Graph
public import EllipticPdes.Sobolev.WeakDerivClassical

/-!
# Truncation in `H₀¹` over a finite-dimensional inner product space

`H₀¹(μ, Ω)` is closed under the truncation `u ↦ (u - k)⁺` for `k ≥ 0`. Two steps. A class on the
whole space with an `L²` weak gradient and compact support inside the open set `Ω` lies in
`H₀¹(μ, Ω)`: its mollifications are test functions of `Ω` once the radius is below the distance
from the support to the complement, and they converge to it in `H¹` together with their
gradients, which are the mollified weak gradient. Then, for `V ∈ H₀¹(μ, Ω)` approximated by test
functions `φₙ`, the truncations `(φₙ - k)⁺` have compact support in `Ω` because `k ≥ 0`, have
the weak gradient `∇φₙ` on `{φₙ > k}` by the chain rule for the positive part, so lie in
`H₀¹(μ, Ω)` by the first step, and converge in `H¹` to `(v - k)⁺` with gradient `∇v` on
`{v > k}`: the function coordinates because truncation is `1`-Lipschitz, the gradient
coordinates along a subsequence converging almost everywhere by dominated convergence, the level
set `{v = k}` giving nothing because the weak gradient vanishes there.

## Main declarations

* `EllipticPdes.H1Graph.mem_H01_of_hasCompactSupport`: a compactly supported class with `L²`
  weak gradient lies in `H₀¹`.
* `EllipticPdes.H1Graph.exists_mem_H01_posPart_sub_const`: `H₀¹` is closed under
  `u ↦ (u - k)⁺` for `k ≥ 0`.

## References

D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§8.1 Theorem 8.1 and Corollary 8.2 (pp. 179–180).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology TopologicalSpace
open scoped NNReal ENNReal Convolution RealInnerProductSpace
open ContinuousLinearMap (lsmul)

noncomputable section

namespace EllipticPdes

/-! ### Convergence of truncated fields -/

section Truncation

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] {ν : Measure α}

/-- The truncation `t ↦ max (t - k) 0` is `1`-Lipschitz. -/
theorem abs_max_sub_le (a b k : ℝ) : |max (a - k) 0 - max (b - k) 0| ≤ |a - b| := by
  have := abs_max_sub_max_le_abs (a - k) (b - k) 0
  rwa [sub_sub_sub_cancel_right] at this

/-- **Measurability of a truncated field.** The restriction of a measurable field to a
superlevel set is measurable. -/
theorem aestronglyMeasurable_ite_lt_vec {u : α → ℝ} {w : α → F} (hu : AEStronglyMeasurable u ν)
    (hw : AEStronglyMeasurable w ν) (c : ℝ) :
    AEStronglyMeasurable (fun x => if c < u x then w x else 0) ν := by
  refine ⟨fun x => if c < hu.mk u x then hw.mk w x else 0, ?_, ?_⟩
  · exact StronglyMeasurable.ite
      (measurableSet_lt measurable_const hu.stronglyMeasurable_mk.measurable)
      hw.stronglyMeasurable_mk stronglyMeasurable_const
  · filter_upwards [hu.ae_eq_mk, hw.ae_eq_mk] with x h1 h2
    simp only [h1, h2]

/-- At a point where `ψₙ → v` and `g = 0` on the level `v = k`, the truncated values
`1_{ψₙ > k} g` eventually equal `1_{v > k} g`. -/
lemma eventually_ite_lt_sub_eq_zero {ψ : ℕ → ℝ} {v k : ℝ} {g : F} (hψ : Tendsto ψ atTop (𝓝 v))
    (hl : v = k → g = 0) :
    ∀ᶠ n in atTop, (if k < ψ n then g else 0) - (if k < v then g else 0) = 0 := by
  rcases lt_trichotomy v k with hlt | heq | hgt
  · filter_upwards [hψ.eventually (gt_mem_nhds hlt)] with n hn
    simp [not_lt.mpr hn.le, not_lt.mpr hlt.le]
  · refine Eventually.of_forall fun n => ?_
    simp only [hl heq]
    split_ifs <;> simp
  · filter_upwards [hψ.eventually (lt_mem_nhds hgt)] with n hn
    simp [hn, hgt]

/-- **Convergence of a level-set indicator.** Let `ψₙ → v` almost everywhere and let `g` be
square integrable and vanish on `{v = k}`. Then `1_{ψₙ > k} g → 1_{v > k} g` in `L²`. -/
lemma tendsto_eLpNorm_indicator_lt_sub {ψ : ℕ → α → ℝ} {v : α → ℝ} {g : α → F} {k : ℝ}
    (hψm : ∀ n, AEStronglyMeasurable (ψ n) ν) (hvm : AEStronglyMeasurable v ν)
    (hg : MemLp g 2 ν) (hae : ∀ᵐ x ∂ν, Tendsto (fun n => ψ n x) atTop (𝓝 (v x)))
    (hlev : ∀ᵐ x ∂ν, v x = k → g x = 0) :
    Tendsto (fun n => eLpNorm ((fun x => if k < ψ n x then g x else 0)
      - fun x => if k < v x then g x else 0) 2 ν) atTop (𝓝 0) := by
  have hBm : ∀ n, AEStronglyMeasurable ((fun x => if k < ψ n x then g x else 0)
      - fun x => if k < v x then g x else 0) ν := fun n =>
    (aestronglyMeasurable_ite_lt_vec (hψm n) hg.aestronglyMeasurable k).sub
      (aestronglyMeasurable_ite_lt_vec hvm hg.aestronglyMeasurable k)
  have hrepr : ∀ n, eLpNorm ((fun x => if k < ψ n x then g x else 0)
      - fun x => if k < v x then g x else 0) 2 ν = (∫⁻ x, ‖(if k < ψ n x then g x else 0)
        - (if k < v x then g x else 0)‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) := fun n => by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top (hBm n),
      ENNReal.toReal_ofNat]
    rfl
  simp only [hrepr]
  have hlim : Tendsto (fun n => ∫⁻ x, ‖(if k < ψ n x then g x else 0)
      - (if k < v x then g x else 0)‖ₑ ^ (2 : ℝ) ∂ν) atTop (𝓝 (∫⁻ _, (0 : ℝ≥0∞) ∂ν)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun x => ‖g x‖ₑ ^ (2 : ℝ))
      (fun n => (hBm n).enorm.pow_const _) (fun n => Eventually.of_forall fun x => ?_) ?_ ?_
    · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
        coe_nnnorm, coe_nnnorm]
      split_ifs <;> simp
    · exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
        hg.eLpNorm_lt_top).ne
    · filter_upwards [hae, hlev] with x hx hxl
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ite_lt_sub_eq_zero hx hxl] with n hn
      rw [hn, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [lintegral_zero] at hlim
  have := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0 |>.comp hlim
  rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this

/-- **Convergence of truncated gradients.** Let `ψₙ → v` almost everywhere, let `Dψₙ → g` in `L²`,
and let `g` vanish on the level set `{v = k}`. Then `1_{ψₙ > k} Dψₙ → 1_{v > k} g` in `L²`. -/
lemma tendsto_eLpNorm_ite_lt_sub {ψ : ℕ → α → ℝ} {Dψ : ℕ → α → F} {v : α → ℝ} {g : α → F}
    {k : ℝ} (hψm : ∀ n, AEStronglyMeasurable (ψ n) ν)
    (hDm : ∀ n, AEStronglyMeasurable (Dψ n) ν) (hvm : AEStronglyMeasurable v ν)
    (hg : MemLp g 2 ν) (hD : Tendsto (fun n => eLpNorm (Dψ n - g) 2 ν) atTop (𝓝 0))
    (hae : ∀ᵐ x ∂ν, Tendsto (fun n => ψ n x) atTop (𝓝 (v x)))
    (hlev : ∀ᵐ x ∂ν, v x = k → g x = 0) :
    Tendsto (fun n => eLpNorm ((fun x => if k < ψ n x then Dψ n x else 0)
      - fun x => if k < v x then g x else 0) 2 ν) atTop (𝓝 0) := by
  have hA : Tendsto (fun n => eLpNorm (fun x => if k < ψ n x then Dψ n x - g x else 0) 2 ν)
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hD (fun _ => zero_le)
      fun n => eLpNorm_mono (aestronglyMeasurable_ite_lt_vec (hψm n)
        ((hDm n).sub hg.aestronglyMeasurable) k) fun x => ?_
    simp only [Pi.sub_apply]
    split_ifs <;> simp
  have hsum := hA.add (tendsto_eLpNorm_indicator_lt_sub hψm hvm hg hae hlev)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun n => ?_
  have hsplit : ((fun x => if k < ψ n x then Dψ n x else 0) - fun x => if k < v x then g x else 0)
      = (fun x => if k < ψ n x then Dψ n x - g x else 0) + ((fun x => if k < ψ n x then g x else 0)
        - fun x => if k < v x then g x else 0) := funext fun x => by
    simp only [Pi.sub_apply, Pi.add_apply]
    split_ifs <;> abel
  rw [hsplit]
  exact eLpNorm_add_le one_le_two

/-- A truncation `(v - k)⁺` of an `L²` function is in `L²`. -/
theorem memLp_max_sub_const {v : α → ℝ} (hv : MemLp v 2 ν) {k : ℝ} (hk : 0 ≤ k) :
    MemLp (fun x => max (v x - k) 0) 2 ν := by
  refine hv.of_le (((continuous_id.sub continuous_const).max
    continuous_const).comp_aestronglyMeasurable hv.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [le_abs_self (v x)]) (abs_nonneg _)

/-- A field cut to the superlevel set `{k < v}` is in `L²` when the field and `v` are. -/
theorem memLp_ite_lt_vec {v : α → ℝ} {g : α → F} (hv : MemLp v 2 ν) (hg : MemLp g 2 ν) (k : ℝ) :
    MemLp (fun x => if k < v x then g x else 0) 2 ν :=
  hg.of_le (aestronglyMeasurable_ite_lt_vec hv.aestronglyMeasurable hg.aestronglyMeasurable k)
    (Eventually.of_forall fun x => by split_ifs <;> simp)

end Truncation

/-! ### Mollification in the graph space -/

namespace H1Graph

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Convergence in the graph space from convergence in `L²` of representatives. -/
lemma tendsto_mk_of_tendsto_eLpNorm {ι : Type*} {l : Filter ι} {Φ : ι → H1Graph μ Ω}
    {f : ι → E → ℝ} {g : ι → E → E} {v : E → ℝ} {w : E → E}
    (hv : MemLp v 2 (μ.restrict Ω)) (hw : MemLp w 2 (μ.restrict Ω))
    (hf : ∀ i, ⇑(fnL (Φ i)) =ᵐ[μ.restrict Ω] f i)
    (hg : ∀ i, ⇑(gradL (Φ i)) =ᵐ[μ.restrict Ω] g i)
    (h1 : Tendsto (fun i => eLpNorm (f i - v) 2 (μ.restrict Ω)) l (𝓝 0))
    (h2 : Tendsto (fun i => eLpNorm (g i - w) 2 (μ.restrict Ω)) l (𝓝 0)) :
    Tendsto Φ l (𝓝 (mk (hv.toLp v) (hw.toLp w))) := by
  rw [tendsto_iff, fnL_mk, gradL_mk]
  refine ⟨(Lp.tendsto_Lp_iff_tendsto_eLpNorm _ _ hv).2 ?_,
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm _ _ hw).2 ?_⟩
  · exact h1.congr fun i => eLpNorm_congr_ae ((hf i).symm.sub EventuallyEq.rfl)
  · exact h2.congr fun i => eLpNorm_congr_ae ((hg i).symm.sub EventuallyEq.rfl)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A square-integrable function of compact support is integrable. -/
lemma integrable_of_memLp_hasCompactSupport {w : E → ℝ} (hw : MemLp w 2 μ)
    (hwcs : HasCompactSupport w) : Integrable w μ := by
  have : IsFiniteMeasure (μ.restrict (tsupport w)) :=
    isFiniteMeasure_restrict.2 hwcs.measure_lt_top.ne
  have : IntegrableOn w (tsupport w) μ :=
    (hw.mono_measure Measure.restrict_le_self).integrable one_le_two
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport w)).mp this

/-- **Mollifications are test functions.** The mollification of an integrable function of compact
support by a bump whose outer radius thickens the support inside `Ω` is a test function of `Ω`. -/
lemma convolution_normed_mem_testFunctions {w : E → ℝ} (hwint : Integrable w μ)
    (hwcs : HasCompactSupport w) (ρ : ContDiffBump (0 : E))
    (hρ : cthickening ρ.rOut (tsupport w) ⊆ Ω) :
    (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] w) ∈ testFunctions Ω :=
  ⟨contDiff_normed_convolution ρ hwint.locallyIntegrable,
    hasCompactSupport_normed_convolution ρ hwcs,
    (tsupport_normed_convolution_subset ρ hwcs).trans hρ⟩

/-- **Compactly supported classes with `L²` weak gradient lie in `H₀¹`.** A class on the whole
space with an `L²` weak gradient whose support is a compact subset of the open set `Ω` is, with
its gradient, the `H¹` limit of its mollifications, which are test functions of `Ω`. -/
theorem mem_H01_of_hasCompactSupport (hΩ : IsOpen Ω) {w : E → ℝ} {g : E → E}
    (hwg : HasWeakFDerivOn ⊤ w (fun x => innerSL ℝ (g x)) μ)
    (hw : MemLp w 2 μ) (hg : MemLp g 2 μ) (hwcs : HasCompactSupport w)
    (hwΩ : tsupport w ⊆ Ω) :
    mk ((hw.mono_measure Measure.restrict_le_self).toLp w)
      ((hg.mono_measure Measure.restrict_le_self).toLp g) ∈ H01 μ Ω := by
  obtain ⟨δ, hδ, hK'⟩ := IsCompact.exists_cthickening_subset_open hwcs hΩ hwΩ
  have hwint := integrable_of_memLp_hasCompactSupport hw hwcs
  set ρ : ℕ → ContDiffBump (0 : E) := fun n => mollifier hδ n with hρ
  set G : E → E →L[ℝ] ℝ := fun x => innerSL ℝ (g x) with hG
  have hGm : MemLp G 2 μ := (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).comp_memLp' hg
  have hmem : ∀ n, (ρ n).normed μ ⋆[lsmul ℝ ℝ, μ] w ∈ testFunctions Ω :=
    fun n => convolution_normed_mem_testFunctions hwint hwcs _
      ((cthickening_mono (rOut_mollifier_le hδ n) _).trans hK')
  have hfd : ∀ n y, fderiv ℝ ((ρ n).normed μ ⋆[lsmul ℝ ℝ, μ] w) y
      = ((ρ n).normed μ ⋆[lsmul ℝ ℝ, μ] G) y := fun n y => by
    have := hasFDerivAt_convolution_of_forall_integral_eq (K := univ) (u := w) (G := G)
      (by simpa using hwint.locallyIntegrable) (by simpa using hGm.locallyIntegrable one_le_two)
      (fun v ψ hψ hψc hψs => (hwg v).integral_eq hψ hψc hψs) (ρ n)
      (y := y) (subset_univ _)
    simpa using this.fderiv
  refine isClosed_H01.mem_of_tendsto (b := atTop)
    (f := fun n => testGraphₗ μ Ω ⟨_, hmem n⟩) ?_
    (Eventually.of_forall fun n => testGraphₗ_mem_H01 _)
  refine tendsto_mk_of_tendsto_eLpNorm (f := fun n => (ρ n).normed μ ⋆[lsmul ℝ ℝ, μ] w)
    (g := fun n => gradient ((ρ n).normed μ ⋆[lsmul ℝ ℝ, μ] w)) _ _
    (fun n => coeFn_fnL_testGraphₗ ⟨_, hmem n⟩) (fun n => coeFn_gradL_testGraphₗ ⟨_, hmem n⟩) ?_ ?_
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (Embedding.tendsto_eLpNorm_normed_convolution_sub (μ := μ) one_le_two ENNReal.ofNat_ne_top hw
        (φ := ρ) (l := atTop) (tendsto_rOut_mollifier hδ)) (fun _ => zero_le) fun n => ?_
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (Embedding.tendsto_eLpNorm_normed_convolution_sub (μ := μ) one_le_two ENNReal.ofNat_ne_top hGm
        (φ := ρ) (l := atTop) (tendsto_rOut_mollifier hδ)) (fun _ => zero_le) fun n => ?_
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
      (eLpNorm_mono_ae (((continuous_gradient_of_mem (hmem n)).aestronglyMeasurable).sub
        hg.aestronglyMeasurable) (Eventually.of_forall fun y => le_of_eq ?_))
    simp only [Pi.sub_apply, gradient, hfd]
    have hy : (InnerProductSpace.toDual ℝ E).symm (innerSL ℝ (g y)) = g y :=
      (InnerProductSpace.toDual ℝ E).symm_apply_apply (g y)
    conv_lhs => rw [← hy]
    rw [← map_sub, LinearIsometryEquiv.norm_map]

/-- **The gradient vanishes on level sets** (Gilbarg and Trudinger Lemma 7.7). The gradient part
of an element of `W^{1,2}(Ω)` vanishes almost everywhere on every level set of its function part. -/
theorem ae_gradL_eq_zero_of_fnL_eq (hΩ : IsOpen Ω) {U : H1Graph μ Ω} (hU : U ∈ W12 μ Ω)
    (c : ℝ) : ∀ᵐ x ∂(μ.restrict Ω), fnL U x = c → gradL U x = 0 := by
  filter_upwards [((mem_W12_iff_hasWeakFDerivOn hΩ U).1 hU).ae_eq_zero_of_eq_const c] with x hx hxc
  exact norm_eq_zero.1 (by rw [← innerSL_apply_norm ℝ, hx hxc, norm_zero])

omit [FiniteDimensional ℝ E] [BorelSpace E] [MeasurableSpace E] in
/-- The truncation `max (φ - k) 0` of a test function of `Ω` has compact support in `Ω`. -/
lemma hasCompactSupport_posPart_sub_const {φ : E → ℝ} (h : φ ∈ testFunctions Ω) {k : ℝ}
    (hk : 0 ≤ k) :
    HasCompactSupport (fun x => max (φ x - k) 0) ∧ tsupport (fun x => max (φ x - k) 0) ⊆ Ω := by
  have hsub : tsupport (fun x => max (φ x - k) 0) ⊆ tsupport φ :=
    closure_minimal (fun x hx => subset_tsupport _ fun h0 => Function.mem_support.mp hx (by
      simp only [h0, zero_sub]; exact max_eq_right (neg_nonpos.mpr hk))) (isClosed_tsupport _)
  exact ⟨h.2.1.of_isClosed_subset (isClosed_tsupport _) hsub, hsub.trans h.2.2⟩

/-- **Truncation in `H₀¹`.** For `V ∈ H₀¹(μ, Ω)` and `k ≥ 0` there is `W ∈ H₀¹(μ, Ω)` whose
function part is `(v - k)⁺` and whose gradient part is that of `V` on `{v > k}` and zero
elsewhere. -/
theorem exists_mem_H01_posPart_sub_const (hΩ : IsOpen Ω) {V : H1Graph μ Ω} (hV : V ∈ H01 μ Ω)
    {k : ℝ} (hk : 0 ≤ k) :
    ∃ W ∈ H01 μ Ω, ⇑(fnL W) =ᵐ[μ.restrict Ω] (fun x => max (fnL V x - k) 0) ∧
      ⇑(gradL W) =ᵐ[μ.restrict Ω] fun x => if k < fnL V x then gradL V x else 0 := by
  classical
  obtain ⟨φ, hφ⟩ := exists_seq_testGraphₗ_tendsto hV
  obtain ⟨hX0, hXg⟩ := tendsto_iff.1 hφ
  set v : E → ℝ := ⇑(fnL V) with hvdef
  set g : E → E := ⇑(gradL V) with hgdef
  have hvm : MemLp v 2 (μ.restrict Ω) := Lp.memLp _
  have hgm : MemLp g 2 (μ.restrict Ω) := Lp.memLp _
  -- the approximants
  set ψ : ℕ → E → ℝ := fun n => (φ n : E → ℝ) with hψdef
  have hψ : ∀ n, ψ n ∈ testFunctions Ω := fun n => (φ n).2
  have hψc : ∀ n, Continuous (ψ n) := fun n => (hψ n).1.continuous
  have hX0' : Tendsto (fun n => eLpNorm (ψ n - v) 2 (μ.restrict Ω)) atTop (𝓝 0) :=
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hX0).congr fun n =>
      eLpNorm_congr_ae ((coeFn_fnL_testGraphₗ (φ n)).sub EventuallyEq.rfl)
  have hXg' : Tendsto (fun n => eLpNorm (gradient (ψ n) - g) 2 (μ.restrict Ω)) atTop (𝓝 0) :=
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hXg).congr fun n =>
      eLpNorm_congr_ae ((coeFn_gradL_testGraphₗ (φ n)).sub EventuallyEq.rfl)
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hX0').exists_seq_tendsto_ae
  -- the level sets of `v` carry no gradient
  have hlev : ∀ᵐ x ∂(μ.restrict Ω), v x = k → g x = 0 :=
    ae_gradL_eq_zero_of_fnL_eq hΩ (H01_le_W12 hV) k
  -- the truncations of the approximants lie in `H₀¹`
  set T : ℕ → E → ℝ := fun i x => max (ψ (ns i) x - k) 0 with hTdef
  set D : ℕ → E → E := fun i x => if k < ψ (ns i) x then gradient (ψ (ns i)) x else 0 with hDdef
  have hTm : ∀ i, MemLp (T i) 2 μ := fun i =>
    (((hψc _).sub continuous_const).max continuous_const).memLp_of_hasCompactSupport
      (hasCompactSupport_posPart_sub_const (hψ _) hk).1
  have hDm : ∀ i, MemLp (D i) 2 μ := fun i =>
    memLp_ite_lt_vec ((hψc _).memLp_of_hasCompactSupport (hψ _).2.1)
      ((continuous_gradient_of_mem (hψ _)).memLp_of_hasCompactSupport
        (hasCompactSupport_gradient_of_mem (hψ _))) k
  have hTwg : ∀ i, HasWeakFDerivOn ⊤ (T i) (fun x => innerSL ℝ (D i x)) μ := fun i => by
    have h := ((hasWeakFDerivOn_fderiv (Ω := (⊤ : Opens E)) (μ := μ) (u := ψ (ns i))
      ((hψ _).1.of_le (by exact_mod_cast le_top)).contDiffOn).sub_const k).posPart
    refine h.congr_ae EventuallyEq.rfl (Eventually.of_forall fun x => ?_)
    simp only [hDdef, sub_pos]
    split_ifs
    · exact ((InnerProductSpace.toDual ℝ E).apply_symm_apply _).symm
    · simp
  have hWmem : ∀ i, mk ((hTm i).mono_measure Measure.restrict_le_self |>.toLp (T i))
      ((hDm i).mono_measure Measure.restrict_le_self |>.toLp (D i)) ∈ H01 μ Ω := fun i =>
    mem_H01_of_hasCompactSupport hΩ (hTwg i) (hTm i) (hDm i)
      (hasCompactSupport_posPart_sub_const (hψ _) hk).1
      (hasCompactSupport_posPart_sub_const (hψ _) hk).2
  -- the limit
  have hwlim := memLp_max_sub_const hvm hk
  have hhlim := memLp_ite_lt_vec hvm hgm k
  refine ⟨mk (hwlim.toLp _) (hhlim.toLp _), ?_, by simpa using hwlim.coeFn_toLp,
    by simpa using hhlim.coeFn_toLp⟩
  refine isClosed_H01.mem_of_tendsto (b := atTop) ?_ (Eventually.of_forall hWmem)
  refine tendsto_mk_of_tendsto_eLpNorm hwlim hhlim (f := T) (g := D) (fun i => ?_)
    (fun i => ?_) ?_ ?_
  · rw [fnL_mk]
    exact ((hTm i).mono_measure Measure.restrict_le_self).coeFn_toLp
  · rw [gradL_mk]
    exact ((hDm i).mono_measure Measure.restrict_le_self).coeFn_toLp
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hX0'.comp hns.tendsto_atTop) (fun _ => zero_le) fun i => ?_
    refine eLpNorm_mono_ae ((((hψc _).sub continuous_const).max
      continuous_const).aestronglyMeasurable.sub hwlim.aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, Real.norm_eq_abs, hTdef]
    exact abs_max_sub_le _ _ _
  · exact tendsto_eLpNorm_ite_lt_sub (fun i => (hψc (ns i)).aestronglyMeasurable)
      (fun i => (continuous_gradient_of_mem (hψ (ns i))).aestronglyMeasurable)
      hvm.aestronglyMeasurable hgm (hXg'.comp hns.tendsto_atTop) hae hlev

end H1Graph

end EllipticPdes
