/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.H01Sobolev
public import EllipticPdes.Embedding.H01SobolevTwo
public import EllipticPdes.Existence.DivFormMaximum
public import EllipticPdes.Sobolev.GraphEuclidean
public import EllipticPdes.Sobolev.GraphIsometry
public import EllipticPdes.Sobolev.GraphLattice

/-!
# Weak maximum principle with a transport term, over a finite-dimensional inner product space

Gilbarg and Trudinger's Theorem 8.1 with the transport term present, in dimension at least
two. The transport-free case tests the subsolution inequality against `(u - k)⁺` and finds the
energy of the truncation nonpositive. With a transport term the energy is bounded by the
transport coefficient times the gradient norm of the truncation times its `L²` norm over the
set `Γ_k` where `u > k` and the gradient does not vanish. Ellipticity, a Sobolev inequality on
`H₀¹` at an exponent above `2`, which is the critical one in dimension at least three and the
embedding into `L⁴` in dimension two, and Hölder's inequality then bound the measure of `Γ_k`
below by a constant independent of `k`, at every level whose superlevel set has positive
measure.

The bound is contradicted as `k` increases to the supremum `T` of the levels at which the
superlevel set has positive measure: the sets `Γ_k` decrease to a subset of `{u ≥ T}` on which
the gradient does not vanish, and this set is null because `{u > T}` is null by the choice of
`T` and the gradient vanishes almost everywhere on `{u = T}`. So no level above the boundary
value has a nonzero truncation, which is the conclusion.

The membership of `(u - k)⁺` in `H₀¹(μ, Ω)` for every `k` above the boundary value comes from
the truncation lemma of `EllipticPdes.H1Graph.exists_mem_H01_posPart_sub_const`. The Sobolev
inequality over a general space is the coordinate one transported along an isometry
`E ≃ₗᵢ ℝⁿ` (`EllipticPdes.H1Graph.mapIsometry`).

## Main declarations

* `EllipticPdes.H1Graph.exists_truncation_mem_H01`: the truncations at every level above the
  boundary value are in `H₀¹`.
* `EllipticPdes.H1Graph.exists_eLpNorm_le_of_mem_H01`: the Sobolev inequality on `H₀¹` of a
  bounded set, in dimension at least two.
* `EllipticPdes.DivForm.FullEllipticOp.weak_maximum_principle_transport_of_sobolev`: the
  principle given a Sobolev inequality at an exponent above `2`.
* `EllipticPdes.DivForm.FullEllipticOp.weak_maximum_principle_transport`: the weak maximum
  principle with a transport term, in dimension at least two.

## References

D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§8.1 Theorem 8.1 (pp. 179–180).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace EllipticPdes

set_option linter.unusedSectionVars false

section Tail

variable {α F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup F]
  [MeasurableSpace F] [BorelSpace F]

/-! ### The set where the truncation has nonvanishing gradient -/

/-- The set where `u > k` and the gradient does not vanish. -/
def truncSupport (u : α → ℝ) (g : α → F)
    (k : ℝ) : Set α :=
  {x | k < u x ∧ g x ≠ 0}

/-- The set is measurable when the functions are. -/
theorem measurableSet_truncSupport {u : α → ℝ} {g : α → F} (hu : Measurable u) (hg : Measurable g)
    (k : ℝ) : MeasurableSet (truncSupport u g k) := by
  exact (measurableSet_lt measurable_const hu).inter (hg (measurableSet_singleton 0).compl)

omit [MeasurableSpace α] [MeasurableSpace F] [BorelSpace F] in
/-- The set is antitone in the level. -/
theorem truncSupport_antitone (u : α → ℝ) (g : α → F) : Antitone (truncSupport u g) :=
  fun _ _ hst _ hx => ⟨lt_of_le_of_lt hst hx.1, hx.2⟩

omit [MeasurableSpace α] [MeasurableSpace F] [BorelSpace F] in
/-- The set lies in the superlevel set. -/
theorem truncSupport_subset (u : α → ℝ) (g : α → F) (k : ℝ) :
    truncSupport u g k ⊆ {x | k < u x} := fun _ hx => hx.1

/-! ### The tail of the argument -/

/-- On a finite measure space the superlevel sets `{u > N}` of a real function have arbitrarily
small measure for large `N`. -/
theorem exists_nat_measure_superlevel_lt [IsFiniteMeasure μ] {u : α → ℝ} (hu : Measurable u)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, μ {x | (N : ℝ) < u x} < ε := by
  have hshrink : Tendsto (fun n : ℕ => μ {x | (n : ℝ) < u x}) atTop
      (𝓝 (μ (⋂ n : ℕ, {x | (n : ℝ) < u x}))) :=
    tendsto_measure_iInter_atTop (fun n => (measurableSet_lt measurable_const hu).nullMeasurableSet)
      (fun m n hmn x (hx : (n : ℝ) < u x) => lt_of_le_of_lt (Nat.cast_le.mpr hmn) hx)
      ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ n : ℕ, {x | (n : ℝ) < u x}) = ∅ := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
    obtain ⟨n, hn⟩ := exists_nat_gt (u x)
    exact ⟨n, hn.le⟩
  rw [hempty, measure_empty] at hshrink
  exact (hshrink.eventually (gt_mem_nhds hε)).exists

/-- If every `Γ_t` with `k₀ ≤ t < T` has measure at least `c`, then so does the intersection of
`{u ≥ T}` with the set where the gradient is nonzero: the sets `Γ_t` decrease to it as
`t ↑ T`. -/
theorem le_measure_superlevel_inter_of_levels [IsFiniteMeasure μ] {u : α → ℝ} {g : α → F}
    (hu : Measurable u) (hg : Measurable g)
    {c k₀ T : ℝ} (hTk : k₀ < T)
    (hbelow : ∀ t, k₀ ≤ t → t < T → ENNReal.ofReal c ≤ μ (truncSupport u g t)) :
    ENNReal.ofReal c ≤ μ ({x | T ≤ u x} ∩ {x | g x ≠ 0}) := by
  set t : ℕ → ℝ := fun n => max k₀ (T - 1 / (n + 1 : ℝ)) with htdef
  have ht_lt : ∀ n, t n < T := fun n =>
    max_lt hTk (by linarith [(by positivity : (0 : ℝ) < 1 / (n + 1 : ℝ))])
  have ht_ge : ∀ n, k₀ ≤ t n := fun n => le_max_left _ _
  have ht_mono : Monotone t := fun m n hmn => max_le_max le_rfl (by
    have : (1 : ℝ) / (n + 1) ≤ 1 / (m + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn)
    linarith)
  have ht_lim : Tendsto t atTop (𝓝 T) := by
    have h1 : Tendsto (fun n : ℕ => T - 1 / (n + 1 : ℝ)) atTop (𝓝 (T - 0)) :=
      tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
    rw [sub_zero] at h1
    have h2 := ((continuous_const.max continuous_id : Continuous fun s : ℝ => max k₀ s).tendsto
      T).comp h1
    simpa only [Function.comp_def, max_eq_right hTk.le] using h2
  have hlim := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => (measurableSet_truncSupport hu hg (t n)).nullMeasurableSet)
    (fun m n hmn => truncSupport_antitone u g (ht_mono hmn)) ⟨0, measure_ne_top μ _⟩
  have hge : ENNReal.ofReal c ≤ μ (⋂ n, truncSupport u g (t n)) :=
    ge_of_tendsto' hlim fun n => hbelow (t n) (ht_ge n) (ht_lt n)
  refine hge.trans (measure_mono fun x hx => ?_)
  rw [mem_iInter] at hx
  exact ⟨le_of_tendsto' ht_lim fun n => (hx n).1.le, (hx 0).2⟩

/-- The superlevel set of `T` is null when the superlevel sets of `T + 1 / (n + 1)` are. -/
theorem measure_superlevel_eq_zero_of_forall_add_inv {μ : Measure α} {u : α → ℝ} {T : ℝ}
    (h : ∀ n : ℕ, μ {x | T + 1 / (n + 1 : ℝ) < u x} = 0) : μ {x | T < u x} = 0 := by
  have hcover : {x | T < u x} = ⋃ n : ℕ, {x | T + 1 / (n + 1 : ℝ) < u x} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
      linarith
  rw [hcover]
  exact measure_iUnion_null h

/-- If the superlevel set of `T` is null and `g` vanishes almost everywhere on the level set of
`T`, then `g` is zero almost everywhere on `{T ≤ u}`. -/
theorem measure_superlevel_inter_eq_zero {μ : Measure α} {u : α → ℝ} {g : α → F} {T : ℝ}
    (hT : μ {x | T < u x} = 0) (hlevel : ∀ᵐ x ∂μ, u x = T → g x = 0) :
    μ ({x | T ≤ u x} ∩ {x | g x ≠ 0}) = 0 := by
  have hlevelnull : μ ({x | u x = T} ∩ {x | g x ≠ 0}) = 0 :=
    measure_mono_null (fun x (hx : u x = T ∧ g x ≠ 0) =>
      show ¬(u x = T → g x = 0) from fun h => hx.2 (h hx.1)) (ae_iff.mp hlevel)
  refine measure_mono_null (fun x hx => ?_) (measure_union_null hT hlevelnull)
  have hx1 : T ≤ u x := hx.1
  rcases lt_or_eq_of_le hx1 with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.symm, hx.2⟩

/-- **Impossibility of a uniform lower bound on the measure of `Γ_k`.** If the measure of `Γ_k`
is at least `c > 0` at every level `k ≥ k₀` whose superlevel set has positive measure, and the
gradient vanishes almost everywhere on every level set, then the superlevel set of `k₀` is
null. -/
theorem measure_superlevel_eq_zero {μ : Measure α} [IsFiniteMeasure μ]
    {u : α → ℝ} {g : α → F}
    (hu : Measurable u) (hg : Measurable g)
    (hlevel : ∀ T : ℝ, ∀ᵐ x ∂μ, u x = T → g x = 0)
    {c : ℝ} (hc : 0 < c) {k₀ : ℝ}
    (hest : ∀ k, k₀ ≤ k → 0 < μ {x | k < u x} → c ≤ (μ (truncSupport u g k)).toReal) :
    μ {x | k₀ < u x} = 0 := by
  by_contra hpos
  replace hpos : 0 < μ {x | k₀ < u x} := pos_iff_ne_zero.mpr hpos
  have hsup_meas : ∀ t : ℝ, MeasurableSet {x | t < u x} := fun t =>
    measurableSet_lt measurable_const hu
  have hΓm : ∀ t, MeasurableSet (truncSupport u g t) := measurableSet_truncSupport hu hg
  -- the superlevel sets of `n` shrink to nothing, so some has measure below `c`
  obtain ⟨N, hN⟩ := exists_nat_measure_superlevel_lt (μ := μ) hu (ENNReal.ofReal_pos.mpr hc)
  -- the levels with a nonzero truncation
  set S : Set ℝ := {t | k₀ ≤ t ∧ 0 < μ {x | t < u x}} with hSdef
  have hk₀S : k₀ ∈ S := ⟨le_rfl, hpos⟩
  have hSbdd : BddAbove S := by
    refine ⟨N, fun t ht => ?_⟩
    by_contra hlt
    have h1 : μ {x | t < u x} ≤ μ {x | (N : ℝ) < u x} :=
      measure_mono fun x hx => lt_trans (not_le.mp hlt) hx
    have h2 : c ≤ (μ (truncSupport u g t)).toReal := hest t ht.1 ht.2
    have h3 : (μ (truncSupport u g t)).toReal ≤ (μ {x | t < u x}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (truncSupport_subset u g t))
    have h4 : (μ {x | t < u x}).toReal < c := by
      rw [← ENNReal.toReal_ofReal hc.le]
      exact ENNReal.toReal_strict_mono ENNReal.ofReal_ne_top (lt_of_le_of_lt h1 hN)
    linarith
  set T : ℝ := sSup S with hTdef
  have hk₀T : k₀ ≤ T := le_csSup hSbdd hk₀S
  -- the superlevel set of `T` is null
  have hTnull : μ {x | T < u x} = 0 := by
    refine measure_superlevel_eq_zero_of_forall_add_inv fun n => ?_
    by_contra hne
    have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    have := le_csSup hSbdd (show T + 1 / (n + 1 : ℝ) ∈ S from
      ⟨by linarith, pos_iff_ne_zero.mpr hne⟩)
    linarith
  -- the sets `Γ_t` for `t < T` have measure at least `c`, and shrink into the level set
  have hbelow : ∀ t, k₀ ≤ t → t < T → ENNReal.ofReal c ≤ μ (truncSupport u g t) := by
    intro t hk₀t htT
    obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup ⟨k₀, hk₀S⟩ htT
    have hpos' : 0 < μ {x | t < u x} :=
      lt_of_lt_of_le hs.2 (measure_mono fun x hx => lt_trans hts hx)
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr (hest t hk₀t hpos')
  have hkey : ENNReal.ofReal c ≤ μ ({x | T ≤ u x} ∩ {x | g x ≠ 0}) := by
    rcases eq_or_lt_of_le hk₀T with hTk | hTk
    · -- the supremum is the boundary level itself
      refine le_trans ((ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr
        (hest k₀ le_rfl hpos)) (measure_mono fun x hx => ⟨?_, hx.2⟩)
      rw [← hTk]
      exact hx.1.le
    · exact le_measure_superlevel_inter_of_levels hu hg hTk hbelow
  have hzero := measure_superlevel_inter_eq_zero hTnull (hlevel T)
  rw [hzero] at hkey
  exact absurd hkey (not_le.mpr (ENNReal.ofReal_pos.mpr hc))


end Tail

/-! ### Hölder's inequality and the level sets -/

/-- **Hölder's inequality on a subset.** For `q ≥ 2` and a finite measure, the `L²` norm of a
function over `Γ` is at most its `Lᵠ` norm times `μ(Γ)^{1/2 - 1/q}`. -/
theorem toReal_eLpNorm_restrict_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : AEStronglyMeasurable f μ) {q : ℝ≥0} (hq : 2 ≤ q)
    (hfin : eLpNorm f q μ ≠ ⊤) (Γ : Set α) :
    (eLpNorm f 2 (μ.restrict Γ)).toReal
      ≤ (eLpNorm f q μ).toReal * (μ Γ).toReal ^ (1 / 2 - 1 / (q : ℝ)) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hθ : 0 ≤ 1 / 2 - 1 / (q : ℝ) := by
    have := one_div_le_one_div_of_le (by norm_num) hq'
    linarith
  have h2q : (2 : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by exact_mod_cast hq
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict Γ) h2q
    (hf.mono_measure Measure.restrict_le_self)
  have hres : eLpNorm f q (μ.restrict Γ) ≤ eLpNorm f q μ :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  have hθ' : 0 ≤ 1 / (2 : ℝ≥0∞).toReal - 1 / (q : ℝ≥0∞).toReal := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.coe_toReal] using hθ
  have hfin' : eLpNorm f q (μ.restrict Γ)
      * (μ.restrict Γ) univ ^ (1 / (2 : ℝ≥0∞).toReal - 1 / (q : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (ne_top_of_le_ne_top hfin hres)
      (ENNReal.rpow_ne_top_of_nonneg hθ' (measure_ne_top _ _))
  have h2 := ENNReal.toReal_mono hfin' h1
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Measure.restrict_apply_univ,
    ENNReal.toReal_ofNat, ENNReal.coe_toReal] at h2
  exact h2.trans (mul_le_mul_of_nonneg_right (ENNReal.toReal_mono hfin hres)
    (Real.rpow_nonneg ENNReal.toReal_nonneg _))

/-- Inverting `1 ≤ K γ^θ`: `K⁻¹^{1/θ} ≤ γ`. -/
theorem inv_rpow_inv_le_of_one_le_mul_rpow {K γ θ : ℝ} (hK : 0 < K) (hγ : 0 ≤ γ) (hθ : 0 < θ)
    (h : 1 ≤ K * γ ^ θ) : K⁻¹ ^ θ⁻¹ ≤ γ := by
  have hinv : K⁻¹ ≤ γ ^ θ := by
    rw [inv_le_iff_one_le_mul₀' hK]
    exact h
  calc K⁻¹ ^ θ⁻¹ ≤ (γ ^ θ) ^ θ⁻¹ :=
        Real.rpow_le_rpow (inv_nonneg.mpr hK.le) hinv (inv_nonneg.mpr hθ.le)
    _ = γ := Real.rpow_rpow_inv hγ hθ.ne'

/-- A function equal to `(u - k)⁺` that vanishes in `Lᵠ` forces the superlevel set `{u > k}` to
be null. -/
theorem measure_superlevel_eq_zero_of_eLpNorm_eq_zero {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f u : α → ℝ} {k : ℝ} {q : ℝ≥0∞} (hq : q ≠ 0)
    (hf : f =ᵐ[μ] fun x => max (u x - k) 0) (h0 : eLpNorm f q μ = 0) : μ {x | k < u x} = 0 := by
  have hae := (eLpNorm_eq_zero_iff hq).mp h0
  have hle : ∀ᵐ x ∂μ, u x ≤ k := by
    filter_upwards [hae, hf] with x hx hx0
    simp only [Pi.zero_apply] at hx
    rw [hx0] at hx
    by_contra hlt
    rw [max_eq_left (by linarith [not_le.mp hlt])] at hx
    linarith [not_le.mp hlt]
  simpa only [not_le] using ae_iff.mp hle

/-! ### The energy estimate -/

section Graph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

open H1Graph

/-- Truncating twice is truncating once. -/
theorem max_max_sub_eq {a k₀ k : ℝ} (hk : k₀ ≤ k) :
    max (max (a - k₀) 0 - (k - k₀)) 0 = max (a - k) 0 := by
  simp only [max_def]
  split_ifs <;> linarith

/-- The indicator of the second truncation is the indicator of `{k < a}`. -/
theorem ite_lt_max_sub {F : Type*} [Zero F] {k₀ k : ℝ} (hk : k₀ ≤ k) (a : ℝ) (b : F) :
    (if k - k₀ < max (a - k₀) 0 then (if k₀ < a then b else 0) else 0)
      = if k < a then b else 0 := by
  simp only [max_def]
  split_ifs <;> first | rfl | (exfalso; linarith)

namespace H1Graph

/-- **Truncations at every level above the boundary value in `H₀¹`.** If `(u - k₀)⁺` is the
function part of an element of `H₀¹(μ, Ω)`, then for every `k ≥ k₀` there is an element of
`H₀¹(μ, Ω)` with function part `(u - k)⁺` and gradient part that of `u` on `{u > k}` and zero
elsewhere. -/
theorem exists_truncation_mem_H01 (hΩ : IsOpen Ω) {U : H1Graph μ Ω} (hU : U ∈ W12 μ Ω)
    {k₀ : ℝ} {V₀ : H01 μ Ω}
    (hV₀ : ⇑(fnL (V₀ : H1Graph μ Ω)) =ᵐ[μ.restrict Ω] fun x => max (fnL U x - k₀) 0)
    {k : ℝ} (hk : k₀ ≤ k) :
    ∃ V : H01 μ Ω, ⇑(fnL (V : H1Graph μ Ω)) =ᵐ[μ.restrict Ω] (fun x => max (fnL U x - k) 0) ∧
      ⇑(gradL (V : H1Graph μ Ω)) =ᵐ[μ.restrict Ω]
        fun x => if k < fnL U x then gradL U x else 0 := by
  obtain ⟨W, hW, hW0, hWg⟩ := exists_mem_H01_posPart_sub_const hΩ V₀.2 (sub_nonneg.mpr hk)
  have hV₀g := gradL_eq_ite_of_fnL_eq_max hΩ hU (H01_le_W12 V₀.2) hV₀
  refine ⟨⟨W, hW⟩, ?_, ?_⟩
  · filter_upwards [hW0, hV₀] with x h1 h2
    rw [h1, h2]
    exact max_max_sub_eq hk
  · filter_upwards [hWg, hV₀, hV₀g] with x h1 h2 h3
    rw [h1, h2, h3]
    exact ite_lt_max_sub hk _ _

end H1Graph

namespace DivForm.FullEllipticOp

variable (Op : FullEllipticOp μ)

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] [BorelSpace E] in
/-- The transport pairing of a gradient class with a function class is the integral of the
pointwise pairing. -/
theorem inner_bAct_eq_integral (g : Lp E 2 (μ.restrict Ω)) (v : Lp ℝ 2 (μ.restrict Ω)) :
    ⟪Op.bAct Ω g, v⟫ = ∫ x, ⟪Op.b x, g x⟫ * v x ∂(μ.restrict Ω) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Op.coeFn_bAct Ω g] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] [BorelSpace E] in
/-- The pointwise transport pairing of a gradient class with a function class is integrable. -/
theorem integrable_inner_bAct (g : Lp E 2 (μ.restrict Ω)) (v : Lp ℝ 2 (μ.restrict Ω)) :
    Integrable (fun x => ⟪Op.b x, g x⟫ * v x) (μ.restrict Ω) := by
  refine (L2.integrable_inner (Op.bAct Ω g) v).congr ?_
  filter_upwards [Op.coeFn_bAct Ω g] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- **The transport term against the truncation.** For `V` with function part the truncation
`(u - k)⁺` and gradient part that of `u` on `{u > k}`, `⟪b · ∇u, v⟫` is at least minus the
transport bound times `‖∇v‖` times the `L²` norm of the truncation over `Γ_k`: where `∇u ≠ 0`
and `v ≠ 0` the point lies in `Γ_k`. -/
theorem neg_mul_le_inner_bAct_truncation {U V : H1Graph μ Ω} {k : ℝ}
    (hV0 : ⇑(fnL V) =ᵐ[μ.restrict Ω] fun x => max (fnL U x - k) 0)
    (hVg : ⇑(gradL V) =ᵐ[μ.restrict Ω] fun x => if k < fnL U x then gradL U x else 0) :
    -(Op.Bsup * (‖gradL V‖ * (eLpNorm (⇑(fnL V)) 2 ((μ.restrict Ω).restrict
      (truncSupport (⇑(fnL U)) (⇑(gradL U)) k))).toReal))
      ≤ ⟪Op.bAct Ω (gradL U), fnL V⟫ := by
  classical
  set ν : Measure E := μ.restrict Ω with hν
  set Γ := truncSupport (⇑(fnL U)) (⇑(gradL U)) k with hΓdef
  have hum : Measurable ⇑(fnL U) := (Lp.stronglyMeasurable _).measurable
  have hgm : Measurable ⇑(gradL U) := (Lp.stronglyMeasurable _).measurable
  have hΓ : MeasurableSet Γ := measurableSet_truncSupport hum hgm k
  set vΓ : E → ℝ := Γ.indicator ⇑(fnL V) with hvΓdef
  have hvΓm : MemLp vΓ 2 ν := (Lp.memLp _).indicator hΓ
  have hnormΓ : (eLpNorm vΓ 2 ν).toReal = (eLpNorm (⇑(fnL V)) 2 (ν.restrict Γ)).toReal := by
    rw [hvΓdef, eLpNorm_indicator_eq_eLpNorm_restrict hΓ]
  -- the classes `‖∇v‖` and `|v 1_Γ|`
  set A : Lp ℝ 2 ν := (Lp.memLp (gradL V)).norm.toLp _ with hAdef
  set B : Lp ℝ 2 ν := hvΓm.norm.toLp _ with hBdef
  have hA : ‖A‖ = ‖gradL V‖ := by
    rw [hAdef, Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable _), Lp.norm_def]
  have hB : ‖B‖ = (eLpNorm (⇑(fnL V)) 2 (ν.restrict Γ)).toReal := by
    rw [hBdef, Lp.norm_toLp, eLpNorm_norm _ hvΓm.aestronglyMeasurable, hnormΓ]
  have hAB : ⟪A, B⟫ = ∫ x, ‖gradL V x‖ * ‖vΓ x‖ ∂ν := by
    rw [hAdef, hBdef, inner_toLp_toLp]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hbint := inner_bAct_eq_integral Op (gradL U) (fnL V)
  have hint1 := integrable_inner_bAct Op (gradL U) (fnL V)
  have hint2 : Integrable (fun x => ‖gradL V x‖ * ‖vΓ x‖) ν := by
    refine (L2.integrable_inner A B).congr ?_
    filter_upwards [(Lp.memLp (gradL V)).norm.coeFn_toLp, hvΓm.norm.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hpt : ∀ᵐ x ∂ν, -(Op.Bsup * (‖gradL V x‖ * ‖vΓ x‖))
      ≤ ⟪Op.b x, gradL U x⟫ * fnL V x := by
    filter_upwards [ae_restrict_of_ae Op.norm_b_le, hV0, hVg] with x hbx hx0 hxg
    -- the product `⟪b, ∇u⟫ v` is `⟪b, ∇v⟫ (v 1_Γ)`
    have hprod : ⟪Op.b x, gradL U x⟫ * fnL V x = ⟪Op.b x, gradL V x⟫ * vΓ x := by
      rw [hxg, hvΓdef, Set.indicator_apply, hx0]
      by_cases hxk : k < fnL U x
      · simp only [hxk, ite_true]
        by_cases hxΓ : x ∈ Γ
        · simp only [hxΓ, ite_true]
        · have h0 : gradL U x = 0 := by
            by_contra hne
            exact hxΓ ⟨hxk, hne⟩
          simp [h0]
      · have hle : fnL U x ≤ k := not_lt.mp hxk
        simp [hxk, max_eq_right (by linarith : fnL U x - k ≤ 0)]
    rw [hprod]
    have habs : |⟪Op.b x, gradL V x⟫ * vΓ x| ≤ Op.Bsup * (‖gradL V x‖ * ‖vΓ x‖) := by
      rw [abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
      calc ‖⟪Op.b x, gradL V x⟫‖ * ‖vΓ x‖ ≤ (Op.Bsup * ‖gradL V x‖) * ‖vΓ x‖ := by
            gcongr
            exact (norm_inner_le_norm _ _).trans (by gcongr)
        _ = _ := by ring
    linarith [neg_abs_le (⟪Op.b x, gradL V x⟫ * vΓ x)]
  calc -(Op.Bsup * (‖gradL V‖ * (eLpNorm (⇑(fnL V)) 2 (ν.restrict Γ)).toReal))
      = -(Op.Bsup * ⟪A, B⟫) + -(Op.Bsup * (‖A‖ * ‖B‖ - ⟪A, B⟫)) := by rw [hA, hB]; ring
    _ ≤ -(Op.Bsup * ⟪A, B⟫) := by
        have : 0 ≤ ‖A‖ * ‖B‖ - ⟪A, B⟫ := sub_nonneg.mpr (real_inner_le_norm A B)
        nlinarith [Op.Bsup_nonneg]
    _ = ∫ x, -(Op.Bsup * (‖gradL V x‖ * ‖vΓ x‖)) ∂ν := by
        rw [hAB, integral_neg, integral_const_mul]
    _ ≤ ∫ x, ⟪Op.b x, gradL U x⟫ * fnL V x ∂ν :=
        integral_mono_ae ((hint2.const_mul _).neg) hint1 hpt
    _ = _ := hbint.symm

/-- **Energy estimate from testing with the truncation.** For a subsolution `U` and an element
`V` of `H₀¹(μ, Ω)` whose parts are the truncation `(u - k)⁺` and its gradient, ellipticity times
the squared gradient norm of `V` is at most the transport bound times the gradient norm times
the `L²` norm of the truncation over `Γ_k`. -/
theorem energy_le_transport (hΩ : IsOpen Ω) (hc : ∀ᵐ x ∂μ, 0 ≤ Op.c x) {U : H1Graph μ Ω}
    (hU : U ∈ W12 μ Ω)
    (hsub : ∀ V : H01 μ Ω, (∀ᵐ x ∂(μ.restrict Ω), 0 ≤ fnL (V : H1Graph μ Ω) x) →
      Op.form Ω U V ≤ 0)
    {k : ℝ} (hk : 0 ≤ k) (V : H01 μ Ω)
    (hV0 : ⇑(fnL (V : H1Graph μ Ω)) =ᵐ[μ.restrict Ω] fun x => max (fnL U x - k) 0)
    (hVg : ⇑(gradL (V : H1Graph μ Ω)) =ᵐ[μ.restrict Ω]
      fun x => if k < fnL U x then gradL U x else 0) :
    Op.lam * ‖gradL (V : H1Graph μ Ω)‖ ^ 2 ≤ Op.Bsup * ‖gradL (V : H1Graph μ Ω)‖
      * (eLpNorm (⇑(fnL (V : H1Graph μ Ω))) 2 ((μ.restrict Ω).restrict
        (truncSupport (⇑(fnL U)) (⇑(gradL U)) k))).toReal := by
  have hVnn : ∀ᵐ x ∂(μ.restrict Ω), 0 ≤ fnL (V : H1Graph μ Ω) x := by
    filter_upwards [hV0] with x hx
    rw [hx]
    exact le_max_right _ _
  have hineq := hsub V hVnn
  rw [form_apply, form_truncation_eq Op hΩ hU (H01_le_W12 V.2) hV0, lowerForm_apply] at hineq
  have hc' := inner_cAct_truncation_nonneg Op hc hk hV0
  have hb' := neg_mul_le_inner_bAct_truncation Op hV0 hVg
  have henergy := Op.toEllipticCoeff.form_self_ge Ω (V : H1Graph μ Ω)
  nlinarith

/-! ### The Sobolev-Hölder lower bound -/

/-- **Bound on the measure of `Γ_k` for a fixed Sobolev exponent.** The conclusion of
`exists_measure_truncSupport_ge_of_sobolev`: for every `V ∈ H₀¹(μ, Ω)` whose function part is
`(u - k)⁺`, with positive superlevel set and the energy estimate, the set `Γ_k` has measure at
least `c`. -/
def TruncSupportBound (Ω : Set E) (Op : FullEllipticOp μ) (c : ℝ) : Prop :=
  ∀ (V : H01 μ Ω) (u : E → ℝ) (g : E → E) (k : ℝ),
    ⇑(fnL (V : H1Graph μ Ω)) =ᵐ[μ.restrict Ω] (fun x => max (u x - k) 0) →
    0 < (μ.restrict Ω) {x | k < u x} →
    Op.lam * ‖gradL (V : H1Graph μ Ω)‖ ^ 2 ≤ Op.Bsup * ‖gradL (V : H1Graph μ Ω)‖
      * (eLpNorm (⇑(fnL (V : H1Graph μ Ω))) 2
        ((μ.restrict Ω).restrict (truncSupport u g k))).toReal →
    c ≤ ((μ.restrict Ω) (truncSupport u g k)).toReal

/-- **Uniform lower bound on the measure of `Γ_k`**, from a Sobolev inequality on `H₀¹(μ, Ω)` at
an exponent above `2`. On a bounded set there is `c > 0`, depending on the operator and the
Sobolev constant alone, such that, whenever the truncation `(u - k)⁺` is the function part of an
element `V` of `H₀¹(μ, Ω)` whose superlevel set has positive measure and satisfies the energy
estimate, the set `Γ_k` has measure at least `c`. -/
theorem exists_measure_truncSupport_ge_of_sobolev (hΩb : Bornology.IsBounded Ω)
    {q : ℝ≥0} (hq2 : 2 < q) {C : ℝ} (hC : 0 ≤ C)
    (hsobolev : ∀ V : H01 μ Ω, MemLp (⇑(fnL (V : H1Graph μ Ω))) q (μ.restrict Ω) ∧
      (eLpNorm (⇑(fnL (V : H1Graph μ Ω))) q (μ.restrict Ω)).toReal ≤
        C * ‖gradL (V : H1Graph μ Ω)‖) :
    ∃ c : ℝ, 0 < c ∧ TruncSupportBound Ω Op c := by
  classical
  have : IsFiniteMeasure (μ.restrict Ω) := isFiniteMeasure_restrict.2 hΩb.measure_lt_top.ne
  set ν : Measure E := μ.restrict Ω with hνdef
  have hq2r : (2 : ℝ) < q := by exact_mod_cast hq2
  set θ : ℝ := 1 / 2 - 1 / (q : ℝ) with hθdef
  have hθpos : 0 < θ := by
    have : 1 / (q : ℝ) < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hq2r
    rw [hθdef]
    linarith
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.coe_ne_zero]
    exact (lt_trans (by norm_num) hq2).ne'
  set K : ℝ := C * (Op.Bsup / Op.lam) + 1 with hKdef
  have hKbase : 0 ≤ C * (Op.Bsup / Op.lam) :=
    mul_nonneg hC (div_nonneg Op.Bsup_nonneg Op.lam_pos.le)
  have hKpos : 0 < K := by linarith
  refine ⟨K⁻¹ ^ θ⁻¹, Real.rpow_pos_of_pos (inv_pos.mpr hKpos) _,
    fun V u g k hV0 hpos henergy => ?_⟩
  set γ : ℝ := (ν (truncSupport u g k)).toReal with hγdef
  have hγ0 : 0 ≤ γ := ENNReal.toReal_nonneg
  obtain ⟨hNm, hN⟩ := hsobolev V
  set N : ℝ := (eLpNorm (⇑(fnL (V : H1Graph μ Ω))) q ν).toReal with hNdef
  have hNfin : eLpNorm (⇑(fnL (V : H1Graph μ Ω))) q ν ≠ ⊤ := hNm.eLpNorm_lt_top.ne
  set G : ℝ := ‖gradL (V : H1Graph μ Ω)‖ with hGdef
  -- the gradient norm is controlled by the `L²` norm of the truncation over `Γ`
  set vΓ : ℝ := (eLpNorm (⇑(fnL (V : H1Graph μ Ω))) 2 (ν.restrict (truncSupport u g k))).toReal
    with hvΓdef
  have hvΓ0 : 0 ≤ vΓ := ENNReal.toReal_nonneg
  have hS : Op.lam * G ≤ Op.Bsup * vΓ := by
    rcases (norm_nonneg (gradL (V : H1Graph μ Ω))).eq_or_lt with hG | hG
    · rw [← hGdef] at hG
      rw [← hG, mul_zero]
      exact mul_nonneg Op.Bsup_nonneg hvΓ0
    · refine le_of_mul_le_mul_right ?_ hG
      calc Op.lam * G * G = Op.lam * G ^ 2 := by ring
        _ ≤ Op.Bsup * G * vΓ := henergy
        _ = Op.Bsup * vΓ * G := by ring
  have hhold : vΓ ≤ N * γ ^ θ :=
    toReal_eLpNorm_restrict_le (Lp.aestronglyMeasurable _) hq2.le hNfin _
  -- the truncation is not zero
  have hNpos : 0 < N := by
    refine (ENNReal.toReal_nonneg : 0 ≤ N).lt_of_ne fun h => hpos.ne' ?_
    refine measure_superlevel_eq_zero_of_eLpNorm_eq_zero hq0 hV0 ?_
    rcases (ENNReal.toReal_eq_zero_iff _).mp h.symm with h0 | htop
    · exact h0
    · exact absurd htop hNfin
  have hchain : N ≤ K * γ ^ θ * N := by
    have hsum : G ≤ Op.Bsup * vΓ / Op.lam := by
      rw [le_div_iff₀ Op.lam_pos]
      linarith [hS]
    calc N ≤ C * G := hN
      _ ≤ C * (Op.Bsup * vΓ / Op.lam) := by gcongr
      _ = C * (Op.Bsup / Op.lam) * vΓ := by ring
      _ ≤ K * (N * γ ^ θ) := by
          refine mul_le_mul (by rw [hKdef]; linarith) hhold hvΓ0 hKpos.le
      _ = K * γ ^ θ * N := by ring
  have hone : 1 ≤ K * γ ^ θ := by
    refine le_of_mul_le_mul_right (a := N) ?_ hNpos
    linarith [hchain]
  exact inv_rpow_inv_le_of_one_le_mul_rpow hKpos hγ0 hθpos hone

/-- **Weak maximum principle with a transport term, given a Sobolev inequality.** Let `Ω` be a
bounded open set, `L` a divergence-form operator with bounded transport term and nonnegative
zeroth-order coefficient, and suppose `H₀¹(μ, Ω)` embeds into `L^q(Ω)` for some `q > 2`, with
`‖v‖_q ≤ C ‖∇v‖₂`. If `U ∈ H¹(Ω)` is a weak subsolution, meaning the bilinear pairing of `U`
against every nonnegative `V ∈ H₀¹(Ω)` is nonpositive, if `k ≥ 0` and if `(u - k)⁺` is the
function part of some element of `H₀¹(Ω)`, then `u ≤ k` almost everywhere on `Ω`. -/
theorem weak_maximum_principle_transport_of_sobolev (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hc : ∀ᵐ x ∂μ, 0 ≤ Op.c x)
    {q : ℝ≥0} (hq2 : 2 < q) {C : ℝ} (hC : 0 ≤ C)
    (hsobolev : ∀ V : H01 μ Ω, MemLp (⇑(fnL (V : H1Graph μ Ω))) q (μ.restrict Ω) ∧
      (eLpNorm (⇑(fnL (V : H1Graph μ Ω))) q (μ.restrict Ω)).toReal ≤
        C * ‖gradL (V : H1Graph μ Ω)‖)
    {U : H1Graph μ Ω} (hU : U ∈ W12 μ Ω)
    (hsub : ∀ V : H01 μ Ω, (∀ᵐ x ∂(μ.restrict Ω), 0 ≤ fnL (V : H1Graph μ Ω) x) →
      Op.form Ω U V ≤ 0)
    {k : ℝ} (hk : 0 ≤ k)
    (hbd : ∃ V : H01 μ Ω, ⇑(fnL (V : H1Graph μ Ω)) =ᵐ[μ.restrict Ω]
      fun x => max (fnL U x - k) 0) :
    ∀ᵐ x ∂(μ.restrict Ω), fnL U x ≤ k := by
  classical
  have : IsFiniteMeasure (μ.restrict Ω) := isFiniteMeasure_restrict.2 hΩb.measure_lt_top.ne
  obtain ⟨V₀, hV₀⟩ := hbd
  have hum : Measurable ⇑(fnL U) := (Lp.stronglyMeasurable _).measurable
  have hgm : Measurable ⇑(gradL U) := (Lp.stronglyMeasurable _).measurable
  obtain ⟨c, hc0, hest⟩ := exists_measure_truncSupport_ge_of_sobolev Op hΩb hq2 hC hsobolev
  have hest' : ∀ k', k ≤ k' → 0 < (μ.restrict Ω) {x | k' < fnL U x} →
      c ≤ ((μ.restrict Ω) (truncSupport (⇑(fnL U)) (⇑(gradL U)) k')).toReal := by
    intro k' hkk' hpos
    obtain ⟨V, hV0, hVg⟩ := exists_truncation_mem_H01 hΩ hU hV₀ hkk'
    exact hest V _ _ k' hV0 hpos
      (energy_le_transport Op hΩ hc hU hsub (hk.trans hkk') V hV0 hVg)
  have hzero := measure_superlevel_eq_zero hum hgm
    (fun T => ae_gradL_eq_zero_of_fnL_eq hΩ hU T) hc0 hest'
  rw [ae_iff]
  simpa only [not_le] using hzero

end DivForm.FullEllipticOp

end Graph

/-! ### The Sobolev inequality on `H₀¹` of a bounded set -/

section SobolevCoordinate

open EllipticPdes.Embedding

/-- **Sobolev inequality on `H₀¹` of a bounded set in coordinates, at an exponent above `2`.**
In dimension at least three the exponent is `2n/(n - 1)`, below the critical one; in dimension
two it is `4`. -/
theorem exists_eLpNorm_le_of_mem_H01_coord {n : ℕ} (hn : 2 ≤ n)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) :
    ∃ q : ℝ≥0, 2 < q ∧ ∃ C : ℝ≥0, ∀ U : Sobolev.H1amb Ω, U ∈ Sobolev.H01 Ω →
      eLpNorm (U 0) q (volume.restrict Ω) ≤ C * ∑ i : Fin n, ‖U i.succ‖ₑ := by
  rcases lt_or_eq_of_le hn with hd | hd
  · have hd3 : (3 : ℝ) ≤ n := by exact_mod_cast hd
    have hd1 : (0 : ℝ) < n - 1 := by linarith
    set q : ℝ≥0 := ⟨2 * n / (n - 1), div_nonneg (by positivity) hd1.le⟩ with hqdef
    have hqcoe : (q : ℝ) = 2 * n / (n - 1) := rfl
    have hqinv : (q : ℝ)⁻¹ = (n - 1) / (2 * n) := by rw [hqcoe, inv_div]
    have hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (n : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ := by
      rw [hqinv]
      have : ((2 : ℝ≥0) : ℝ)⁻¹ - (n : ℝ)⁻¹ = (n - 2) / (2 * n) := by
        push_cast
        field_simp
      rw [this]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    refine ⟨q, ?_, sobolevConstOfLe Ω q, fun U hU => ?_⟩
    · rw [← NNReal.coe_lt_coe, hqcoe, NNReal.coe_ofNat, lt_div_iff₀ hd1]
      linarith
    · exact eLpNorm_le_of_mem_H01_of_isBounded hΩm hΩb hd hq hU
  · subst hd
    refine ⟨4, by norm_num, sobolevConstTwo Ω, fun U hU => ?_⟩
    have h4 : ((4 : ℝ≥0) : ℝ≥0∞) = 4 := by norm_num
    rw [h4]
    exact eLpNorm_le_of_mem_H01_two hΩm hΩb hU

end SobolevCoordinate

namespace H1Graph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Set E}

/-- The sum of the extended norms of a finite family bounded by `G` is at most `n G`. -/
theorem sum_enorm_le_ofReal_card_mul {ι E' : Type*} [Fintype ι] [SeminormedAddCommGroup E']
    (a : ι → E') {G : ℝ} (h : ∀ i, ‖a i‖ ≤ G) :
    ∑ i, ‖a i‖ₑ ≤ ENNReal.ofReal (Fintype.card ι * G) := by
  calc _ ≤ ∑ _i : ι, ENNReal.ofReal G := Finset.sum_le_sum fun i _ => by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (h i)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- **Sobolev inequality on `H₀¹` of a bounded set.** In dimension at least two, on a bounded
measurable set, `H₀¹(Ω)` embeds into `L^q(Ω)` for some `q > 2`, with `‖v‖_q ≤ C ‖∇v‖₂`. -/
theorem exists_eLpNorm_le_of_mem_H01 (hn : 2 ≤ Module.finrank ℝ E) (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) :
    ∃ q : ℝ≥0, 2 < q ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ V : H01 (volume : Measure E) Ω,
      MemLp (⇑(fnL (V : H1Graph volume Ω))) q (volume.restrict Ω) ∧
        (eLpNorm (⇑(fnL (V : H1Graph volume Ω))) q (volume.restrict Ω)).toReal ≤
          C * ‖gradL (V : H1Graph volume Ω)‖ := by
  set e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (stdOrthonormalBasis ℝ E).repr with he
  have hm' : MeasurableSet (e.symm ⁻¹' Ω) := e.symm.continuous.measurable hΩm
  have hb' : Bornology.IsBounded (e.symm ⁻¹' Ω) := by
    rw [← LinearIsometryEquiv.image_eq_preimage_symm]
    exact e.isometry.lipschitzWith.isBounded_image hΩb
  obtain ⟨q, hq2, K, hK⟩ := exists_eLpNorm_le_of_mem_H01_coord hn hm' hb'
  refine ⟨q, hq2, K * Module.finrank ℝ E, by positivity, fun V => ?_⟩
  set Ω' := e.symm ⁻¹' Ω with hΩ'
  have hV' : mapIsometry e Ω (V : H1Graph volume Ω) ∈ H01 volume Ω' :=
    mapIsometry_mem_H01 e Ω V.2
  set Y : Sobolev.H01 Ω' := (h01Equiv Ω').symm ⟨_, hV'⟩ with hY
  have hYV : (h01Equiv Ω' Y : H1Graph volume Ω') = mapIsometry e Ω V := by
    rw [hY, LinearIsometryEquiv.apply_symm_apply]
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ‖gradL (V : H1Graph volume Ω)‖ := ⟨_, rfl⟩
  -- the function parts agree
  have hf0 : ⇑((Y : Sobolev.H1amb Ω') 0) =ᵐ[volume.restrict Ω']
      ⇑(fnL (V : H1Graph volume Ω)) ∘ e.symm := by
    have := fnL_h01Equiv Ω' Y
    rw [hYV, fnL_mapIsometry] at this
    rw [← this]
    exact coeFn_pullFn e Ω _
  have hE : eLpNorm (⇑(fnL (V : H1Graph volume Ω))) q (volume.restrict Ω) =
      eLpNorm (⇑((Y : Sobolev.H1amb Ω') 0)) q (volume.restrict Ω') := by
    rw [eLpNorm_congr_ae hf0, eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable _)
      (measurePreserving_symm_restrict e Ω)]
  -- the gradient parts are controlled
  have hG0 : 0 ≤ G := hG ▸ norm_nonneg _
  have hGsq : ∀ i : Fin (Module.finrank ℝ E), ‖(Y : Sobolev.H1amb Ω') i.succ‖ ≤ G := by
    intro i
    have h1 := norm_gradL_h01Equiv_sq Ω' Y
    rw [hYV, gradL_mapIsometry, LinearIsometry.norm_map] at h1
    have h2 : ‖(Y : Sobolev.H1amb Ω') i.succ‖ ^ 2 ≤ G ^ 2 := by
      rw [hG, h1]
      have := Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin (Module.finrank ℝ E) => ‖(Y : Sobolev.H1amb Ω') j.succ‖ ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      exact this
    exact (sq_le_sq₀ (norm_nonneg _) hG0).1 h2
  have hsum := sum_enorm_le_ofReal_card_mul (fun i : Fin (Module.finrank ℝ E) =>
    (Y : Sobolev.H1amb Ω') i.succ) hGsq
  rw [Fintype.card_fin] at hsum
  have hbound : eLpNorm (⇑(fnL (V : H1Graph volume Ω))) q (volume.restrict Ω) ≤
      ENNReal.ofReal (K * Module.finrank ℝ E * G) := by
    rw [hE]
    refine (hK _ Y.2).trans ?_
    calc (K : ℝ≥0∞) * ∑ i : Fin (Module.finrank ℝ E), ‖(Y : Sobolev.H1amb Ω') i.succ‖ₑ
        ≤ (K : ℝ≥0∞) * ENNReal.ofReal (Module.finrank ℝ E * G) := by gcongr
      _ = _ := by
          rw [mul_assoc, ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  refine ⟨lt_of_le_of_lt hbound ENNReal.ofReal_lt_top, ?_⟩
  rw [← hG]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans
    (ENNReal.toReal_ofReal (by positivity)).le

end H1Graph

namespace DivForm.FullEllipticOp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Set E}

open H1Graph

/-- **Weak maximum principle with a transport term** (Gilbarg and Trudinger Theorem 8.1, in
dimension at least two). Let `Ω` be a bounded open set in a space of dimension at least two,
`L` a divergence-form operator for the volume measure with bounded transport term and
nonnegative zeroth-order coefficient, and `U ∈ H¹(Ω)` a weak subsolution, meaning the bilinear
pairing of `U` against every nonnegative `V ∈ H₀¹(Ω)` is nonpositive. If `k ≥ 0` and `(u - k)⁺`
is the function part of some element of `H₀¹(Ω)`, then `u ≤ k` almost everywhere on `Ω`. -/
theorem weak_maximum_principle_transport (Op : FullEllipticOp (volume : Measure E))
    (hn : 2 ≤ Module.finrank ℝ E) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hc : ∀ᵐ x ∂(volume : Measure E), 0 ≤ Op.c x) {U : H1Graph volume Ω}
    (hU : U ∈ W12 volume Ω)
    (hsub : ∀ V : H01 volume Ω, (∀ᵐ x ∂(volume.restrict Ω), 0 ≤ fnL (V : H1Graph volume Ω) x) →
      Op.form Ω U V ≤ 0)
    {k : ℝ} (hk : 0 ≤ k)
    (hbd : ∃ V : H01 volume Ω, ⇑(fnL (V : H1Graph volume Ω)) =ᵐ[volume.restrict Ω]
      fun x => max (fnL U x - k) 0) :
    ∀ᵐ x ∂(volume.restrict Ω), fnL U x ≤ k := by
  obtain ⟨q, hq2, C, hC, hsob⟩ := exists_eLpNorm_le_of_mem_H01 hn hΩ.measurableSet hΩb
  exact weak_maximum_principle_transport_of_sobolev Op hΩ hΩb hc hq2 hC hsob hU hsub hk hbd

end DivForm.FullEllipticOp

end EllipticPdes
