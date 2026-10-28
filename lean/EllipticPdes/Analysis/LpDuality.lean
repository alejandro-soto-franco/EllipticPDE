/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

/-!
# Dual of `L^p`

Gilbarg and Trudinger state in §7.1 that the dual space of `L^p(Ω)` is isomorphic to `L^q(Ω)`
for `1/p + 1/q = 1` and `p < ∞`. This file builds the map `L^q → (L^p)*` sending `g` to the
functional `f ↦ ∫ f g`, proves that it is injective on a σ-finite measure space, proves the
reverse Hölder bound `‖g‖_q ≤ ‖∫ · g‖`, and proves that the map is onto for a finite measure and
then for a σ-finite measure. The open mapping theorem makes it an isomorphism `lpDualEquiv`, and
`exists_lpDual_eq` states it on a set of `ℝⁿ` in the form of Gilbarg and Trudinger.

The surjectivity proof follows the classical route. A functional `φ` defines the signed measure
`E ↦ φ(1_E)`, countably additive because the indicators of the partial unions converge in `L^p`
for `p < ∞`, and absolutely continuous with respect to `μ`. Its Radon–Nikodym density `g`
represents `φ` on indicators. The truncations of `g` at the levels `|g| ≤ n` lie in `L^q`, and the
reverse Hölder bound gives them `L^q` norm at most `‖φ‖`. Fatou's lemma puts `g` in `L^q`, and
two functionals agreeing on indicators agree on `L^p`.

On a σ-finite measure the finite case gives a density `k_n` on each set `S_n` of an increasing
exhausting sequence of sets of finite measure. The densities agree almost everywhere on the
overlaps. Their common limit `g` has `L^q` norm at most `‖φ‖` by Fatou's lemma. The functionals
of `g` and `φ` agree on the indicator of each `E ∩ S_n`, and continuity passes the equality to
the indicator of `E`.

## Main declarations

* `EllipticPdes.Analysis.lpDualMap`: the map `L^q → (L^p)*`, `g ↦ (f ↦ ∫ f g)`.
* `EllipticPdes.Analysis.lpDualMap_apply`: its value as an integral.
* `EllipticPdes.Analysis.lpDualMap_injective`: injectivity on a σ-finite measure.
* `EllipticPdes.Analysis.norm_le_norm_lpDualMap`: the reverse Hölder bound.
* `EllipticPdes.Analysis.lpDualMap_surjective_of_finite`: surjectivity on a finite measure.
* `EllipticPdes.Analysis.lpDualMap_surjective`: surjectivity on a σ-finite measure.
* `EllipticPdes.Analysis.lpDualEquiv`: the isomorphism `L^q ≃ (L^p)*` on a σ-finite measure.
* `EllipticPdes.Analysis.exists_lpDual_eq`: the form of Gilbarg and Trudinger on a set of `ℝⁿ`.
* `EllipticPdes.Analysis.extendByZeroLp`: the extension by zero `L^p(μ|s) → L^p(μ)`.
* `EllipticPdes.Analysis.ext_of_indicatorConstLp`: functionals on `L^p` for `p < ∞` that agree
  on the indicators of sets of finite measure are equal.

## References

D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§7.1 (p. 146).
-/

@[expose] public section

open Filter Function Topology MeasureTheory Set
open scoped ENNReal symmDiff

noncomputable section

namespace EllipticPdes.Analysis

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p q : ℝ≥0∞}

/-! ### Indicators in `L^p` -/

/-- An indicator with value `c` is `c` times the indicator with value `1`. -/
theorem indicatorConstLp_eq_smul_one {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (c : ℝ) : indicatorConstLp p hs hμs c = c • indicatorConstLp p hs hμs (1 : ℝ) := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := c),
    Lp.coeFn_smul c (indicatorConstLp p hs hμs (1 : ℝ)),
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := (1 : ℝ))] with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3]
  by_cases hx : x ∈ s <;> simp [hx]

/-- Two continuous functionals on `L^p` for `p < ∞` that agree on the indicators of the sets of
finite measure are equal. The indicators span the simple functions, and the simple functions are
dense in `L^p`. -/
theorem ext_of_indicatorConstLp [Fact (1 ≤ p)] (hp : p ≠ ∞) {T S : StrongDual ℝ (Lp ℝ p μ)}
    (h : ∀ (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ∞),
      T (indicatorConstLp p hs hμs (1 : ℝ)) = S (indicatorConstLp p hs hμs (1 : ℝ))) :
    T = S := by
  ext f
  refine Lp.induction hp (motive := fun f => T f = S f) ?_ ?_ ?_ f
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst, indicatorConstLp_eq_smul_one, map_smul, map_smul,
      h s hs hμs.ne]
  · intro f g hf hg _ hf' hg'
    simp only [map_add, hf', hg']
  · exact isClosed_eq T.continuous S.continuous

/-! ### Map from `L^q` to the dual of `L^p` -/

section Map

variable [p.HolderConjugate q] [Fact (1 ≤ p)] [Fact (1 ≤ q)]

variable (μ p q) in
/-- **Map from `L^q` to the dual of `L^p`.** For Hölder conjugate exponents, `g ∈ L^q` defines
the continuous functional `f ↦ ∫ f g` on `L^p`. Gilbarg and Trudinger §7.1 (p. 146). -/
def lpDualMap : Lp ℝ q μ →L[ℝ] StrongDual ℝ (Lp ℝ p μ) :=
  ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q).flip

/-- The functional `lpDualMap μ p q g` is the integral of the product with `g`. -/
theorem lpDualMap_apply (g : Lp ℝ q μ) (f : Lp ℝ p μ) :
    lpDualMap μ p q g f = ∫ x, f x * g x ∂μ := by
  simp [lpDualMap, ContinuousLinearMap.lpPairing_eq_integral]

/-- On the indicator of a set of finite measure, `lpDualMap μ p q g` is the integral of `g`
over the set. -/
theorem lpDualMap_indicatorConstLp (g : Lp ℝ q μ) {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) :
    lpDualMap μ p q g (indicatorConstLp p hs hμs (1 : ℝ)) = ∫ x in s, g x ∂μ := by
  rw [lpDualMap_apply, ← integral_indicator hs]
  refine integral_congr_ae ?_
  filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := (1 : ℝ))]
    with x hx
  rw [hx]
  by_cases h : x ∈ s <;> simp [h]

/-- **Injectivity of `L^q → (L^p)*`.** On a σ-finite measure, a function of `L^q` whose
integral against every function of `L^p` vanishes is zero. -/
theorem lpDualMap_injective [SigmaFinite μ] : Function.Injective (lpDualMap μ p q) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  rw [Lp.eq_zero_iff_ae_eq_zero]
  refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite (fun s hs hμs => ?_)
    fun s hs hμs => ?_
  · have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
    exact ((Lp.memLp g).restrict s).integrable (ENNReal.HolderConjugate.one_le q p)
  · rw [← lpDualMap_indicatorConstLp (p := p) g hs hμs.ne, hg]
    rfl

/-! ### Reverse Hölder bound -/

/-- The test function `t ↦ sgn t · |t|^{r-1}` of the reverse Hölder bound, written with `t / |t|`
for the sign of `t`. -/
def signPow (r t : ℝ) : ℝ := t / |t| * |t| ^ (r - 1)

/-- The test function `signPow r` is measurable. -/
theorem measurable_signPow (r : ℝ) : Measurable (signPow r) := by
  unfold signPow
  fun_prop

/-- The product of `signPow r t` with `t` is `|t|^r`. -/
theorem signPow_mul_self {r : ℝ} (hr : 0 < r) (t : ℝ) : signPow r t * t = |t| ^ r := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [signPow, Real.zero_rpow hr.ne']
  · have ha : 0 < |t| := abs_pos.2 ht
    have h1 : t / |t| * t = |t| := by
      rw [div_mul_eq_mul_div, ← abs_mul_abs_self, mul_div_assoc, div_self ha.ne', mul_one]
    calc signPow r t * t = (t / |t| * t) * |t| ^ (r - 1) := by unfold signPow; ring
      _ = |t| ^ (1 + (r - 1)) := by rw [h1, Real.rpow_add ha, Real.rpow_one]
      _ = |t| ^ r := by congr 1; ring

/-- For `1 < r`, the absolute value of `signPow r t` is `|t|^{r-1}`. -/
theorem abs_signPow {r : ℝ} (hr : 1 < r) (t : ℝ) : |signPow r t| = |t| ^ (r - 1) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [signPow, Real.zero_rpow (sub_pos.2 hr).ne']
  · rw [signPow, abs_mul, abs_div, abs_abs, div_self (abs_pos.2 ht).ne', one_mul,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _)]

/-- The sign `signPow 1 t` has absolute value at most `1`. -/
theorem abs_signPow_one_le (t : ℝ) : |signPow 1 t| ≤ 1 := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [signPow]
  · rw [signPow, sub_self, Real.rpow_zero, mul_one, abs_div, abs_abs, div_self (abs_pos.2 ht).ne']

/-- Hölder's bound for `lpDualMap` on a test function given as a function of `L^p`. -/
theorem integral_mul_le_of_memLp (g : Lp ℝ q μ) {F : α → ℝ} (hF : MemLp F p μ) :
    ∫ x, F x * g x ∂μ ≤ ‖lpDualMap μ p q g‖ * (eLpNorm F p μ).toReal := by
  have h := (lpDualMap μ p q g).le_opNorm (hF.toLp F)
  rw [lpDualMap_apply, Lp.norm_toLp, Real.norm_eq_abs] at h
  have he : ∫ x, (hF.toLp F) x * g x ∂μ = ∫ x, F x * g x ∂μ :=
    integral_congr_ae (hF.coeFn_toLp.mono fun x hx => by simp only [hx])
  rw [he] at h
  exact (le_abs_self _).trans h

/-- **Reverse Hölder bound.** On a σ-finite measure, the `L^q` norm of `g` is at most the norm
of the functional `f ↦ ∫ f g` on `L^p`. The case `q = ∞` tests `g` against sets of finite
measure, and σ-finiteness supplies them. Gilbarg and Trudinger §7.1 (p. 146). -/
theorem norm_le_norm_lpDualMap [SigmaFinite μ] (g : Lp ℝ q μ) :
    ‖g‖ ≤ ‖lpDualMap μ p q g‖ := by
  have hgm : AEStronglyMeasurable g μ := Lp.aestronglyMeasurable g
  rcases eq_or_ne q ∞ with hq | hq
  · -- `q = ∞` and `p = 1`: `|g|` is at most the norm on every set of finite measure
    have hp1 : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one q p).1 hq
    subst hq hp1
    set C := ‖lpDualMap μ 1 ∞ g‖
    have h0 : 0 ≤ᵐ[μ] fun x => C - ‖g x‖ := by
      refine ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite (fun s hs hμs => ?_)
        fun s hs hμs => ?_
      · have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
        exact (integrable_const C).sub (((Lp.memLp g).restrict s).integrable le_top).norm
      · have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
        have hgs : Integrable (fun x => ‖g x‖) (μ.restrict s) :=
          (((Lp.memLp g).restrict s).integrable le_top).norm
        set F : α → ℝ := s.indicator fun x => signPow 1 (g x)
        have hFm : AEStronglyMeasurable (fun x => signPow 1 (g x)) μ :=
          ((measurable_signPow 1).comp_aemeasurable hgm.aemeasurable).aestronglyMeasurable
        have hFms : AEStronglyMeasurable (fun x => signPow 1 (g x)) (μ.restrict s) :=
          hFm.restrict
        have hbd : ∀ x, ‖signPow 1 (g x)‖ ≤ 1 := fun x => abs_signPow_one_le _
        have hF : MemLp F 1 μ := by
          rw [memLp_indicator_iff_restrict hs]
          exact MemLp.of_bound hFms 1 (ae_of_all _ hbd)
        have hFn : (eLpNorm F 1 μ).toReal ≤ μ.real s := by
          rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
          have := eLpNorm_le_of_ae_bound (p := 1) hFms (ae_of_all _ hbd)
          rw [Measure.restrict_apply_univ] at this
          simp only [ENNReal.toReal_one, inv_one, ENNReal.rpow_one, ENNReal.ofReal_one,
            mul_one] at this
          exact ENNReal.toReal_mono hμs.ne this
        have hFg : ∀ x, F x * g x = s.indicator (fun x => ‖g x‖) x := by
          intro x
          by_cases hx : x ∈ s
          · simp [F, hx, signPow_mul_self one_pos, Real.norm_eq_abs]
          · simp [F, hx]
        have key := integral_mul_le_of_memLp g hF
        simp_rw [hFg] at key
        rw [integral_indicator hs] at key
        rw [integral_sub (integrable_const C) hgs, setIntegral_const, smul_eq_mul, sub_nonneg]
        calc ∫ x in s, ‖g x‖ ∂μ ≤ C * (eLpNorm F 1 μ).toReal := key
          _ ≤ C * μ.real s := mul_le_mul_of_nonneg_left hFn (norm_nonneg _)
          _ = μ.real s * C := mul_comm _ _
    have hae : ∀ᵐ x ∂μ, ‖g x‖ ≤ C := h0.mono fun x hx => sub_nonneg.1 hx
    rw [Lp.norm_def]
    refine ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) ?_
    simpa using eLpNorm_le_of_ae_bound (p := ∞) hgm hae
  rcases eq_or_ne q 1 with hq1 | hq1
  · -- `q = 1` and `p = ∞`: test against the sign of `g`
    have hp : p = ∞ := (ENNReal.HolderConjugate.eq_top_iff_eq_one p q).2 hq1
    subst hq1 hp
    set F : α → ℝ := fun x => signPow 1 (g x)
    have hFm : AEStronglyMeasurable F μ :=
      ((measurable_signPow 1).comp_aemeasurable hgm.aemeasurable).aestronglyMeasurable
    have hbd : ∀ᵐ x ∂μ, ‖F x‖ ≤ 1 := ae_of_all _ fun x => abs_signPow_one_le _
    have hF : MemLp F ∞ μ := memLp_top_of_bound hFm 1 hbd
    have hFn : (eLpNorm F ∞ μ).toReal ≤ 1 := by
      refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
      simpa using eLpNorm_le_of_ae_bound (p := ∞) hFm hbd
    have hg1 : ‖g‖ = ∫ x, F x * g x ∂μ := by
      rw [L1.norm_eq_integral_norm]
      congr 1
      funext x
      simp [F, signPow_mul_self one_pos, Real.norm_eq_abs]
    rw [hg1]
    calc ∫ x, F x * g x ∂μ ≤ ‖lpDualMap μ ∞ 1 g‖ * (eLpNorm F ∞ μ).toReal :=
          integral_mul_le_of_memLp g hF
      _ ≤ ‖lpDualMap μ ∞ 1 g‖ * 1 := mul_le_mul_of_nonneg_left hFn (norm_nonneg _)
      _ = ‖lpDualMap μ ∞ 1 g‖ := mul_one _
  · -- `1 < q < ∞`: test against `sgn g · |g|^{q-1}`
    have hp : p ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one p q).2 hq1
    have hpq : p.toReal.HolderConjugate q.toReal :=
      ENNReal.HolderConjugate.toReal_of_ne_top hp hq
    have hq0 : q ≠ 0 := ENNReal.HolderConjugate.ne_zero q p
    have hp0 : p ≠ 0 := ENNReal.HolderConjugate.ne_zero p q
    have hr : 1 < q.toReal := hpq.symm.lt
    set F : α → ℝ := fun x => signPow q.toReal (g x)
    have hFm : AEStronglyMeasurable F μ :=
      ((measurable_signPow _).comp_aemeasurable hgm.aemeasurable).aestronglyMeasurable
    have hFs : ∀ x, ‖F x‖ ^ p.toReal = ‖g x‖ ^ q.toReal := by
      intro x
      simp only [F, Real.norm_eq_abs, abs_signPow hr, ← Real.rpow_mul (abs_nonneg _),
        hpq.symm.sub_one_mul_conj]
    have hF : MemLp F p μ := by
      rw [← integrable_norm_rpow_iff hFm hp0 hp]
      simp_rw [hFs]
      exact (integrable_norm_rpow_iff hgm hq0 hq).2 (Lp.memLp g)
    set I := ∫ x, ‖g x‖ ^ q.toReal ∂μ
    have hI0 : 0 ≤ I := integral_nonneg fun x => by positivity
    have hgn : ‖g‖ = I ^ q.toReal⁻¹ := by
      rw [Lp.norm_def]
      exact lpNorm_eq_integral_norm_rpow_toReal hq0 hq hgm
    have hFn : (eLpNorm F p μ).toReal = I ^ p.toReal⁻¹ := by
      rw [toReal_eLpNorm, lpNorm_eq_integral_norm_rpow_toReal hp0 hp hFm]
      simp_rw [hFs]
      rfl
    have hFg : ∫ x, F x * g x ∂μ = I := by
      congr 1
      funext x
      simp [F, signPow_mul_self (zero_lt_one.trans hr), Real.norm_eq_abs]
    have key := integral_mul_le_of_memLp g hF
    rw [hFg, hFn] at key
    rw [hgn]
    rcases hI0.eq_or_lt with hI | hI
    · rw [← hI, Real.zero_rpow (inv_ne_zero (by positivity))]
      exact norm_nonneg _
    · have hpos : 0 < I ^ p.toReal⁻¹ := Real.rpow_pos_of_pos hI _
      have hsplit : I ^ q.toReal⁻¹ * I ^ p.toReal⁻¹ = I := by
        rw [← Real.rpow_add hI, hpq.symm.inv_add_inv_eq_one, Real.rpow_one]
      exact le_of_mul_le_mul_right (hsplit.trans_le key) hpos

end Map

/-! ### Surjectivity on a finite measure -/

section Finite

variable [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
/-- Indicators of equal sets are equal. -/
private theorem indicatorConstLp_congr_set {s t : Set α} (hst : s = t) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (ht : MeasurableSet t) (hμt : μ t ≠ ∞) (c : ℝ) :
    indicatorConstLp p hs hμs c = indicatorConstLp p ht hμt c := by
  subst hst
  rfl

/-- The indicator of a finite union of pairwise disjoint sets is the sum of their indicators. -/
private theorem indicatorConstLp_biUnion_finset {f : ℕ → Set α} (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (Disjoint on f)) (b : Finset ℕ) :
    indicatorConstLp p (b.measurableSet_biUnion fun i _ => hf i) (measure_ne_top μ _) (1 : ℝ) =
      ∑ i ∈ b, indicatorConstLp p (hf i) (measure_ne_top μ _) (1 : ℝ) := by
  induction b using Finset.induction_on with
  | empty =>
    rw [indicatorConstLp_congr_set (t := ∅) (by simp) _ _ MeasurableSet.empty (by simp),
      indicatorConstLp_empty, Finset.sum_empty]
  | insert a b ha ih =>
    rw [Finset.sum_insert ha, ← ih]
    have hdisj : Disjoint (f a) (⋃ i ∈ b, f i) := by
      rw [Set.disjoint_iUnion₂_right]
      intro i hi
      exact hd (by rintro rfl; exact ha hi)
    rw [indicatorConstLp_congr_set (Finset.set_biUnion_insert a b f) _ _
      ((hf a).union (b.measurableSet_biUnion fun i _ => hf i)) (measure_ne_top μ _)]
    exact indicatorConstLp_disjoint_union _ _ _ _ hdisj 1

/-- For `p < ∞`, the indicators of a pairwise disjoint family of sets sum in `L^p` to the
indicator of the union. -/
private theorem hasSum_indicatorConstLp [Fact (1 ≤ p)] (hp : p ≠ ∞) {f : ℕ → Set α}
    (hf : ∀ i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) :
    HasSum (fun i => indicatorConstLp p (hf i) (measure_ne_top μ _) (1 : ℝ))
      (indicatorConstLp p (MeasurableSet.iUnion hf) (measure_ne_top μ _) 1) := by
  have hμ : Tendsto (fun b : Finset ℕ => μ ((⋃ i ∈ b, f i) ∆ ⋃ i, f i)) atTop (𝓝 0) := by
    have hsub : ∀ b : Finset ℕ, (⋃ i ∈ b, f i) ⊆ ⋃ i, f i := fun b =>
      Set.iUnion₂_subset fun i _ => Set.subset_iUnion f i
    have heq : ∀ b : Finset ℕ, μ ((⋃ i ∈ b, f i) ∆ ⋃ i, f i) =
        μ (⋃ i, f i) - ∑ i ∈ b, μ (f i) := by
      intro b
      rw [symmDiff_of_le (hsub b), measure_sdiff (hsub b)
        (b.measurableSet_biUnion fun i _ => hf i).nullMeasurableSet (measure_ne_top μ _),
        measure_biUnion_finset (fun i _ j _ hij => hd hij) fun i _ => hf i]
    simp_rw [heq]
    have hsum : Tendsto (fun b : Finset ℕ => ∑ i ∈ b, μ (f i)) atTop (𝓝 (μ (⋃ i, f i))) := by
      rw [measure_iUnion hd hf]
      exact ENNReal.summable.hasSum
    simpa using ENNReal.Tendsto.sub (tendsto_const_nhds (x := μ (⋃ i, f i))) hsum
      (Or.inl (measure_ne_top μ _))
  exact (tendsto_indicatorConstLp_set hp hμ).congr fun b => indicatorConstLp_biUnion_finset hf hd b

open Classical in
/-- The signed measure `E ↦ φ(1_E)` of a functional `φ` on `L^p`, `p < ∞`. -/
private def dualSignedMeasure [Fact (1 ≤ p)] (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ)) :
    SignedMeasure α where
  measureOf' s := if hs : MeasurableSet s then φ (indicatorConstLp p hs (measure_ne_top μ s) 1)
    else 0
  empty' := by simp
  not_measurable' _ hs := dite_eq_right_iff.2 fun h => absurd h hs
  m_iUnion' f hf hd := by
    convert (hasSum_indicatorConstLp hp hf hd).mapL φ using 1
    · funext i
      exact dite_eq_left (hf i)
    · exact dite_eq_left _

/-- On a measurable set, `dualSignedMeasure` is the value of `φ` on its indicator. -/
private theorem dualSignedMeasure_apply [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (φ : StrongDual ℝ (Lp ℝ p μ)) {s : Set α} (hs : MeasurableSet s) :
    dualSignedMeasure hp φ s = φ (indicatorConstLp p hs (measure_ne_top μ s) 1) := by
  classical
  simp only [dualSignedMeasure, VectorMeasure.coe_mk]
  exact dite_eq_left hs

/-- A `μ`-null set has a zero indicator in `L^p`. Hence `dualSignedMeasure` is absolutely
continuous with respect to `μ`. -/
private theorem dualSignedMeasure_absolutelyContinuous [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (φ : StrongDual ℝ (Lp ℝ p μ)) : dualSignedMeasure hp φ ≪ᵥ μ.toENNRealVectorMeasure := by
  classical
  intro s hs0
  by_cases hs : MeasurableSet s
  · rw [Measure.toENNRealVectorMeasure_apply_measurable hs] at hs0
    rw [dualSignedMeasure_apply hp φ hs]
    have h0 : indicatorConstLp p hs (measure_ne_top μ s) (1 : ℝ) = 0 := by
      rw [← indicatorConstLp_empty (p := p) (μ := μ) (c := (1 : ℝ))]
      exact (indicatorConstLp_inj hs _ .empty (by simp) one_ne_zero).2 (ae_eq_empty.2 hs0)
    rw [h0, map_zero]
  · simp only [dualSignedMeasure, VectorMeasure.coe_mk]
    exact dite_eq_right_iff.2 fun h => absurd h hs

/-- The density of `dualSignedMeasure` represents `φ` on indicators. -/
private theorem setIntegral_rnDeriv_dualSignedMeasure [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (φ : StrongDual ℝ (Lp ℝ p μ)) {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, (dualSignedMeasure hp φ).rnDeriv μ x ∂μ =
      φ (indicatorConstLp p hs (measure_ne_top μ s) 1) := by
  rw [← withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hs,
    SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ (dualSignedMeasure_absolutelyContinuous hp φ),
    dualSignedMeasure_apply hp φ hs]

variable [p.HolderConjugate q] [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Surjectivity of `L^q → (L^p)*` on a finite measure.** For `1 ≤ p < ∞` and a finite
measure, every continuous functional on `L^p` is `f ↦ ∫ f g` for some `g ∈ L^q`.
Gilbarg and Trudinger §7.1 (p. 146). -/
theorem lpDualMap_surjective_of_finite (hp : p ≠ ∞) : Function.Surjective (lpDualMap μ p q) := by
  intro φ
  set g := (dualSignedMeasure hp φ).rnDeriv μ
  have hgm : Measurable g := SignedMeasure.measurable_rnDeriv _ _
  have hint : ∀ (s : Set α) (hs : MeasurableSet s),
      ∫ x in s, g x ∂μ = φ (indicatorConstLp p hs (measure_ne_top μ s) 1) :=
    fun s hs => setIntegral_rnDeriv_dualSignedMeasure hp φ hs
  -- the truncations `g · 1_{|g| ≤ n}`
  set B : ℕ → Set α := fun n => {x | |g x| ≤ n}
  have hB : ∀ n, MeasurableSet (B n) := fun n =>
    measurableSet_le (continuous_abs.measurable.comp hgm) measurable_const
  have hmem : ∀ n, MemLp ((B n).indicator g) q μ := fun n =>
    MemLp.of_bound (hgm.indicator (hB n)).aestronglyMeasurable n (ae_of_all _ fun x => by
      by_cases hx : x ∈ B n
      · rw [Set.indicator_of_mem hx, Real.norm_eq_abs]
        exact hx
      · simp [Set.indicator_of_notMem hx])
  -- each truncation has `L^q` norm at most `‖φ‖`
  have hbound : ∀ n, ‖(hmem n).toLp _‖ ≤ ‖φ‖ := by
    intro n
    refine (norm_le_norm_lpDualMap (p := p) _).trans ?_
    set h1 : Lp ℝ ∞ μ := indicatorConstLp ∞ (hB n) (measure_ne_top μ _) (1 : ℝ)
    set M := (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ p p h1
    have heq : lpDualMap μ p q ((hmem n).toLp _) = φ.comp M := by
      refine ext_of_indicatorConstLp hp fun s hs hμs => ?_
      have hM : M (indicatorConstLp p hs hμs 1) =
          indicatorConstLp p (hs.inter (hB n)) (measure_ne_top μ _) (1 : ℝ) := by
        refine Lp.ext ?_
        filter_upwards [ContinuousLinearMap.coeFn_holder (ContinuousLinearMap.mul ℝ ℝ) (r := p) h1
            (indicatorConstLp p hs hμs (1 : ℝ)),
          indicatorConstLp_coeFn (p := ∞) (hs := hB n) (hμs := measure_ne_top μ _)
            (c := (1 : ℝ)),
          indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := (1 : ℝ)),
          indicatorConstLp_coeFn (p := p) (hs := hs.inter (hB n)) (hμs := measure_ne_top μ _)
            (c := (1 : ℝ))] with x h2 h3 h4 h5
        simp only [M, ContinuousLinearMap.holderL_apply_apply] at *
        rw [h2, h3, h4, h5]
        by_cases hxs : x ∈ s <;> by_cases hxB : x ∈ B n <;> simp [hxs, hxB]
      rw [lpDualMap_indicatorConstLp, ContinuousLinearMap.comp_apply, hM,
        ← hint _ (hs.inter (hB n)), ← setIntegral_indicator (hB n)]
      exact integral_congr_ae (ae_restrict_of_ae (MemLp.coeFn_toLp _))
    rw [heq]
    calc ‖φ.comp M‖ ≤ ‖φ‖ * ‖M‖ := φ.opNorm_comp_le M
      _ ≤ ‖φ‖ * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ‖M‖ ≤ ‖(ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ p p‖ * ‖h1‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * 1 := by
            refine mul_le_mul ((ContinuousLinearMap.norm_holderL_le _).trans
              (ContinuousLinearMap.opNorm_mul_le _ _)) ?_ (norm_nonneg _) zero_le_one
            refine norm_indicatorConstLp_le.trans ?_
            simp
          _ = 1 := one_mul 1
      _ = ‖φ‖ := mul_one _
  -- Fatou puts `g` in `L^q`
  have hgq : MemLp g q μ := by
    rw [memLp_iff]
    have hlim : ∀ x, Tendsto (fun n => (B n).indicator g x) atTop (𝓝 (g x)) := by
      intro x
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈|g x|⌉₊] with n hn
      exact (Set.indicator_of_mem (s := B n) (show |g x| ≤ n from
        (Nat.le_ceil _).trans (by exact_mod_cast hn)) g).symm
    have hle : ∀ n, eLpNorm ((B n).indicator g) q μ ≤ ENNReal.ofReal ‖φ‖ := by
      intro n
      have := hbound n
      rw [Lp.norm_toLp] at this
      exact (ENNReal.le_ofReal_iff_toReal_le (hmem n).eLpNorm_ne_top (norm_nonneg _)).2 this
    calc eLpNorm g q μ ≤ atTop.liminf fun n => eLpNorm ((B n).indicator g) q μ :=
          Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => (hmem n).aestronglyMeasurable) g
            hgm.aestronglyMeasurable (ae_of_all _ hlim)
      _ ≤ ENNReal.ofReal ‖φ‖ := liminf_le_of_frequently_le' (Frequently.of_forall hle)
      _ < ∞ := ENNReal.ofReal_lt_top
  -- two functionals agreeing on indicators are equal
  refine ⟨hgq.toLp g, ext_of_indicatorConstLp hp fun s hs hμs => ?_⟩
  rw [lpDualMap_indicatorConstLp, ← hint s hs]
  exact integral_congr_ae (ae_restrict_of_ae (MemLp.coeFn_toLp _))

end Finite

/-! ### Extension by zero -/

section Extend

variable {s : Set α}

/-- A function of `L^p(μ|s)` extended by zero off `s` lies in `L^p(μ)`. -/
theorem memLp_indicator_restrict (hs : MeasurableSet s) (f : Lp ℝ p (μ.restrict s)) :
    MemLp (s.indicator f) p μ :=
  (memLp_indicator_iff_restrict hs).2 (Lp.memLp f)

variable [Fact (1 ≤ p)]

variable (μ p) in
/-- **Extension by zero.** The continuous linear map `L^p(μ|s) → L^p(μ)` that extends a function
by zero off the measurable set `s`. -/
def extendByZeroLp (hs : MeasurableSet s) : Lp ℝ p (μ.restrict s) →L[ℝ] Lp ℝ p μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_indicator_restrict hs f).toLp _
      map_add' := fun f g => by
        refine Lp.ext ?_
        filter_upwards [(memLp_indicator_restrict hs (f + g)).coeFn_toLp,
          Lp.coeFn_add ((memLp_indicator_restrict hs f).toLp _)
            ((memLp_indicator_restrict hs g).toLp _),
          (memLp_indicator_restrict hs f).coeFn_toLp, (memLp_indicator_restrict hs g).coeFn_toLp,
          (ae_restrict_iff' hs).1 (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
        rw [h1, h2, Pi.add_apply, h3, h4]
        by_cases hx : x ∈ s
        · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx, h5 hx, Pi.add_apply]
        · simp [indicator_of_notMem hx]
      map_smul' := fun c f => by
        refine Lp.ext ?_
        filter_upwards [(memLp_indicator_restrict hs (c • f)).coeFn_toLp,
          Lp.coeFn_smul c ((memLp_indicator_restrict hs f).toLp _),
          (memLp_indicator_restrict hs f).coeFn_toLp,
          (ae_restrict_iff' hs).1 (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3]
        by_cases hx : x ∈ s
        · rw [indicator_of_mem hx, indicator_of_mem hx, h4 hx, Pi.smul_apply]
        · simp [indicator_of_notMem hx] }
    1 fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hs, Lp.norm_def]

/-- The extension by zero of `f` is almost everywhere equal to `s.indicator f`. -/
theorem extendByZeroLp_coeFn (hs : MeasurableSet s) (f : Lp ℝ p (μ.restrict s)) :
    extendByZeroLp μ p hs f =ᵐ[μ] s.indicator f :=
  (memLp_indicator_restrict hs f).coeFn_toLp

/-- The extension by zero has operator norm at most `1`. -/
theorem norm_extendByZeroLp_le (hs : MeasurableSet s) : ‖extendByZeroLp μ p hs‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The extension by zero of the indicator of `t` in `L^p(μ|s)` is the indicator of `t ∩ s` in
`L^p(μ)`. -/
theorem extendByZeroLp_indicatorConstLp (hs : MeasurableSet s) {t : Set α}
    (ht : MeasurableSet t) (hμt : μ (t ∩ s) ≠ ∞) :
    extendByZeroLp μ p hs (indicatorConstLp p ht (by rwa [Measure.restrict_apply ht]) (1 : ℝ)) =
      indicatorConstLp p (ht.inter hs) hμt (1 : ℝ) := by
  refine Lp.ext ?_
  filter_upwards [extendByZeroLp_coeFn hs
      (indicatorConstLp p ht (by rwa [Measure.restrict_apply ht]) (1 : ℝ)),
    (ae_restrict_iff' hs).1 (indicatorConstLp_coeFn (p := p) (μ := μ.restrict s) (hs := ht)
      (hμs := by rwa [Measure.restrict_apply ht]) (c := (1 : ℝ))),
    indicatorConstLp_coeFn (p := p) (hs := ht.inter hs) (hμs := hμt) (c := (1 : ℝ))]
    with x h1 h2 h3
  rw [h1, h3]
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, h2 hx]
    by_cases hxt : x ∈ t <;> simp [hx, hxt]
  · simp [hx]

end Extend

/-! ### Duality on a σ-finite measure -/

section SigmaFinite

variable [p.HolderConjugate q] [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Surjectivity of `L^q → (L^p)*`.** For `1 ≤ p < ∞` and a σ-finite measure, every continuous
functional on `L^p` is `f ↦ ∫ f g` for some `g ∈ L^q`. The proof applies the finite case on each
set of an increasing exhausting sequence of sets of finite measure and glues the densities.
Gilbarg and Trudinger §7.1 (p. 146). -/
theorem lpDualMap_surjective [SigmaFinite μ] (hp : p ≠ ∞) :
    Function.Surjective (lpDualMap μ p q) := by
  intro φ
  set S := spanningSets μ
  have hS : ∀ n, MeasurableSet (S n) := measurableSet_spanningSets μ
  have hSμ : ∀ n, μ (S n) ≠ ∞ := fun n => (measure_spanningSets_lt_top μ n).ne
  have hSf : ∀ n, IsFiniteMeasure (μ.restrict (S n)) := fun n =>
    isFiniteMeasure_restrict.2 (hSμ n)
  have hq1 : 1 ≤ q := ENNReal.HolderConjugate.one_le q p
  -- the finite case gives a density on each `S n`
  have hk : ∀ n, ∃ k : Lp ℝ q (μ.restrict (S n)),
      lpDualMap (μ.restrict (S n)) p q k = φ.comp (extendByZeroLp μ p (hS n)) := fun n => by
    have := hSf n
    exact lpDualMap_surjective_of_finite hp _
  choose k hk using hk
  have hrep : ∀ n (t : Set α) (ht : MeasurableSet t) (hμt : μ (t ∩ S n) ≠ ∞),
      ∫ x in t, k n x ∂μ.restrict (S n) =
        φ (indicatorConstLp p (ht.inter (hS n)) hμt (1 : ℝ)) := by
    intro n t ht hμt
    rw [← lpDualMap_indicatorConstLp (p := p) (k n) ht (by rwa [Measure.restrict_apply ht]),
      hk n, ContinuousLinearMap.comp_apply, extendByZeroLp_indicatorConstLp]
  have hnorm : ∀ n, ‖k n‖ ≤ ‖φ‖ := by
    intro n
    have := hSf n
    refine (norm_le_norm_lpDualMap (p := p) (k n)).trans ?_
    rw [hk n]
    exact (φ.opNorm_comp_le _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (norm_extendByZeroLp_le (hS n)))
  -- the densities agree on the overlaps
  have hagree : ∀ n m, n ≤ m → k n =ᵐ[μ.restrict (S n)] k m := by
    intro n m hnm
    have := hSf n
    have hsub : S n ⊆ S m := monotone_spanningSets μ hnm
    have hres : (μ.restrict (S m)).restrict (S n) = μ.restrict (S n) := by
      rw [Measure.restrict_restrict (hS n), inter_eq_left.2 hsub]
    have hint : Integrable (k m) (μ.restrict (S n)) := by
      have := hSf m
      rw [← hres]
      exact ((Lp.memLp (k m)).restrict (S n)).integrable hq1
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
      (fun t _ _ => ((Lp.memLp (k n)).integrable hq1).integrableOn)
      (fun t _ _ => hint.integrableOn) fun t ht _ => ?_
    have h1 : μ (t ∩ S n) ≠ ∞ := measure_ne_top_of_subset inter_subset_right (hSμ n)
    have h2 : μ (t ∩ S n ∩ S m) ≠ ∞ := measure_ne_top_of_subset inter_subset_left h1
    rw [hrep n t ht h1, ← hres, Measure.restrict_restrict ht, hrep m _ (ht.inter (hS n)) h2]
    exact congrArg φ (indicatorConstLp_congr_set
      (inter_eq_left.2 (inter_subset_right.trans hsub)).symm _ _ _ _ _)
  have hgood : ∀ᵐ x ∂μ, ∀ n m, n ≤ m → x ∈ S n → k n x = k m x := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro m
    by_cases hnm : n ≤ m
    · filter_upwards [(ae_restrict_iff' (hS n)).1 (hagree n m hnm)] with x hx _ hxn
        using hx hxn
    · exact ae_of_all _ fun x h => absurd h hnm
  -- glue the densities
  set G : ℕ → α → ℝ := fun n => (S n).indicator (k n)
  set g : α → ℝ := fun x => limUnder atTop fun n => G n x
  have hlim : ∀ᵐ x ∂μ, ∀ n, x ∈ S n → Tendsto (fun m => G m x) atTop (𝓝 (k n x)) := by
    filter_upwards [hgood] with x hx n hxn
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    change k n x = (S m).indicator (k m) x
    rw [indicator_of_mem (monotone_spanningSets μ hm hxn), hx n m hm hxn]
  have hgk : ∀ᵐ x ∂μ, ∀ n, x ∈ S n → g x = k n x := by
    filter_upwards [hlim] with x hx n hxn
    exact (hx n hxn).limUnder_eq
  have hgt : ∀ᵐ x ∂μ, Tendsto (fun m => G m x) atTop (𝓝 (g x)) := by
    filter_upwards [hlim, hgk] with x hx hx'
    obtain ⟨n, hn⟩ := mem_iUnion.1 (show x ∈ ⋃ n, S n by rw [iUnion_spanningSets]; trivial)
    rw [hx' n hn]
    exact hx n hn
  have hGm : ∀ n, AEStronglyMeasurable (G n) μ := fun n =>
    (aestronglyMeasurable_indicator_iff (hS n)).2 (Lp.aestronglyMeasurable (k n))
  have hgm : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae atTop hGm hgt
  -- Fatou puts `g` in `L^q`
  have hle : ∀ n, eLpNorm (G n) q μ ≤ ENNReal.ofReal ‖φ‖ := by
    intro n
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (hS n)]
    refine (ENNReal.le_ofReal_iff_toReal_le (Lp.eLpNorm_ne_top _) (norm_nonneg _)).2 ?_
    rw [← Lp.norm_def]
    exact hnorm n
  have hgq : MemLp g q μ := by
    have hlt : eLpNorm g q μ < ∞ := calc eLpNorm g q μ ≤ atTop.liminf fun n => eLpNorm (G n) q μ :=
          Lp.eLpNorm_lim_le_liminf_eLpNorm hGm g hgm hgt
      _ ≤ ENNReal.ofReal ‖φ‖ := liminf_le_of_frequently_le' (Frequently.of_forall hle)
      _ < ∞ := ENNReal.ofReal_lt_top
    exact hlt
  -- pass to the limit along the indicators of `t ∩ S n`
  refine ⟨hgq.toLp g, ext_of_indicatorConstLp hp fun t ht hμt => ?_⟩
  have hμtn : ∀ n, μ (t ∩ S n) ≠ ∞ := fun n => measure_ne_top_of_subset inter_subset_left hμt
  have hseq : ∀ n, lpDualMap μ p q (hgq.toLp g)
      (indicatorConstLp p (ht.inter (hS n)) (hμtn n) 1) =
        φ (indicatorConstLp p (ht.inter (hS n)) (hμtn n) 1) := by
    intro n
    rw [lpDualMap_indicatorConstLp, ← hrep n t ht (hμtn n), Measure.restrict_restrict ht]
    refine integral_congr_ae ?_
    have h1 : ∀ᵐ x ∂μ.restrict (t ∩ S n), x ∈ S n :=
      ae_restrict_of_forall_mem (ht.inter (hS n)) fun x hx => hx.2
    filter_upwards [ae_restrict_of_ae hgq.coeFn_toLp, ae_restrict_of_ae hgk, h1]
      with x h2 h3 h4
    rw [h2, h3 n h4]
  have hconv : Tendsto (fun n => indicatorConstLp p (ht.inter (hS n)) (hμtn n) (1 : ℝ)) atTop
      (𝓝 (indicatorConstLp p ht hμt 1)) := by
    refine tendsto_indicatorConstLp_set hp ?_
    have he : ∀ n, (t ∩ S n) ∆ t = t \ S n := fun n => by
      rw [symmDiff_of_le inter_subset_left, sdiff_self_inter]
    simp_rw [he]
    have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun n => t \ S n)
      (fun n => (ht.diff (hS n)).nullMeasurableSet)
      (fun n m h => sdiff_subset_sdiff_right (monotone_spanningSets μ h))
      ⟨0, measure_ne_top_of_subset sdiff_subset hμt⟩
    rwa [← sdiff_iUnion, iUnion_spanningSets, sdiff_univ, measure_empty] at h
  exact tendsto_nhds_unique ((((lpDualMap μ p q _).continuous.tendsto _).comp hconv).congr hseq)
    ((φ.continuous.tendsto _).comp hconv)

variable (μ p q) in
/-- **Dual of `L^p`.** For `1 ≤ p < ∞` and a σ-finite measure, `g ↦ (f ↦ ∫ f g)` is an
isomorphism of Banach spaces from `L^q` onto the dual of `L^p`. The open mapping theorem gives the
continuity of the inverse. Gilbarg and Trudinger §7.1 (p. 146). -/
def lpDualEquiv [SigmaFinite μ] (hp : p ≠ ∞) : Lp ℝ q μ ≃L[ℝ] StrongDual ℝ (Lp ℝ p μ) :=
  ContinuousLinearEquiv.ofBijective (lpDualMap μ p q)
    (LinearMap.ker_eq_bot.2 lpDualMap_injective)
    (LinearMap.range_eq_top.2 (lpDualMap_surjective hp))

/-- The isomorphism `lpDualEquiv` is the map `lpDualMap`. -/
theorem coe_lpDualEquiv [SigmaFinite μ] (hp : p ≠ ∞) :
    ⇑(lpDualEquiv μ p q hp) = lpDualMap μ p q :=
  rfl

/-- **Dual of `L^p(Ω)`.** Let `Ω` be a set of a finite-dimensional real space with Haar measure
and let `1 ≤ p < ∞` have conjugate exponent `q`. Every continuous functional `φ` on `L^p(Ω)` is
`f ↦ ∫_Ω f g` for exactly one `g ∈ L^q(Ω)`. The case `p = 1` is included.
Gilbarg and Trudinger §7.1 (p. 146). -/
theorem exists_lpDual_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [(volume : Measure E).IsAddHaarMeasure] (hp : p ≠ ∞)
    (Ω : Set E)
    (φ : StrongDual ℝ (Lp ℝ p (volume.restrict Ω))) :
    ∃! g : Lp ℝ q (volume.restrict Ω), ∀ f, φ f = ∫ x in Ω, f x * g x := by
  obtain ⟨g, hg⟩ := lpDualMap_surjective (μ := volume.restrict Ω) (q := q) hp φ
  refine ⟨g, fun f => by rw [← hg, lpDualMap_apply], fun g' hg' => ?_⟩
  refine lpDualMap_injective (p := p) (ContinuousLinearMap.ext fun f => ?_)
  rw [lpDualMap_apply, ← hg' f, hg]

end SigmaFinite

end EllipticPdes.Analysis
