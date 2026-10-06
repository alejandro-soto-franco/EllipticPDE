/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.LinearOperator
public import EllipticPdes.Extension.GlobalApproximation
public import EllipticPdes.Extension.Descent
public import EllipticPdes.Embedding.H01Sobolev

/-!
# Extension operator between the graph spaces

`EllipticPdes.Extension.exists_extLinear` is the extension operator on pairs of a class and its
gradient, given as functions. Guo's Theorem III.2.2 states it as a bounded linear map
`E : W^{1,p}(Ω) → W^{1,p}(ℝⁿ)` between the Sobolev spaces. This file states it that way at
`p = 2`, between the graph spaces `W12 Ω` and `W12 ℝᵈ` of this development.

The passage from functions to classes needs nothing beyond the bound. A linear map on
representatives whose image is bounded in `L²(ℝᵈ)` by the `L²(Ω)` seminorms of the input
descends to classes: two representatives of one class differ by a pair of seminorm zero, so
their images differ by a function of seminorm zero, which vanishes almost everywhere. The map
is then linear on the classes, bounded by the same constant, its image lies in the graph space
of the whole space because the image pair has a weak gradient there, and the three clauses of
the theorem are read off `exists_extLinear` through the representatives.

## Main declarations

* `EllipticPdes.Extension.mem_W12_of_hasWeakGradOn`: a class with an `L²` weak gradient,
  paired with it, lies in the graph space.
* `EllipticPdes.Extension.exists_extW12`: the extension operator as a bounded linear map
  between the graph spaces, with the three clauses of Guo III.2.2.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem III.2.2
(p. 20); L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4 Theorem 1 (p. 253).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev
open EllipticPdes.Embedding (HasWeakGradOn hasWeakGradOn_zero hasWeakGradOn_unique_ae
  isFiniteMeasure_restrict_of_isBounded norm_apply_le)

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### Membership of a pair in the graph space -/

/-- **Membership of a class with an `L²` weak gradient in the graph space**, paired with that
gradient.
This is the converse of `hasWeakGradOn_of_mem_W12`: the constraint defining `W12 Ω` is the
integration by parts the weak gradient asserts. -/
theorem mem_W12_of_hasWeakGradOn {F : EuclideanSpace ℝ (Fin d) → ℝ}
    {G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hF : MemLp F 2 (volume.restrict Ω))
    (hG : ∀ k, MemLp (G k) 2 (volume.restrict Ω)) (hwg : HasWeakGradOn Ω F G) :
    (WithLp.toLp 2 (Fin.cons (hF.toLp F) fun k => (hG k).toLp (G k)) : H1amb Ω) ∈ W12 Ω := by
  rw [mem_W12_iff]
  intro φ h i
  simp only [Fin.cons_zero, Fin.cons_succ, IsTestFn.partialCls, IsTestFn.testCls]
  rw [inner_toLp_eq, inner_toLp_eq]
  have key := hwg φ h.1 h.2.1 h.2.2 i
  have e1 : ∫ x in Ω, partialD i φ x * F x = ∫ x in Ω, F x * partialD i φ x :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have e2 : ∫ x in Ω, φ x * G i x = ∫ x in Ω, G i x * φ x :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [e1, e2, key]
  ring

/-! ### The operator on the graph spaces -/

/-- **The pairs of a class and a gradient on `Ω`**: integrable components, and the weak gradient
identity on `Ω`. -/
def goodPairs (Ω : Set (EuclideanSpace ℝ (Fin d))) : Submodule ℝ (SobolevPair d) where
  carrier := {w | IntegrableOn w.1 Ω volume ∧ (∀ k, IntegrableOn (w.2 k) Ω volume) ∧
    HasWeakGradOn Ω w.1 w.2}
  add_mem' := fun ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ =>
    ⟨a1.add b1, fun k => (a2 k).add (b2 k), a3.add a1 b1 a2 b2 b3⟩
  zero_mem' := ⟨integrableOn_zero, fun _ => integrableOn_zero, hasWeakGradOn_zero⟩
  smul_mem' := fun c _ ⟨h1, h2, h3⟩ =>
    ⟨h1.smul c, fun k => (h2 k).smul c, h3.const_mul c⟩

/-- **A bounded operator on good pairs respects almost-everywhere equality.** If the image of a
good pair is bounded by the pair seminorm over `Ω`, then two good pairs that agree almost
everywhere on `Ω` have images that agree almost everywhere. -/
theorem ae_eq_of_bound {T : SobolevPair d →ₗ[ℝ] SobolevPair d} {K : ℝ≥0}
    (hT : ∀ w ∈ goodPairs Ω, eLpNorm (T w).1 2 volume
        ≤ K * pairNorm 2 (volume.restrict Ω) w.1 w.2 ∧
      ∀ k, eLpNorm ((T w).2 k) 2 volume ≤ K * pairNorm 2 (volume.restrict Ω) w.1 w.2)
    {p q : SobolevPair d} (hp : p ∈ goodPairs Ω) (hq : q ∈ goodPairs Ω)
    (h1 : p.1 =ᵐ[volume.restrict Ω] q.1) (h2 : ∀ k, p.2 k =ᵐ[volume.restrict Ω] q.2 k) :
    (T p).1 =ᵐ[volume] (T q).1 ∧ ∀ k, (T p).2 k =ᵐ[volume] (T q).2 k := by
  have hd1 : (p - q).1 =ᵐ[volume.restrict Ω] (0 : EuclideanSpace ℝ (Fin d) → ℝ) := by
    filter_upwards [h1] with x hx
    simp [hx]
  have hd2 : ∀ k, (p - q).2 k =ᵐ[volume.restrict Ω] (0 : EuclideanSpace ℝ (Fin d) → ℝ) :=
    fun k => by filter_upwards [h2 k] with x hx; simp [hx]
  have hzero : pairNorm 2 (volume.restrict Ω) (p - q).1 (p - q).2 = 0 := by
    simp only [pairNorm, eLpNorm_congr_ae hd1, eLpNorm_zero, zero_add]
    exact Finset.sum_eq_zero fun i _ => by rw [eLpNorm_congr_ae (hd2 i), eLpNorm_zero]
  obtain ⟨hb1, hb2⟩ := hT (p - q) (sub_mem hp hq)
  rw [hzero, mul_zero, nonpos_iff_eq_zero] at hb1
  refine ⟨?_, fun k => ?_⟩
  · have h := (eLpNorm_eq_zero_iff two_ne_zero).mp hb1
    rw [map_sub] at h
    filter_upwards [h] with x hx
    simpa [sub_eq_zero] using hx
  · have hk := hb2 k
    rw [hzero, mul_zero, nonpos_iff_eq_zero] at hk
    have h := (eLpNorm_eq_zero_iff two_ne_zero).mp hk
    rw [map_sub] at h
    filter_upwards [h] with x hx
    simpa [sub_eq_zero] using hx

/-- A vector of classes is the vector with the given representatives. -/
theorem eq_toLp_cons {F : EuclideanSpace ℝ (Fin d) → ℝ}
    {G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hF : MemLp F 2 (volume.restrict Ω))
    (hG : ∀ k, MemLp (G k) 2 (volume.restrict Ω)) (V : H1amb Ω)
    (h0 : ⇑(V 0) =ᵐ[volume.restrict Ω] F) (hk : ∀ k, ⇑(V k.succ) =ᵐ[volume.restrict Ω] G k) :
    V = WithLp.toLp 2 (Fin.cons (hF.toLp F) fun k => (hG k).toLp (G k)) := by
  refine PiLp.ext fun i => ?_
  refine Fin.cases ?_ (fun k => ?_) i
  · exact Lp.ext (h0.trans hF.coeFn_toLp.symm)
  · exact Lp.ext ((hk k).trans (hG k).coeFn_toLp.symm)

/-- The pair seminorm of the representatives of an element of the graph space is at most `d + 1`
times its norm. -/
theorem pairNorm_rep_le (U : H1amb Ω) :
    pairNorm 2 (volume.restrict Ω) (rep U 0) (fun k => rep U k.succ)
      ≤ ENNReal.ofReal ((d + 1) * ‖U‖) := by
  have hk : ∀ i, eLpNorm (rep U i) 2 (volume.restrict Ω) = ENNReal.ofReal ‖U i‖ := fun i => by
    rw [rep, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_lt_top _).ne]
  rw [pairNorm]
  simp_rw [hk]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _),
    ← ENNReal.ofReal_add (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖U 0‖ + ∑ k : Fin d, ‖U k.succ‖ ≤ ‖U‖ + ∑ _k : Fin d, ‖U‖ :=
        add_le_add (PiLp.norm_apply_le U 0) (Finset.sum_le_sum fun k _ => PiLp.norm_apply_le U _)
    _ = (d + 1) * ‖U‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **Extension operator between the graph spaces** (Guo Theorem III.2.2 at `p = 2`,
Evans §5.4 Theorem 1). On a bounded open domain with `C¹` boundary, and for any open set
the closure of the domain sits in, there is a bounded linear map from `W12 Ω`, the `H¹(Ω)`
of this development, to the graph space of the whole space, such that the image of every
element agrees with it on the domain, function coordinate and gradient coordinates alike,
its function coordinate vanishes almost everywhere outside the given open set, and it is
bounded by a constant times the norm of the element. -/
theorem exists_extW12 (hd : 0 < d) (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) {Ω' : Set (EuclideanSpace ℝ (Fin d))} (hΩ'open : IsOpen Ω')
    (hsub : closure Ω ⊆ Ω') :
    ∃ (E : W12 Ω →L[ℝ] W12 (Set.univ : Set (EuclideanSpace ℝ (Fin d)))) (C : ℝ),
      (∀ U : W12 Ω,
        (((E U : W12 (Set.univ : Set (EuclideanSpace ℝ (Fin d)))) : H1amb Set.univ) 0 :
            EuclideanSpace ℝ (Fin d) → ℝ)
          =ᵐ[volume.restrict Ω] (fun x => ((U : H1amb Ω) 0 : L2D Ω) x) ∧
        ∀ k : Fin d,
          (((E U : W12 (Set.univ : Set (EuclideanSpace ℝ (Fin d)))) : H1amb Set.univ) k.succ :
              EuclideanSpace ℝ (Fin d) → ℝ)
            =ᵐ[volume.restrict Ω] (fun x => ((U : H1amb Ω) k.succ : L2D Ω) x)) ∧
      (∀ U : W12 Ω, ∀ᵐ y ∂volume, y ∉ Ω' →
        (((E U : W12 (Set.univ : Set (EuclideanSpace ℝ (Fin d)))) : H1amb Set.univ) 0 :
          EuclideanSpace ℝ (Fin d) → ℝ) y = 0) ∧
      ∀ U : W12 Ω, ‖E U‖ ≤ C * ‖U‖ := by
  classical
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict_of_isBounded hΩb
  obtain ⟨T, K, hT⟩ := exists_extLinear hd hΩopen hΩb hC1 hΩ'open hsub (p := 2) one_le_two
  have hbd : ∀ w ∈ goodPairs Ω, eLpNorm (T w).1 2 volume
        ≤ K * pairNorm 2 (volume.restrict Ω) w.1 w.2 ∧
      ∀ k, eLpNorm ((T w).2 k) 2 volume ≤ K * pairNorm 2 (volume.restrict Ω) w.1 w.2 :=
    fun w hw => by
      obtain ⟨-, -, -, -, -, -, h1, h2⟩ := hT w hw.1 hw.2.1 hw.2.2
      exact ⟨h1, h2⟩
  obtain ⟨ce, hce0, hces⟩ : ∃ ce : SobolevPair d ≃ₗ[ℝ]
      (Fin (d + 1) → EuclideanSpace ℝ (Fin d) → ℝ),
      (∀ p : SobolevPair d, ce p 0 = p.1) ∧ ∀ (p : SobolevPair d) k, ce p k.succ = p.2 k :=
    ⟨Fin.consLinearEquiv ℝ fun _ : Fin (d + 1) => EuclideanSpace ℝ (Fin d) → ℝ,
      fun p => by simp, fun p k => by simp⟩
  -- the operator on vectors of representatives, and the pair a vector of classes presents
  obtain ⟨T', hT'⟩ : ∃ T' : (Fin (d + 1) → EuclideanSpace ℝ (Fin d) → ℝ) →ₗ[ℝ]
      (Fin (d + 1) → EuclideanSpace ℝ (Fin d) → ℝ), ∀ f, T' f = ce (T (ce.symm f)) :=
    ⟨ce.toLinearMap ∘ₗ T ∘ₗ ce.symm.toLinearMap, fun f => rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : H1amb Ω → SobolevPair d, ∀ U, w U = ce.symm (rep U) := ⟨_, fun U => rfl⟩
  have hrep : ∀ U : H1amb Ω, ce (w U) = rep U := fun U => by rw [hwdef, ce.apply_symm_apply]
  have hw1 : ∀ U, (w U).1 = rep U 0 := fun U => by rw [← hce0, hrep U]
  have hw2 : ∀ U k, (w U).2 k = rep U k.succ := fun U k => by rw [← hces, hrep U]
  have hw : ∀ U : W12 Ω, w U ∈ goodPairs Ω := fun U => by
    refine ⟨?_, fun k => ?_, ?_⟩
    · rw [hw1]; exact (Lp.memLp _).integrable one_le_two
    · rw [hw2]; exact (Lp.memLp _).integrable one_le_two
    · rw [show (w U).1 = _ from hw1 U, show (w U).2 = _ from funext (hw2 U)]
      exact hasWeakGradOn_of_mem_W12 U.2
  have hT'0 : ∀ U : H1amb Ω, T' (rep U) 0 = (T (w U)).1 := fun U => by
    rw [hT', ← hrep U, ce.symm_apply_apply, hce0]
  have hT's : ∀ (U : H1amb Ω) k, T' (rep U) k.succ = (T (w U)).2 k := fun U k => by
    rw [hT', ← hrep U, ce.symm_apply_apply, hces]
  -- measure and bound
  have hpair : ∀ U : H1amb Ω, pairNorm 2 (volume.restrict Ω) (w U).1 (w U).2
      ≤ ENNReal.ofReal ((d + 1) * ‖U‖) := fun U => by
    rw [show (w U).1 = rep U 0 from hw1 U, show (w U).2 = fun k => rep U k.succ from funext (hw2 U)]
    exact pairNorm_rep_le U
  have hfin : ∀ U : W12 Ω, (K : ℝ≥0∞) * pairNorm 2 (volume.restrict Ω) (w U).1 (w U).2 < ⊤ :=
    fun U => ENNReal.mul_lt_top ENNReal.coe_lt_top
      (lt_of_le_of_lt (hpair U) ENNReal.ofReal_lt_top)
  have hMF : ∀ U : W12 Ω, MemLp (T (w U)).1 2 volume := fun U =>
    lt_of_le_of_lt (hbd _ (hw U)).1 (hfin U)
  have hMG : ∀ U : W12 Ω, ∀ k, MemLp ((T (w U)).2 k) 2 volume := fun U k =>
    lt_of_le_of_lt ((hbd _ (hw U)).2 k) (hfin U)
  have hmem : ∀ U ∈ W12 Ω, ∀ k, MemLp (T' (rep U) k) 2 (volume.restrict Set.univ) :=
    fun U hU k => by
      rw [Measure.restrict_univ]
      refine Fin.cases ?_ (fun k => ?_) k
      · rw [hT'0]; exact hMF ⟨U, hU⟩
      · rw [hT's]; exact hMG ⟨U, hU⟩ k
  have hbound : ∀ U ∈ W12 Ω, ∀ k, eLpNorm (T' (rep U) k) 2 (volume.restrict Set.univ)
      ≤ ENNReal.ofReal (K * (d + 1) * ‖U‖) := fun U hU k => by
    rw [Measure.restrict_univ]
    have h : (K : ℝ≥0∞) * pairNorm 2 (volume.restrict Ω) (w U).1 (w U).2
        ≤ ENNReal.ofReal (K * (d + 1) * ‖U‖) := by
      rw [mul_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
      exact mul_le_mul_right (hpair U) _
    refine Fin.cases ?_ (fun k => ?_) k
    · rw [hT'0]; exact (hbd _ (hw ⟨U, hU⟩)).1.trans h
    · rw [hT's]; exact ((hbd _ (hw ⟨U, hU⟩)).2 k).trans h
  have hcompat : ∀ f ∈ (goodPairs Ω).map (ce : SobolevPair d →ₗ[ℝ] _),
      ∀ g ∈ (goodPairs Ω).map (ce : SobolevPair d →ₗ[ℝ] _),
      (∀ i, f i =ᵐ[volume.restrict Ω] g i) → ∀ k, T' f k =ᵐ[volume.restrict Set.univ] T' g k := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hfg k
    have h := ae_eq_of_bound hbd hp hq (by simpa only [LinearEquiv.coe_coe, hce0] using hfg 0)
      (fun k => by simpa only [LinearEquiv.coe_coe, hces] using hfg k.succ)
    rw [Measure.restrict_univ]
    refine Fin.cases ?_ (fun k => ?_) k
    · simpa only [hT', LinearEquiv.coe_coe, ce.symm_apply_apply, hce0] using h.1
    · simpa only [hT', LinearEquiv.coe_coe, ce.symm_apply_apply, hces] using h.2 k
  obtain ⟨E, hE, hEn⟩ := exists_clm_of_ae_compat (W12 Ω)
    ((goodPairs Ω).map (ce : SobolevPair d →ₗ[ℝ] _)) (fun U hU => ⟨w U, hw ⟨U, hU⟩, hrep U⟩) T'
    hcompat hmem (by positivity) hbound
  have hE0 : ∀ U : W12 Ω, ⇑(E U 0) =ᵐ[volume] (T (w U)).1 := fun U => by
    simpa only [hT'0, Measure.restrict_univ] using hE U 0
  have hEs : ∀ (U : W12 Ω) k, ⇑(E U k.succ) =ᵐ[volume] (T (w U)).2 k := fun U k => by
    simpa only [hT's, Measure.restrict_univ] using hE U k.succ
  have hmemE : ∀ U : W12 Ω, (E U : H1amb Set.univ) ∈ W12 Set.univ := fun U => by
    have hF : MemLp (T (w U)).1 2 (volume.restrict Set.univ) := by
      rw [Measure.restrict_univ]; exact hMF U
    have hG : ∀ k, MemLp ((T (w U)).2 k) 2 (volume.restrict Set.univ) := fun k => by
      rw [Measure.restrict_univ]; exact hMG U k
    rw [eq_toLp_cons hF hG (E U) (by simpa only [Measure.restrict_univ] using hE0 U)
      (fun k => by simpa only [Measure.restrict_univ] using hEs U k)]
    exact mem_W12_of_hasWeakGradOn hF hG (hT _ (hw U).1 (hw U).2.1 (hw U).2.2).1
  refine ⟨E.codRestrict (W12 Set.univ) hmemE, Real.sqrt (d + 1) * (K * (d + 1)),
    fun U => ⟨?_, fun k => ?_⟩, fun U => ?_, fun U => ?_⟩
  · -- agreement of the function coordinate on the domain
    obtain ⟨-, -, -, -, -, hag, -, -⟩ := hT _ (hw U).1 (hw U).2.1 (hw U).2.2
    have h2 : (T (w U)).1 =ᵐ[volume.restrict Ω] (w U).1 :=
      (ae_restrict_iff' hΩopen.measurableSet).mpr (Eventually.of_forall hag)
    rw [hw1] at h2
    exact Filter.EventuallyEq.trans (ae_restrict_of_ae (hE0 U)) h2
  · -- agreement of the gradient coordinates, by uniqueness of the weak gradient
    obtain ⟨hwgU, -, -, -, hgint, hag, -, -⟩ := hT _ (hw U).1 (hw U).2.1 (hw U).2.2
    have hue : (w U).1 =ᵐ[volume.restrict Ω] (T (w U)).1 :=
      (ae_restrict_iff' hΩopen.measurableSet).mpr
        (Eventually.of_forall fun y hy => (hag y hy).symm)
    have hge : (T (w U)).2 k =ᵐ[volume.restrict Ω] (w U).2 k :=
      hasWeakGradOn_unique_ae hΩopen hΩopen.measurableSet (fun k => (hgint k).integrableOn)
        (hw U).2.1 (((hwgU.mono (subset_univ _)).congr_ae hue.symm fun _ => EventuallyEq.rfl))
        (hw U).2.2 k
    rw [hw2] at hge
    exact Filter.EventuallyEq.trans (ae_restrict_of_ae (hEs U k)) hge
  · -- vanishing outside the given open set
    obtain ⟨-, -, hsupp, -⟩ := hT _ (hw U).1 (hw U).2.1 (hw U).2.2
    filter_upwards [hE0 U] with y hy hyΩ'
    rw [show (((E.codRestrict (W12 Set.univ) hmemE U : W12 Set.univ) : H1amb Set.univ) 0 :
      EuclideanSpace ℝ (Fin d) → ℝ) y = E U 0 y from rfl, hy]
    exact image_eq_zero_of_notMem_tsupport fun hc => hyΩ' (hsupp hc)
  · simpa [mul_assoc] using hEn U

end EllipticPdes.Extension
