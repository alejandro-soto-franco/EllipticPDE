/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticDirichlet.Regularity.RestrictedDiffQuotientMem
import EllipticDirichlet.Regularity.CoeffC1
import EllipticDirichlet.Regularity.CutoffTower

/-!
# The master interior difference-quotient energy estimate

The interior second-derivative estimate (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1; Gilbarg-Trudinger, *Elliptic PDE of Second Order*, Theorem 8.8) proceeds by testing
the weak formulation of `L u = f` with the difference-quotient test element
`v_h = -Dₖ^{-h}(ξ² Dₖ^h u)`, using discrete integration by parts to move the outer difference
quotient onto the coefficient factor, uniform ellipticity from below to control the leading
term, and Cauchy-Schwarz together with the Peter-Paul (Young) inequality to absorb the
commutator, cross, zeroth-order, and right-hand terms.

## Main declarations

* `evansTest`: the admissible test element `v_h = -Dₖ^{-h}(ξ² Dₖ^h u) ∈ H₀¹(Ω)`, whose
  membership is two applications of `cutoffMul_diffQuotG_mem_H01`.
-/

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticDirichlet.Regularity

open EllipticDirichlet.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
  {ξ θ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ### D1: The admissible Evans test element -/

/-- **The admissible Evans test element** `v_h = -Dₖ^{-h}(ξ² Dₖ^h u) ∈ H₀¹(Ω)`. The inner
cutoff `ξ²` and the outer cutoff `θ` (which is `≡ 1` on `tsupport ξ`) localise the two
difference quotients so that the composite stays inside `H₀¹(Ω)`; membership is two
applications of the crux admissibility lemma `cutoffMul_diffQuotG_mem_H01`, together with
closure of the submodule under negation. This is the single admissible test vector that the
weak formulation consumes in the difference-quotient energy method (Evans, *Partial
Differential Equations* (2nd ed.), §6.3.1). -/
noncomputable def evansTest (hΩm : MeasurableSet Ω) (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ)
    (k : Fin d) (h : ℝ)
    (hsm_in : ∀ x ∈ tsupport (fun y => ξ y * ξ y), x + hshift k h ∈ Ω)
    (hsm_out : ∀ x ∈ tsupport θ, x + hshift k (-h) ∈ Ω) (u : H01 Ω) : H01 Ω :=
  ⟨-(cutoffMul hθ (diffQuotG k (-h) hΩm
      (cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))))),
    Submodule.neg_mem _
      (cutoffMul_diffQuotG_mem_H01 hθ k hΩm hsm_out
        (cutoffMul_diffQuotG_mem_H01 (isTestFn_mul hξ hξ) k hΩm hsm_in u.2))⟩

/-- The ambient-graph value of `evansTest` is the negated cutoff of the outer difference
quotient of `ξ² Dₖ^h u`. -/
theorem evansTest_coe (hΩm : MeasurableSet Ω) (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ)
    (k : Fin d) (h : ℝ)
    (hsm_in : ∀ x ∈ tsupport (fun y => ξ y * ξ y), x + hshift k h ∈ Ω)
    (hsm_out : ∀ x ∈ tsupport θ, x + hshift k (-h) ∈ Ω) (u : H01 Ω) :
    (evansTest hΩm hξ hθ k h hsm_in hsm_out u : H1amb Ω)
      = -(cutoffMul hθ (diffQuotG k (-h) hΩm
          (cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))))) :=
  rfl

/-! ### D2 core: support control and θ-invisibility -/

/-- A cutoff-multiplied class vanishes a.e. off the topological support of the cutoff. -/
private lemma mulTest_ae_eq_zero_off_tsupport {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hη : IsTestFn Ω η) (g : L2D Ω) :
    ∀ᵐ x ∂(volume.restrict Ω),
      x ∉ tsupport η → (mulTest hη g x : ℝ) = 0 := by
  filter_upwards [mulTest_coeFn hη g] with x hx hxns
  rw [hx, image_eq_zero_of_notMem_tsupport hxns, zero_mul]

/-- **Support of the interior difference quotient.** If a class `g` has whole-space extension
a.e. supported in a measurable set `S`, then its interior difference quotient `diffQuotD k h g`
vanishes (a.e. on `Ω`) outside `S ∪ (S - h eₖ)`: the numerator
`extendL2 g (x + h eₖ) - g x` can be nonzero only when `x ∈ S` (through `g x`) or
`x + h eₖ ∈ S` (through the translate). -/
private lemma diffQuotD_ae_eq_zero_off (hΩm : MeasurableSet Ω) (k : Fin d) {h : ℝ}
    (g : L2D Ω) {S : Set (EuclideanSpace ℝ (Fin d))}
    (hgS : ∀ᵐ x ∂volume, (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) x ≠ 0 → x ∈ S) :
    ∀ᵐ x ∂(volume.restrict Ω),
      x ∉ S → x + hshift k h ∉ S → (diffQuotD k h hΩm g x : ℝ) = 0 := by
  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving (· + hshift k h) volume volume :=
    (measurePreserving_add_right volume (hshift k h)).quasiMeasurePreserving
  have hgS_shift : ∀ᵐ x ∂volume,
      (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) (x + hshift k h) ≠ 0 →
        x + hshift k h ∈ S := hqmp.ae hgS
  filter_upwards [coeFn_diffQuotD k h hΩm g, ae_restrict_of_ae hgS,
    ae_restrict_of_ae hgS_shift, ae_restrict_of_ae (coeFn_extendL2 hΩm g),
    ae_restrict_mem hΩm] with x hdq hgx hgxs hext hmem hxS hxsS
  rw [hdq]
  have h1 : (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) (x + hshift k h) = 0 := by
    by_contra hne; exact hxsS (hgxs hne)
  have h2 : (g x : ℝ) = 0 := by
    by_contra hne
    refine hxS (hgx ?_)
    rw [hext, Set.indicator_of_mem hmem]; exact hne
  rw [h1, h2, sub_zero, zero_div]

/-- **θ-chop invisibility.** If `g`'s extension is a.e. supported in `S` and the outer cutoff
`θ ≡ 1` on the part of `Ω` reachable into `S` by the shift, then multiplying `θ` onto the
interior difference quotient of `g` is invisible: `θ · Dₖʰ g = Dₖʰ g`. This is what lets the
outer cutoff of the Evans test element drop out of the energy identity (Evans, *Partial
Differential Equations* (2nd ed.), §6.3.1). -/
private lemma mulTest_theta_diffQuotD (hΩm : MeasurableSet Ω) (hθ : IsTestFn Ω θ)
    (k : Fin d) {h : ℝ} (g : L2D Ω) {S : Set (EuclideanSpace ℝ (Fin d))}
    (hgS : ∀ᵐ x ∂volume, (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) x ≠ 0 → x ∈ S)
    (hθ1 : ∀ x ∈ Ω, x ∈ S ∨ x + hshift k h ∈ S → θ x = 1) :
    mulTest hθ (diffQuotD k h hΩm g) = diffQuotD k h hΩm g := by
  apply Lp.ext
  filter_upwards [mulTest_coeFn hθ (diffQuotD k h hΩm g),
    diffQuotD_ae_eq_zero_off hΩm k g hgS, ae_restrict_mem hΩm] with x hmt hzero hmem
  rw [hmt]
  by_cases hd : (diffQuotD k h hΩm g x : ℝ) = 0
  · rw [hd, mul_zero]
  · have hmemS : x ∈ S ∨ x + hshift k h ∈ S := by
      by_contra hc; exact hd (hzero (not_or.mp hc).1 (not_or.mp hc).2)
    rw [hθ1 x hmem hmemS, one_mul]

/-- **θ-cross-term vanishing.** Under the same support and `θ ≡ 1` conditions (so that
`∂ⱼθ = 0` on the reachable part of `Ω`), the partial-cutoff multiplier annihilates the
interior difference quotient: `(∂ⱼθ) · Dₖʰ g = 0`. This kills the outer-cutoff cross term of
the Evans test element, which would otherwise be a second-order (double difference-quotient)
object beyond the reach of the data bound (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1). -/
private lemma mulTestPartial_theta_diffQuotD (hΩm : MeasurableSet Ω) (hθ : IsTestFn Ω θ)
    (j k : Fin d) {h : ℝ} (g : L2D Ω) {S : Set (EuclideanSpace ℝ (Fin d))}
    (hgS : ∀ᵐ x ∂volume, (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) x ≠ 0 → x ∈ S)
    (hθ0 : ∀ x ∈ Ω, x ∈ S ∨ x + hshift k h ∈ S → partialD j θ x = 0) :
    mulTestPartial hθ j (diffQuotD k h hΩm g) = 0 := by
  apply Lp.ext
  filter_upwards [mulTestPartial_coeFn hθ j (diffQuotD k h hΩm g),
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volume.restrict Ω),
    diffQuotD_ae_eq_zero_off hΩm k g hgS, ae_restrict_mem hΩm] with x hmtp hz hzero hmem
  rw [hmtp, hz, Pi.zero_apply]
  by_cases hd : (diffQuotD k h hΩm g x : ℝ) = 0
  · rw [hd, mul_zero]
  · have hmemS : x ∈ S ∨ x + hshift k h ∈ S := by
      by_contra hc; exact hd (hzero (not_or.mp hc).1 (not_or.mp hc).2)
    rw [hθ0 x hmem hmemS, zero_mul]

/-! ### D2 core: discrete integration by parts -/

/-- **Discrete integration by parts, principal term.** For a class `p` whose whole-space
extension stays supported inside `Ω` after the backward shift, the restricted-domain pairing
of the coefficient action against the backward interior difference quotient of `p` transfers,
via the extension isometry and the whole-space adjoint relation `diffQuot_inner_adjoint`,
into minus the whole-space pairing of the *forward* difference quotient of the coefficient
action against `extendL2 p`. This is the discrete analogue of moving the derivative off the
test factor onto the coefficient factor (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1, proof of Theorem 3). -/
private lemma actL_diffQuotD_ibp (A : EllipticCoeff d) (hΩm : MeasurableSet Ω)
    (i j k : Fin d) {h : ℝ} (g p : L2D Ω)
    (hsupp : ∀ᵐ x ∂volume,
      (extendL2 hΩm p : EuclideanSpace ℝ (Fin d) → ℝ) (x + hshift k (-h)) ≠ 0 → x ∈ Ω) :
    ⟪A.actL i j g, diffQuotD k (-h) hΩm p⟫
      = -⟪diffQuot k h (extendL2 hΩm (A.actL i j g)), extendL2 hΩm p⟫ := by
  rw [← (extendL2 hΩm).inner_map_map (A.actL i j g) (diffQuotD k (-h) hΩm p),
    extendL2_diffQuotD_eq k (-h) hΩm p hsupp,
    diffQuot_inner_adjoint k h (extendL2 hΩm (A.actL i j g)) (extendL2 hΩm p)]
  exact (neg_neg _).symm

/-! ### D2 core: support of the inner cutoff data and the Evans coordinate reduction -/

/-- If a class `g` vanishes a.e. (on `Ω`) off a set `S`, then its extension by zero to the
whole space is a.e. supported in `S`. -/
private lemma extendL2_supp_of_ae_restrict (hΩm : MeasurableSet Ω) (g : L2D Ω)
    {S : Set (EuclideanSpace ℝ (Fin d))}
    (hg : ∀ᵐ x ∂(volume.restrict Ω), x ∉ S → (g x : ℝ) = 0) :
    ∀ᵐ x ∂volume, (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) x ≠ 0 → x ∈ S := by
  filter_upwards [coeFn_extendL2 hΩm g, ae_imp_of_ae_restrict hg] with x hx himp
  rw [hx]; intro hne
  by_cases hxΩ : x ∈ Ω
  · by_contra hxS
    rw [Set.indicator_of_mem hxΩ] at hne
    exact hne (himp hxΩ hxS)
  · rw [Set.indicator_of_notMem hxΩ] at hne; exact absurd rfl hne

/-- **Support of the inner cutoff data.** Every ambient coordinate of the inner block
`ξ² · Dₖ^h u` has whole-space extension a.e. supported in `tsupport ξ²`: the zeroth
coordinate is `ξ² · Dₖ^h u₀`, and the `i+1` coordinate is
`ξ² · Dₖ^h ∂ᵢu + (∂ᵢξ²) · Dₖ^h u₀`, both of which carry the factor `ξ²` (or its partial,
whose support is smaller). -/
private lemma diffQuotG_cutoffSq_supp (hξ : IsTestFn Ω ξ) (hΩm : MeasurableSet Ω)
    (k : Fin d) (h : ℝ) (u : H1amb Ω) (j : Fin (d + 1)) :
    ∀ᵐ x ∂volume,
      (extendL2 hΩm ((cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm u)) j)
          : EuclideanSpace ℝ (Fin d) → ℝ) x ≠ 0
        → x ∈ tsupport (fun y => ξ y * ξ y) := by
  apply extendL2_supp_of_ae_restrict
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [cutoffMul_apply_zero, diffQuotG_apply]
    exact mulTest_ae_eq_zero_off_tsupport (isTestFn_mul hξ hξ) _
  · rw [cutoffMul_apply_succ, diffQuotG_apply, diffQuotG_apply]
    filter_upwards [Lp.coeFn_add
        (mulTest (isTestFn_mul hξ hξ) (diffQuotD k h hΩm (u i.succ)))
        (mulTestPartial (isTestFn_mul hξ hξ) i (diffQuotD k h hΩm (u 0))),
      mulTest_coeFn (isTestFn_mul hξ hξ) (diffQuotD k h hΩm (u i.succ)),
      mulTestPartial_coeFn (isTestFn_mul hξ hξ) i (diffQuotD k h hΩm (u 0))]
      with x hadd hmt hmtp hxS
    have hsq : ξ x * ξ x = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => ξ y * ξ y) hxS
    have hpsq : partialD i (fun y => ξ y * ξ y) x = 0 :=
      image_eq_zero_of_notMem_tsupport (f := partialD i (fun y => ξ y * ξ y))
        (fun hc => hxS (tsupport_partialD_subset i _ hc))
    rw [hadd, Pi.add_apply, hmt, hmtp, hsq, hpsq, zero_mul, zero_mul, add_zero]

/-- **Evans test element, successor coordinate.** Under the outer-cutoff reachability
conditions (`θ ≡ 1`, hence `∂θ = 0`, on the shift-reachable part of `tsupport ξ²`), the
`j+1` coordinate of the admissible test element reduces to a single backward difference
quotient of the inner block: `(v_h)_{j+1} = -Dₖ^{-h}((ξ²·Dₖ^h u)_{j+1})`. This is the
θ-chop invisibility together with the vanishing of the outer-cutoff cross term (Evans,
*Partial Differential Equations* (2nd ed.), §6.3.1). -/
private lemma evansTest_succ_eq (hΩm : MeasurableSet Ω) (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ)
    (k : Fin d) (h : ℝ)
    (hsm_in : ∀ x ∈ tsupport (fun y => ξ y * ξ y), x + hshift k h ∈ Ω)
    (hsm_out : ∀ x ∈ tsupport θ, x + hshift k (-h) ∈ Ω) (u : H01 Ω) (j : Fin d)
    (hθ1 : ∀ x ∈ Ω,
      x ∈ tsupport (fun y => ξ y * ξ y) ∨ x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y)
        → θ x = 1)
    (hθ0 : ∀ x ∈ Ω,
      x ∈ tsupport (fun y => ξ y * ξ y) ∨ x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y)
        → partialD j θ x = 0) :
    (evansTest hΩm hξ hθ k h hsm_in hsm_out u : H1amb Ω) j.succ
      = -diffQuotD k (-h) hΩm
          ((cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))) j.succ) := by
  set Z : H1amb Ω := cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω)) with hZ
  have hcoe : (evansTest hΩm hξ hθ k h hsm_in hsm_out u : H1amb Ω) j.succ
      = -(cutoffMul hθ (diffQuotG k (-h) hΩm Z)) j.succ := by
    rw [evansTest_coe]; rfl
  rw [hcoe, cutoffMul_apply_succ, diffQuotG_apply, diffQuotG_apply]
  have hvis : mulTest hθ (diffQuotD k (-h) hΩm (Z j.succ)) = diffQuotD k (-h) hΩm (Z j.succ) :=
    mulTest_theta_diffQuotD hΩm hθ k (Z j.succ)
      (diffQuotG_cutoffSq_supp hξ hΩm k h (u : H1amb Ω) j.succ) hθ1
  have hcross : mulTestPartial hθ j (diffQuotD k (-h) hΩm (Z 0)) = 0 :=
    mulTestPartial_theta_diffQuotD hΩm hθ j k (Z 0)
      (diffQuotG_cutoffSq_supp hξ hΩm k h (u : H1amb Ω) 0) hθ0
  rw [hvis, hcross, add_zero]

/-- **Evans bilinear identity after discrete integration by parts.** Testing the principal
bilinear form with the Evans test element, the coordinate reduction `evansTest_succ_eq`
followed by the discrete integration-by-parts identity `actL_diffQuotD_ibp` moves the
backward difference quotient off the test factor onto the coefficient action, yielding the
whole-space pairing of the forward difference quotient of the coefficient-weighted gradient
against the inner cutoff block (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1). -/
private lemma evansTest_bilin_ibp (A : EllipticCoeff d) (hΩm : MeasurableSet Ω)
    (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ) (k : Fin d) (h : ℝ)
    (hsm_in : ∀ x ∈ tsupport (fun y => ξ y * ξ y), x + hshift k h ∈ Ω)
    (hsm_out : ∀ x ∈ tsupport θ, x + hshift k (-h) ∈ Ω)
    (hθ1 : ∀ x ∈ Ω,
      x ∈ tsupport (fun y => ξ y * ξ y) ∨ x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y)
        → θ x = 1)
    (hθ0 : ∀ (j : Fin d), ∀ x ∈ Ω,
      x ∈ tsupport (fun y => ξ y * ξ y) ∨ x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y)
        → partialD j θ x = 0) (u : H01 Ω) :
    A.bilin Ω u (evansTest hΩm hξ hθ k h hsm_in hsm_out u)
      = ∑ i : Fin d, ∑ j : Fin d,
        ⟪diffQuot k h (extendL2 hΩm (A.actL i j ((u : H1amb Ω) i.succ))),
          extendL2 hΩm
            ((cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))) j.succ)⟫ := by
  rw [EllipticCoeff.bilin_apply]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  set Z : H1amb Ω := cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω)) with hZ
  have hsupp_j : ∀ᵐ x ∂volume,
      (extendL2 hΩm (Z j.succ) : EuclideanSpace ℝ (Fin d) → ℝ) (x + hshift k (-h)) ≠ 0
        → x ∈ Ω := by
    have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving
        (· + hshift k (-h)) volume volume :=
      (measurePreserving_add_right volume (hshift k (-h))).quasiMeasurePreserving
    filter_upwards [hqmp.ae (diffQuotG_cutoffSq_supp hξ hΩm k h (u : H1amb Ω) j.succ)]
      with x hx hne
    have hxS : x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y) := hx hne
    have hxeq : x = (x + hshift k (-h)) + hshift k h := by rw [hshift_neg]; abel
    rw [hxeq]; exact hsm_in _ hxS
  rw [show ((evansTest hΩm hξ hθ k h hsm_in hsm_out u : H1amb Ω) j.succ)
        = -diffQuotD k (-h) hΩm (Z j.succ) from
      evansTest_succ_eq hΩm hξ hθ k h hsm_in hsm_out u j hθ1 (hθ0 j),
    inner_neg_right, actL_diffQuotD_ibp A hΩm i j k ((u : H1amb Ω) i.succ) (Z j.succ) hsupp_j,
    neg_neg]

/-- Restriction to `Ω` is non-expansive on `L²`: `‖restrictL2 w‖ ≤ ‖w‖`. -/
private lemma norm_restrictL2_le (hΩm : MeasurableSet Ω) (w : EucL2 d) :
    ‖restrictL2 hΩm w‖ ≤ ‖w‖ :=
  norm_Lp_toLp_restrict_le Ω w

/-- The interior difference quotient is the restriction of the whole-space difference
quotient of the extension: `Dₖʰ g = restrict (Dₖʰ (extendL2 g))`. -/
private lemma diffQuotD_eq_restrictL2_diffQuot (hΩm : MeasurableSet Ω) (k : Fin d) (h : ℝ)
    (g : L2D Ω) :
    diffQuotD k h hΩm g = restrictL2 hΩm (diffQuot k h (extendL2 hΩm g)) := by
  apply Lp.ext
  filter_upwards [coeFn_diffQuotD k h hΩm g,
    coeFn_restrictL2 hΩm (diffQuot k h (extendL2 hΩm g)),
    ae_restrict_of_ae (coeFn_diffQuot k h (extendL2 hΩm g)),
    ae_restrict_of_ae (coeFn_extendL2 hΩm g), ae_restrict_mem hΩm] with x hx1 hx2 hx3 hx4 hx5
  rw [hx1, hx2, hx3, hx4, Set.indicator_of_mem hx5]

/-- **Evans test element, zeroth coordinate.** The function value of the test element is a
single backward difference quotient of the inner block, `(v_h)₀ = -Dₖ^{-h}((ξ²·Dₖ^h u)₀)`,
by θ-chop invisibility (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1). -/
private lemma evansTest_zero_eq (hΩm : MeasurableSet Ω) (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ)
    (k : Fin d) (h : ℝ)
    (hsm_in : ∀ x ∈ tsupport (fun y => ξ y * ξ y), x + hshift k h ∈ Ω)
    (hsm_out : ∀ x ∈ tsupport θ, x + hshift k (-h) ∈ Ω) (u : H01 Ω)
    (hθ1 : ∀ x ∈ Ω,
      x ∈ tsupport (fun y => ξ y * ξ y) ∨ x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y)
        → θ x = 1) :
    (evansTest hΩm hξ hθ k h hsm_in hsm_out u : H1amb Ω) 0
      = -diffQuotD k (-h) hΩm
          ((cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))) 0) := by
  set Z : H1amb Ω := cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω)) with hZ
  have hcoe : (evansTest hΩm hξ hθ k h hsm_in hsm_out u : H1amb Ω) 0
      = -(cutoffMul hθ (diffQuotG k (-h) hΩm Z)) 0 := by rw [evansTest_coe]; rfl
  rw [hcoe, cutoffMul_apply_zero, diffQuotG_apply]
  rw [mulTest_theta_diffQuotD hΩm hθ k (Z 0)
    (diffQuotG_cutoffSq_supp hξ hΩm k h (u : H1amb Ω) 0) hθ1]

/-- **Evans bilinear identity, restricted-domain form.** Bringing the whole-space pairing of
`evansTest_bilin_ibp` back to `L²(Ω)` through the extension adjoint and the identity
`diffQuotD = restrict ∘ diffQuot ∘ extendL2`, the principal form testing against the Evans
element is the restricted-domain pairing of the inner cutoff block against the interior
difference quotient of the coefficient action (Evans, *Partial Differential Equations*
(2nd ed.), §6.3.1). -/
private lemma evansTest_bilin_L2D (A : EllipticCoeff d) (hΩm : MeasurableSet Ω)
    (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ) (k : Fin d) (h : ℝ)
    (hsm_in : ∀ x ∈ tsupport (fun y => ξ y * ξ y), x + hshift k h ∈ Ω)
    (hsm_out : ∀ x ∈ tsupport θ, x + hshift k (-h) ∈ Ω)
    (hθ1 : ∀ x ∈ Ω,
      x ∈ tsupport (fun y => ξ y * ξ y) ∨ x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y)
        → θ x = 1)
    (hθ0 : ∀ (j : Fin d), ∀ x ∈ Ω,
      x ∈ tsupport (fun y => ξ y * ξ y) ∨ x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y)
        → partialD j θ x = 0) (u : H01 Ω) :
    A.bilin Ω u (evansTest hΩm hξ hθ k h hsm_in hsm_out u)
      = ∑ i : Fin d, ∑ j : Fin d,
        ⟪(cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))) j.succ,
          diffQuotD k h hΩm (A.actL i j ((u : H1amb Ω) i.succ))⟫ := by
  rw [evansTest_bilin_ibp A hΩm hξ hθ k h hsm_in hsm_out hθ1 hθ0 u]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [real_inner_comm, extendL2_inner_restrictL2, ← diffQuotD_eq_restrictL2_diffQuot]

/-! ### D2 core: the extension-by-zero weak derivative and the first-order global energy -/

/-- **Extension by zero of an `H₀¹` element carries the weak gradient.** For `u ∈ H₀¹(Ω)`,
the whole-space extension by zero of the function value `u₀` has whole-space `L²` weak
`k`-derivative equal to the extension by zero of the gradient component `u_{k+1}`. Because
`u` vanishes at the boundary (it lies in the closure of the compactly supported test
functions), no boundary term appears when integrating against an arbitrary whole-space test
function `φ`: the identity `∫ (extendL2 u₀) ∂ₖφ = -∫ (extendL2 u_{k+1}) φ` is closed under
`L²` limits and holds on every test-function graph by classical integration by parts, hence
on the whole of `H₀¹(Ω)` (Evans, *Partial Differential Equations* (2nd ed.), §5.8.2). -/
theorem hasWeakDeriv_extendL2_of_mem_H01 (hΩm : MeasurableSet Ω) (k : Fin d)
    {U : H1amb Ω} (hU : U ∈ H01 Ω) :
    HasWeakDeriv k (extendL2 hΩm (U 0)) (extendL2 hΩm (U k.succ)) := by
  intro φ hφcd hφcs
  have hφL2 : MemLp φ 2 volume := hφcd.continuous.memLp_of_hasCompactSupport hφcs
  have hφpc : Continuous (partialD k φ) :=
    (hφcd.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφpcs : HasCompactSupport (partialD k φ) :=
    hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  have hφpL2 : MemLp (partialD k φ) 2 volume := hφpc.memLp_of_hasCompactSupport hφpcs
  set a : EucL2 d := hφpL2.toLp (partialD k φ) with ha
  set b : EucL2 d := hφL2.toLp φ with hb
  set w₀ : H1amb Ω := PiLp.single 2 (0 : Fin (d + 1)) (restrictL2 hΩm a)
      + PiLp.single 2 k.succ (restrictL2 hΩm b) with hw₀
  -- The inner product against `w₀` extracts the two extension-by-zero pairings.
  have hΦ : ∀ V : H1amb Ω, ⟪w₀, V⟫
      = ⟪extendL2 hΩm (V 0), a⟫ + ⟪extendL2 hΩm (V k.succ), b⟫ := by
    intro V
    rw [extendL2_inner_restrictL2 hΩm (V 0) a, extendL2_inner_restrictL2 hΩm (V k.succ) b,
      hw₀, inner_add_left, inner_single_left, inner_single_left]
    congr 1 <;> exact real_inner_comm _ _
  -- On a test-function graph `w₀` is orthogonal: classical integration by parts.
  have hbase : ∀ V ∈ testGraphSet Ω, ⟪w₀, V⟫ = 0 := by
    rintro _ ⟨ψ, hψ, rfl⟩
    rw [hΦ, IsTestFn.testGraph_zero, IsTestFn.testGraph_succ]
    have hext0 : (extendL2 hΩm hψ.testCls : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume] ψ := by
      filter_upwards [coeFn_extendL2 hΩm hψ.testCls,
        ae_imp_of_ae_restrict hψ.mem_lp.coeFn_toLp] with x hx himp
      rw [hx]
      by_cases hxΩ : x ∈ Ω
      · rw [Set.indicator_of_mem hxΩ]; exact himp hxΩ
      · rw [Set.indicator_of_notMem hxΩ,
          image_eq_zero_of_notMem_tsupport (fun hc => hxΩ (hψ.2.2 hc))]
    have hextk : (extendL2 hΩm (hψ.partialCls k) : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume] partialD k ψ := by
      filter_upwards [coeFn_extendL2 hΩm (hψ.partialCls k),
        ae_imp_of_ae_restrict (hψ.memLp_partialD k).coeFn_toLp] with x hx himp
      rw [hx]
      by_cases hxΩ : x ∈ Ω
      · rw [Set.indicator_of_mem hxΩ]; exact himp hxΩ
      · rw [Set.indicator_of_notMem hxΩ,
          image_eq_zero_of_notMem_tsupport
            (fun hc => hxΩ (hψ.2.2 (tsupport_partialD_subset k ψ hc)))]
    have hI0 : ⟪extendL2 hΩm hψ.testCls, a⟫ = ∫ x, ψ x * partialD k φ x := by
      rw [L2.inner_def]; refine integral_congr_ae ?_
      filter_upwards [hext0, hφpL2.coeFn_toLp] with x hx hax
      rw [Real.inner_apply, hx, hax]
    have hIk : ⟪extendL2 hΩm (hψ.partialCls k), b⟫ = ∫ x, partialD k ψ x * φ x := by
      rw [L2.inner_def]; refine integral_congr_ae ?_
      filter_upwards [hextk, hφL2.coeFn_toLp] with x hx hbx
      rw [Real.inner_apply, hx, hbx]
    rw [hI0, hIk]
    have hIBP : (∫ x, φ x * partialD k ψ x) = -∫ x, partialD k φ x * ψ x :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
        (f := φ) (g := ψ) (v := EuclideanSpace.single k (1 : ℝ))
        ((hφpc.mul hψ.continuous).integrable_of_hasCompactSupport hφpcs.mul_right)
        ((hφcd.continuous.mul (hψ.continuous_partialD k)).integrable_of_hasCompactSupport
          hφcs.mul_right)
        ((hφcd.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hφcs.mul_right)
        (fun x _ => (hφcd.differentiable (by simp)).differentiableAt)
        (fun x _ => (hψ.1.differentiable (by simp)).differentiableAt)
    rw [show (∫ x, ψ x * partialD k φ x) = ∫ x, partialD k φ x * ψ x from
          integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _),
      show (∫ x, partialD k ψ x * φ x) = ∫ x, φ x * partialD k ψ x from
          integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _),
      hIBP]
    ring
  -- `w₀` is orthogonal to the span, hence to its closure `H₀¹(Ω)`.
  have hUperp : U ∈ (Submodule.span ℝ {w₀})ᗮ := by
    have hle : Submodule.span ℝ (testGraphSet Ω) ≤ (Submodule.span ℝ {w₀})ᗮ := by
      rw [Submodule.span_le]
      intro V hV
      rw [SetLike.mem_coe, Submodule.mem_orthogonal]
      intro u hu
      rw [Submodule.mem_span_singleton] at hu
      obtain ⟨c, rfl⟩ := hu
      rw [inner_smul_left, hbase V hV, mul_zero]
    exact (Submodule.span ℝ (testGraphSet Ω)).topologicalClosure_minimal hle
      (Submodule.isClosed_orthogonal _) hU
  rw [Submodule.mem_orthogonal] at hUperp
  have hzero := hUperp w₀ (Submodule.mem_span_singleton_self w₀)
  rw [hΦ] at hzero
  -- Convert the two extension pairings back to integrals to match `HasWeakDeriv`.
  have hLconv : ⟪extendL2 hΩm (U 0), a⟫
      = ∫ x, ((extendL2 hΩm (U 0)) x : ℝ) * partialD k φ x := by
    rw [L2.inner_def]; refine integral_congr_ae ?_
    filter_upwards [hφpL2.coeFn_toLp] with x hax
    rw [Real.inner_apply, hax]
  have hRconv : ⟪extendL2 hΩm (U k.succ), b⟫
      = ∫ x, ((extendL2 hΩm (U k.succ)) x : ℝ) * φ x := by
    rw [L2.inner_def]; refine integral_congr_ae ?_
    filter_upwards [hφL2.coeFn_toLp] with x hbx
    rw [Real.inner_apply, hbx]
  rw [hLconv, hRconv] at hzero
  linarith [hzero]

/-- **The first-order global energy estimate.** For a weak solution `u ∈ H₀¹(Ω)` of
`L u = f` whose transport field `b` vanishes and whose zeroth-order coefficient `c` is
nonnegative (a.e. on `Ω`), the full gradient energy is bounded by the data:
`λ ∑ᵢ ‖u_{i+1}‖² ≤ ‖f‖ · ‖u₀‖`. Testing the weak formulation with `u` itself, ellipticity
bounds the principal part from below, the transport term drops (`b = 0`) and the
zeroth-order term has a sign (`c ≥ 0`), so only the right-hand pairing `⟪f, u₀⟫` survives
(Evans, *Partial Differential Equations* (2nd ed.), §6.2.2). -/
theorem firstOrder_energy_le (Op : FullEllipticOp d)
    (hb0 : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc0 : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x) (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ v : H01 Ω, Op.fullBilin Ω u v
      = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) :
    Op.lam * ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ ^ 2 ≤ ‖f‖ * ‖(u : H1amb Ω) 0‖ := by
  have hbz : ∀ i : Fin d,
      ⟪Op.bAct i ((u : H1amb Ω) i.succ), ((u : H1amb Ω) 0)⟫ = 0 := by
    intro i
    rw [FullEllipticOp.bAct, inner_mulCoeffL_eq]
    have hz : (fun x => Op.b x i * ((u : H1amb Ω) i.succ x : ℝ) * ((u : H1amb Ω) 0 x : ℝ))
        =ᵐ[volume.restrict Ω] 0 := by
      filter_upwards [hb0 i] with x hx; simp [hx]
    rw [integral_congr_ae hz]; simp
  have hcnn : 0 ≤ ⟪Op.cAct ((u : H1amb Ω) 0), ((u : H1amb Ω) 0)⟫ := by
    rw [FullEllipticOp.cAct, inner_mulCoeffL_eq]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hc0] with x hx
    have hsq : Op.c x * ((u : H1amb Ω) 0 x : ℝ) * ((u : H1amb Ω) 0 x : ℝ)
        = Op.c x * ((u : H1amb Ω) 0 x : ℝ) ^ 2 := by ring
    rw [Pi.zero_apply, hsq]; positivity
  have hfull := hu u
  rw [Op.fullBilin_apply, Op.lowerBilin_apply,
    Finset.sum_eq_zero (fun i _ => hbz i), zero_add] at hfull
  have hge : Op.lam * ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ ^ 2
      ≤ Op.toEllipticCoeff.bilin Ω u u := Op.toEllipticCoeff.bilin_self_ge u
  have hfu : (∫ x in Ω, (f x : ℝ) * ((u : H1amb Ω) 0 x : ℝ)) ≤ ‖f‖ * ‖(u : H1amb Ω) 0‖ := by
    have heq : (∫ x in Ω, (f x : ℝ) * ((u : H1amb Ω) 0 x : ℝ)) = ⟪f, (u : H1amb Ω) 0⟫ := by
      rw [L2.inner_def]; refine integral_congr_ae ?_
      filter_upwards with x; rw [Real.inner_apply]
    rw [heq]; exact real_inner_le_norm _ _
  linarith [hge, hcnn, hfu, hfull]

/-- **The difference quotient of `u₀` is controlled by the gradient.** For `u ∈ H₀¹(Ω)`,
the interior difference quotient of the function value is bounded in `L²` by the `k`-th
gradient component, uniformly in the step `h`: `‖Dₖ^h u₀‖ ≤ ‖u_{k+1}‖`. This composes the
weak-derivative difference-quotient bound `norm_diffQuot_le_of_hasWeakDeriv` with the
extension-by-zero weak gradient `hasWeakDeriv_extendL2_of_mem_H01`, through the non-expansive
restriction (Evans, *Partial Differential Equations* (2nd ed.), §5.8.2). -/
private lemma norm_diffQuotD_u0_le (hΩm : MeasurableSet Ω) (k : Fin d) (h : ℝ) (u : H01 Ω) :
    ‖diffQuotD k h hΩm ((u : H1amb Ω) 0)‖ ≤ ‖(u : H1amb Ω) k.succ‖ :=
  calc ‖diffQuotD k h hΩm ((u : H1amb Ω) 0)‖
      = ‖restrictL2 hΩm (diffQuot k h (extendL2 hΩm ((u : H1amb Ω) 0)))‖ := by
        rw [diffQuotD_eq_restrictL2_diffQuot]
    _ ≤ ‖diffQuot k h (extendL2 hΩm ((u : H1amb Ω) 0))‖ := norm_restrictL2_le hΩm _
    _ ≤ ‖extendL2 hΩm ((u : H1amb Ω) k.succ)‖ :=
        norm_diffQuot_le_of_hasWeakDeriv k (extendL2 hΩm ((u : H1amb Ω) 0))
          (extendL2 hΩm ((u : H1amb Ω) k.succ))
          (hasWeakDeriv_extendL2_of_mem_H01 hΩm k u.2) h
    _ = ‖(u : H1amb Ω) k.succ‖ := norm_extendL2 hΩm _

/-! ### D2 core: the master assembly toolkit -/

/-- Operator-norm bound for the cutoff multiplier: `‖ξ · g‖ ≤ ‖ξ‖∞ · ‖g‖`. -/
private lemma norm_mulTest_le (hξ : IsTestFn Ω ξ) (g : L2D Ω) :
    ‖mulTest hξ g‖ ≤ (exists_abs_bound hξ).choose * ‖g‖ :=
  norm_mulCoeffL_le _ _ g

/-- Operator-norm bound for the partial-cutoff multiplier: `‖(∂ᵢξ) · g‖ ≤ ‖∂ᵢξ‖∞ · ‖g‖`. -/
private lemma norm_mulTestPartial_le (hξ : IsTestFn Ω ξ) (i : Fin d) (g : L2D Ω) :
    ‖mulTestPartial hξ i g‖ ≤ (exists_abs_bound_partialD hξ i).choose * ‖g‖ :=
  norm_mulCoeffL_le _ _ g

/-- Regrouping one `ξ` factor across the coefficient action, principal part:
`⟪aᵢⱼ (ξ p), ξ q⟫ = ⟪aᵢⱼ p, ξ² q⟫`. -/
private lemma actL_mulTest_regroup (A : EllipticCoeff d) (hξ : IsTestFn Ω ξ)
    (i j : Fin d) (p q : L2D Ω) :
    ⟪A.actL i j (mulTest hξ p), mulTest hξ q⟫
      = ⟪A.actL i j p, mulTest (isTestFn_mul hξ hξ) q⟫ := by
  rw [A.inner_actL_eq, A.inner_actL_eq]
  refine integral_congr_ae ?_
  filter_upwards [mulTest_coeFn hξ p, mulTest_coeFn hξ q,
    mulTest_coeFn (isTestFn_mul hξ hξ) q] with x hp hq hpq
  rw [hp, hq, hpq]; ring

/-- Regrouping the cross term: moving one `ξ` off `∂ⱼ(ξ²) = 2 ξ ∂ⱼξ` onto `p`,
`⟪aᵢⱼ p, ∂ⱼ(ξ²) q⟫ = 2 ⟪aᵢⱼ (ξ p), ∂ⱼξ q⟫`. -/
private lemma actL_cross_regroup (A : EllipticCoeff d) (hξ : IsTestFn Ω ξ)
    (i j : Fin d) (p q : L2D Ω) :
    ⟪A.actL i j p, mulTestPartial (isTestFn_mul hξ hξ) j q⟫
      = 2 * ⟪A.actL i j (mulTest hξ p), mulTestPartial hξ j q⟫ := by
  rw [A.inner_actL_eq, A.inner_actL_eq, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [mulTestPartial_coeFn (isTestFn_mul hξ hξ) j q,
    mulTest_coeFn hξ p, mulTestPartial_coeFn hξ j q] with x hpart hp hq
  rw [hpart, hp, hq,
    congrFun (partialD_mul (hξ.1.differentiable (by simp))
      (hξ.1.differentiable (by simp)) j) x]
  ring

/-- Multiplying by `ξ²` is multiplying by `ξ` twice: `[ξ² · g] = [ξ · (ξ · g)]`. -/
private lemma mulTest_mul_eq (hξ : IsTestFn Ω ξ) (g : L2D Ω) :
    mulTest (isTestFn_mul hξ hξ) g = mulTest hξ (mulTest hξ g) := by
  apply Lp.ext
  filter_upwards [mulTest_coeFn (isTestFn_mul hξ hξ) g,
    mulTest_coeFn hξ (mulTest hξ g), mulTest_coeFn hξ g] with x h1 h2 h3
  rw [h1, h2, h3]; ring

/-- The `ξ²`-cutoff of a class is controlled by `‖ξ‖∞` times its `ξ`-cutoff:
`‖ξ² · g‖ ≤ ‖ξ‖∞ · ‖ξ · g‖`. -/
private lemma norm_mulTest_sq_le (hξ : IsTestFn Ω ξ) (g : L2D Ω) :
    ‖mulTest (isTestFn_mul hξ hξ) g‖ ≤ (exists_abs_bound hξ).choose * ‖mulTest hξ g‖ := by
  rw [mulTest_mul_eq hξ g]; exact norm_mulTest_le hξ _

/-- **The coefficient difference-quotient commutator, `L²(Ω)` norm bound.** The interior
difference quotient of a coefficient-multiplied field splits into the translated coefficient
acting on the field's difference quotient plus a commutator whose `L²(Ω)` norm is controlled
by the `C¹` gradient bound `A₁`: `‖Dₖʰ(aᵢⱼ g) − (τ_{h eₖ}aᵢⱼ) Dₖʰ g‖ ≤ A₁ ‖g‖`. This is the
discrete Leibniz split `coeFn_diffQuot_mul_coeff` measured at the restricted-domain level,
its commutator coefficient bounded pointwise by `IsC1Coeff.abs_diffQuot_coeff_le` (Evans,
*Partial Differential Equations* (2nd ed.), §6.3.1). -/
private lemma norm_diffQuotD_actL_sub_le {A : EllipticCoeff d} (hA : IsC1Coeff A)
    (hΩm : MeasurableSet Ω) (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) (g : L2D Ω) :
    ‖diffQuotD k h hΩm (A.actL i j g)
        - (A.translate (hshift k h)).actL i j (diffQuotD k h hΩm g)‖ ≤ hA.A1 * ‖g‖ := by
  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving (· + hshift k h) volume volume :=
    (measurePreserving_add_right volume (hshift k h)).quasiMeasurePreserving
  set cf : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun x => (A.a (x + hshift k h) i j - A.a x i j) / h with hcf
  have hmeas : Measurable cf :=
    (((A.measurable i j).comp (measurable_add_const _)).sub (A.measurable i j)).div_const h
  have hbdd : ∀ᵐ x ∂(volume.restrict Ω), |cf x| ≤ hA.A1 :=
    ae_of_all _ (fun x => hA.abs_diffQuot_coeff_le i j k hh x)
  have hkey : diffQuotD k h hΩm (A.actL i j g)
        - (A.translate (hshift k h)).actL i j (diffQuotD k h hΩm g)
      = mulCoeffL hmeas hbdd g := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (diffQuotD k h hΩm (A.actL i j g))
        ((A.translate (hshift k h)).actL i j (diffQuotD k h hΩm g)),
      coeFn_diffQuotD k h hΩm (A.actL i j g),
      (A.translate (hshift k h)).actL_coeFn i j (diffQuotD k h hΩm g),
      coeFn_diffQuotD k h hΩm g, mulCoeffL_coeFn hmeas hbdd g,
      ae_restrict_of_ae (hqmp.ae (extendL2_actL hΩm A i j g)),
      A.actL_coeFn i j g] with x hsub hdq1 hact' hdq0 hmul hsha hact0
    rw [hsub, Pi.sub_apply, hdq1, hact', EllipticCoeff.translate_a, hdq0, hmul, hact0, hsha]
    simp only [hcf]
    field_simp
    ring
  rw [hkey]; exact norm_mulCoeffL_le hmeas hbdd g

/-! ### D2: the master interior difference-quotient energy estimate -/

/-- Abstract single-term ≤ sum over `Fin d` for a nonnegative real family, isolated so its
application only beta-reduces (avoiding a `Finset.single_le_sum` isDefEq loop on `L²` norm
summands). -/
private lemma single_le_sum_fin {m : ℕ} (g : Fin m → ℝ) (hg : ∀ i, 0 ≤ g i) (k : Fin m) :
    g k ≤ ∑ i : Fin m, g i :=
  Finset.single_le_sum (f := g) (fun i _ => hg i) (Finset.mem_univ k)

/-- The squared interior difference quotient of `u₀` is bounded by the full gradient energy:
`‖Dₖ^h u₀‖² ≤ ∑ᵢ ‖u_{i+1}‖²`. Squaring `norm_diffQuotD_u0_le` (via `gcongr`) and dominating the
single `k`-th term by the sum; kept as its own declaration, proved in tactic mode with explicit
types, so the difference-quotient definition is never forced to unfold. -/
private lemma sq_norm_diffQuotD_u0_le (hΩm : MeasurableSet Ω) (k : Fin d) (h : ℝ) (u : H01 Ω) :
    ‖diffQuotD k h hΩm ((u : H1amb Ω) 0)‖ ^ 2 ≤ ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ ^ 2 := by
  have hsum : ‖(u : H1amb Ω) k.succ‖ ^ 2 ≤ ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ ^ 2 :=
    single_le_sum_fin (fun i => ‖(u : H1amb Ω) i.succ‖ ^ 2) (fun i => sq_nonneg _) k
  have key : ‖diffQuotD k h hΩm ((u : H1amb Ω) 0)‖ ≤ ‖(u : H1amb Ω) k.succ‖ :=
    norm_diffQuotD_u0_le hΩm k h u
  have key2 : ‖diffQuotD k h hΩm ((u : H1amb Ω) 0)‖ ^ 2 ≤ ‖(u : H1amb Ω) k.succ‖ ^ 2 := by
    gcongr
  exact le_trans key2 hsum


set_option maxHeartbeats 3200000 in
-- The final Young-absorption assembly chains the full D2 toolkit (bilinear identity,
-- ellipticity lower bound, four Cauchy-Schwarz/Peter-Paul term families) in one term, whose
-- elaboration exceeds the default heartbeat budget.
/-- **The master interior difference-quotient energy estimate.** For a `C¹`-coefficient
weak solution `u ∈ H₀¹(Ω)` of `L u = f` with `b = 0` and `c ≥ 0`, an inner cutoff `ξ` and an
outer cutoff `θ ≡ 1` on the shift-reachable part of `tsupport ξ²`, the cutoff-weighted energy
of the interior difference quotient of the gradient is bounded by the data, uniformly in the
step `h`: `(λ/2) ∑ᵢ ‖ξ · Dₖ^h ∂ᵢu‖² ≤ C (‖f‖² + ‖u₀‖²)`, with `C` depending only on
`λ, Λ, A₁, d, ‖ξ‖∞, ‖∂ξ‖∞` (and not on `‖∇u‖` or `h`). Testing the weak formulation with the
admissible Evans element `v_h = -Dₖ^{-h}(ξ² Dₖ^h u)`, discrete integration by parts
(`evansTest_bilin_L2D`) moves the outer difference quotient onto the coefficient action; the
discrete Leibniz split (`norm_diffQuotD_actL_sub_le`) exposes the translated-coefficient
leading term, controlled from below by ellipticity (`energy_ge` for the translate, same `λ`);
Cauchy-Schwarz and the Peter-Paul inequality absorb the commutator, cross, and right-hand
terms, the first-order energy bound `firstOrder_energy_le` supplying all gradient data
(Evans, *Partial Differential Equations* (2nd ed.), §6.3.1; Gilbarg-Trudinger, *Elliptic
PDE of Second Order*, Theorem 8.8). -/
theorem interior_diffQuot_energy_bound (Op : FullEllipticOp d) (hΩm : MeasurableSet Ω)
    (hA : IsC1Coeff Op.toEllipticCoeff)
    (hb0 : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc0 : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x)
    (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ) (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    (hsm_in : ∀ x ∈ tsupport (fun y => ξ y * ξ y), x + hshift k h ∈ Ω)
    (hsm_out : ∀ x ∈ tsupport θ, x + hshift k (-h) ∈ Ω)
    (hθ1 : ∀ x ∈ Ω,
      x ∈ tsupport (fun y => ξ y * ξ y) ∨ x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y)
        → θ x = 1)
    (hθ0 : ∀ (j : Fin d), ∀ x ∈ Ω,
      x ∈ tsupport (fun y => ξ y * ξ y) ∨ x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y)
        → partialD j θ x = 0)
    (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      Op.lam / 2 * ∑ i : Fin d,
        ‖extendL2 hΩm (mulTest hξ (diffQuotD k h hΩm ((u : H1amb Ω) i.succ)))‖ ^ 2
        ≤ C * (‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2) := by
  classical
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0; exact k.elim0
  set A := Op.toEllipticCoeff with hAdef
  set A' := A.translate (hshift k h) with hA'def
  set Dg : Fin d → L2D Ω := fun i => diffQuotD k h hΩm ((u : H1amb Ω) i.succ) with hDgdef
  set D0 : L2D Ω := diffQuotD k h hΩm ((u : H1amb Ω) 0) with hD0def
  set v : H01 Ω := evansTest hΩm hξ hθ k h hsm_in hsm_out u with hvdef
  set E : ℝ := ∑ i : Fin d, ‖mulTest hξ (Dg i)‖ ^ 2 with hEdef
  set P : ℝ := ‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2 with hPdef
  set U1 : ℝ := ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ ^ 2 with hU1def
  -- Commutator remainder classes.
  set Sr : Fin d → Fin d → L2D Ω := fun i j =>
    diffQuotD k h hΩm (A.actL i j ((u : H1amb Ω) i.succ)) - A'.actL i j (Dg i) with hSrdef
  -- The three families of the bilinear form.
  set LEAD : ℝ := ∑ i : Fin d, ∑ j : Fin d, ⟪A'.actL i j (mulTest hξ (Dg i)),
      mulTest hξ (Dg j)⟫ with hLEADdef
  set CROSS : ℝ := ∑ i : Fin d, ∑ j : Fin d,
      2 * ⟪A'.actL i j (mulTest hξ (Dg i)), mulTestPartial hξ j D0⟫ with hCROSSdef
  set REST : ℝ := ∑ i : Fin d, ∑ j : Fin d,
      ⟪mulTest (isTestFn_mul hξ hξ) (Dg j)
        + mulTestPartial (isTestFn_mul hξ hξ) j D0, Sr i j⟫ with hRESTdef
  -- Keep the enormous Evans-test term and the real aggregates opaque so downstream
  -- `isDefEq`/`linarith` stay cheap, while `Dg`/`D0`/`Sr` remain definitionally foldable.
  clear_value v E P U1 LEAD CROSS REST
  -- nonnegativity facts
  have hlam : (0 : ℝ) < A.lam := A.lam_pos
  have hEnn : (0 : ℝ) ≤ E := by rw [hEdef]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  -- LHS reduction via the extension isometry.
  have hLHS : ∑ i : Fin d,
      ‖extendL2 hΩm (mulTest hξ (diffQuotD k h hΩm ((u : H1amb Ω) i.succ)))‖ ^ 2 = E := by
    rw [hEdef]; simp only [hDgdef]; simp_rw [norm_extendL2]
  rw [hLHS]
  -- The bilinear identity, expanded into the three families.
  have hbil : A.bilin Ω u v = LEAD + CROSS + REST := by
    rw [hLEADdef, hCROSSdef, hRESTdef, hvdef,
      evansTest_bilin_L2D A hΩm hξ hθ k h hsm_in hsm_out hθ1 hθ0 u]
    simp only [hDgdef, hD0def, hSrdef]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hSreq : diffQuotD k h hΩm (A.actL i j ((u : H1amb Ω) i.succ))
        = A'.actL i j (diffQuotD k h hΩm ((u : H1amb Ω) i.succ))
          + (diffQuotD k h hΩm (A.actL i j ((u : H1amb Ω) i.succ))
              - A'.actL i j (diffQuotD k h hΩm ((u : H1amb Ω) i.succ))) := by abel
    have key_lead : ∀ p q : L2D Ω,
        ⟪mulTest (isTestFn_mul hξ hξ) q, A'.actL i j p⟫
          = ⟪A'.actL i j (mulTest hξ p), mulTest hξ q⟫ := fun p q => by
      rw [real_inner_comm, ← actL_mulTest_regroup A' hξ i j p q]
    have key_cross : ∀ p q : L2D Ω,
        ⟪mulTestPartial (isTestFn_mul hξ hξ) j q, A'.actL i j p⟫
          = 2 * ⟪A'.actL i j (mulTest hξ p), mulTestPartial hξ j q⟫ := fun p q => by
      rw [real_inner_comm, actL_cross_regroup A' hξ i j p q]
    conv_lhs =>
      rw [cutoffMul_apply_succ, diffQuotG_apply, diffQuotG_apply, hSreq, inner_add_right,
        inner_add_left, key_lead, key_cross]
  -- The weak equation kills the transport term (b = 0).
  have hbz : ∀ i : Fin d, ⟪Op.bAct i ((u : H1amb Ω) i.succ), (v : H1amb Ω) 0⟫ = 0 := by
    intro i
    rw [FullEllipticOp.bAct, inner_mulCoeffL_eq]
    have hz : (fun x => Op.b x i * ((u : H1amb Ω) i.succ x : ℝ) * ((v : H1amb Ω) 0 x : ℝ))
        =ᵐ[volume.restrict Ω] 0 := by
      filter_upwards [hb0 i] with x hx; simp [hx]
    rw [integral_congr_ae hz]; simp
  have hRHSeq : (∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) = ⟪f, (v : H1amb Ω) 0⟫ := by
    rw [L2.inner_def]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Real.inner_apply]
  have hweak : A.bilin Ω u v = ⟪f, (v : H1amb Ω) 0⟫ - ⟪Op.cAct ((u : H1amb Ω) 0),
      (v : H1amb Ω) 0⟫ := by
    have hfull := hu v
    rw [Op.fullBilin_apply, Op.lowerBilin_apply,
      Finset.sum_eq_zero (fun i _ => hbz i), zero_add, hRHSeq] at hfull
    linarith [hfull]
  -- LEAD lower bound from ellipticity of the translated coefficients.
  have hLE : A.lam * E ≤ LEAD := by
    have h := energy_ge A' (fun i => mulTest hξ (Dg i))
    rw [hLEADdef, hEdef]
    exact h
  -- first-order energy: U1 ≤ P/(2λ).
  have hU1 : A.lam * U1 ≤ ‖f‖ * ‖(u : H1amb Ω) 0‖ := by
    rw [hU1def]; exact firstOrder_energy_le Op hb0 hc0 u f hu
  have hfu2 : ‖f‖ * ‖(u : H1amb Ω) 0‖ ≤ P / 2 := by
    have hsq := sq_nonneg (‖f‖ - ‖(u : H1amb Ω) 0‖)
    rw [hPdef]; nlinarith only [hsq]
  have hU1P : A.lam * U1 ≤ P / 2 := le_trans hU1 hfu2
  have hU1nn : (0 : ℝ) ≤ U1 := by rw [hU1def]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hnD0 : ‖D0‖ ^ 2 ≤ U1 := by
    rw [hD0def, hU1def]; exact sq_norm_diffQuotD_u0_le hΩm k h u
  have hU1P2 : U1 ≤ P / (2 * A.lam) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * A.lam)]; nlinarith only [hU1P]
  have hD0P : ‖D0‖ ^ 2 ≤ P / (2 * A.lam) := le_trans hnD0 hU1P2
  have hPnn : (0 : ℝ) ≤ P := by rw [hPdef]; positivity
  -- Shared: the function value of the Evans element is a `√E`-factor plus data.
  have hmk : ‖mulTest hξ (Dg k)‖ ^ 2 ≤ E := by
    rw [hEdef]
    exact single_le_sum_fin (fun i => ‖mulTest hξ (Dg i)‖ ^ 2) (fun i => sq_nonneg _) k
  have hXinn : (0 : ℝ) ≤ (exists_abs_bound hξ).choose :=
    le_trans (abs_nonneg _) ((exists_abs_bound hξ).choose_spec 0)
  have hWknn : (0 : ℝ) ≤ (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose :=
    le_trans (abs_nonneg _)
      ((exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose_spec 0)
  have hv0 : ‖(v : H1amb Ω) 0‖
      ≤ (exists_abs_bound hξ).choose * ‖mulTest hξ (Dg k)‖
        + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose * ‖D0‖ := by
    have hz0 : (v : H1amb Ω) 0 = -diffQuotD k (-h) hΩm
        ((cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))) 0) := by
      rw [hvdef]; exact evansTest_zero_eq hΩm hξ hθ k h hsm_in hsm_out u hθ1
    have hbnd : ‖diffQuotD k (-h) hΩm
          ((cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))) 0)‖
        ≤ ‖(cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))) k.succ‖ :=
      norm_diffQuotD_u0_le hΩm k (-h)
        ⟨_, cutoffMul_diffQuotG_mem_H01 (isTestFn_mul hξ hξ) k hΩm hsm_in u.2⟩
    rw [hz0, norm_neg]
    refine le_trans hbnd ?_
    rw [cutoffMul_apply_succ, diffQuotG_apply, diffQuotG_apply]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · exact norm_mulTest_sq_le hξ (diffQuotD k h hΩm ((u : H1amb Ω) k.succ))
    · exact norm_mulTestPartial_le (isTestFn_mul hξ hξ) k (diffQuotD k h hΩm ((u : H1amb Ω) 0))
  -- The four family bounds (each `≤ (λ/8) E + Cᵢ P`).
  obtain ⟨Cf, hCfnn, hfv⟩ :
      ∃ Cf : ℝ, 0 ≤ Cf ∧ ⟪f, (v : H1amb Ω) 0⟫ ≤ A.lam / 8 * E + Cf * P := by
    have hfP : ‖f‖ ^ 2 ≤ P := by rw [hPdef]; linarith only [sq_nonneg ‖(u : H1amb Ω) 0‖]
    have hfv1 : ⟪f, (v : H1amb Ω) 0⟫
        ≤ ‖f‖ * ((exists_abs_bound hξ).choose * ‖mulTest hξ (Dg k)‖
            + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose * ‖D0‖) :=
      le_trans (real_inner_le_norm _ _) (mul_le_mul_of_nonneg_left hv0 (norm_nonneg f))
    have hb1 := young_peterPaul (lam := A.lam / 4) (B := (exists_abs_bound hξ).choose)
      (x := ‖mulTest hξ (Dg k)‖) (y := ‖f‖) (by positivity)
    have hb2 : (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose * ‖f‖ * ‖D0‖
        ≤ (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
            * (‖f‖ ^ 2 + ‖D0‖ ^ 2) := by
      nlinarith only [sq_nonneg (‖f‖ - ‖D0‖), hWknn, norm_nonneg f, norm_nonneg D0]
    have hmkE : A.lam / 8 * ‖mulTest hξ (Dg k)‖ ^ 2 ≤ A.lam / 8 * E :=
      mul_le_mul_of_nonneg_left hmk (by linarith only [hlam])
    have hK : (0 : ℝ) ≤ (exists_abs_bound hξ).choose ^ 2 / (2 * (A.lam / 4)) :=
      div_nonneg (sq_nonneg _) (by linarith only [hlam])
    have hW2 : (0 : ℝ) ≤ (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2 := by
      linarith only [hWknn]
    have hln : A.lam ≠ 0 := hlam.ne'
    refine ⟨2 * (exists_abs_bound hξ).choose ^ 2 / A.lam
        + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
        + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / (4 * A.lam),
      add_nonneg (add_nonneg (div_nonneg (by positivity) hlam.le) hW2)
        (div_nonneg hWknn (by linarith only [hlam])), ?_⟩
    calc ⟪f, (v : H1amb Ω) 0⟫
        ≤ ‖f‖ * ((exists_abs_bound hξ).choose * ‖mulTest hξ (Dg k)‖
            + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose * ‖D0‖) := hfv1
      _ = (exists_abs_bound hξ).choose * ‖mulTest hξ (Dg k)‖ * ‖f‖
            + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose * ‖f‖ * ‖D0‖ := by ring
      _ ≤ (A.lam / 4 / 2 * ‖mulTest hξ (Dg k)‖ ^ 2
              + (exists_abs_bound hξ).choose ^ 2 / (2 * (A.lam / 4)) * ‖f‖ ^ 2)
            + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
                * (‖f‖ ^ 2 + ‖D0‖ ^ 2) := by linarith only [hb1, hb2]
      _ ≤ (A.lam / 8 * E
              + (exists_abs_bound hξ).choose ^ 2 / (2 * (A.lam / 4)) * P)
            + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
                * (P + P / (2 * A.lam)) := by
          have t1 : A.lam / 4 / 2 * ‖mulTest hξ (Dg k)‖ ^ 2 ≤ A.lam / 8 * E := by
            rw [show A.lam / 4 / 2 = A.lam / 8 by ring]; exact hmkE
          have t2 := mul_le_mul_of_nonneg_left hfP hK
          have t3 := mul_le_mul_of_nonneg_left (add_le_add hfP hD0P) hW2
          linarith only [t1, t2, t3]
      _ = A.lam / 8 * E + (2 * (exists_abs_bound hξ).choose ^ 2 / A.lam
            + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
            + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / (4 * A.lam)) * P := by
          field_simp
          ring
  obtain ⟨Cc, hCcnn, hcv⟩ :
      ∃ Cc : ℝ, 0 ≤ Cc ∧
        -⟪Op.cAct ((u : H1amb Ω) 0), (v : H1amb Ω) 0⟫ ≤ A.lam / 8 * E + Cc * P := by
    have hu0P : ‖(u : H1amb Ω) 0‖ ^ 2 ≤ P := by
      rw [hPdef]; linarith only [sq_nonneg ‖f‖]
    have hcv1 : -⟪Op.cAct ((u : H1amb Ω) 0), (v : H1amb Ω) 0⟫
        ≤ Op.Csup * ‖(u : H1amb Ω) 0‖
            * ((exists_abs_bound hξ).choose * ‖mulTest hξ (Dg k)‖
              + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose * ‖D0‖) := by
      have h1 : -⟪Op.cAct ((u : H1amb Ω) 0), (v : H1amb Ω) 0⟫
          ≤ ‖Op.cAct ((u : H1amb Ω) 0)‖ * ‖(v : H1amb Ω) 0‖ :=
        le_trans (neg_le_abs _) (abs_real_inner_le_norm _ _)
      refine le_trans h1 (mul_le_mul (Op.norm_cAct_le _) hv0 (norm_nonneg _)
        (mul_nonneg Op.Csup_nonneg (norm_nonneg _)))
    have hb1 := young_peterPaul (lam := A.lam / 4)
      (B := Op.Csup * (exists_abs_bound hξ).choose)
      (x := ‖mulTest hξ (Dg k)‖) (y := ‖(u : H1amb Ω) 0‖) (by positivity)
    have hb2 : Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose
          * ‖(u : H1amb Ω) 0‖ * ‖D0‖
        ≤ Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
            * (‖(u : H1amb Ω) 0‖ ^ 2 + ‖D0‖ ^ 2) := by
      nlinarith only [sq_nonneg (‖(u : H1amb Ω) 0‖ - ‖D0‖),
        mul_nonneg Op.Csup_nonneg hWknn, norm_nonneg ((u : H1amb Ω) 0), norm_nonneg D0]
    have hmkE : A.lam / 8 * ‖mulTest hξ (Dg k)‖ ^ 2 ≤ A.lam / 8 * E :=
      mul_le_mul_of_nonneg_left hmk (by linarith only [hlam])
    have hK : (0 : ℝ) ≤ (Op.Csup * (exists_abs_bound hξ).choose) ^ 2 / (2 * (A.lam / 4)) :=
      div_nonneg (sq_nonneg _) (by linarith only [hlam])
    have hW2 : (0 : ℝ) ≤ Op.Csup
        * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2 :=
      div_nonneg (mul_nonneg Op.Csup_nonneg hWknn) (by norm_num)
    have hln : A.lam ≠ 0 := hlam.ne'
    refine ⟨2 * (Op.Csup * (exists_abs_bound hξ).choose) ^ 2 / A.lam
        + Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
        + Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / (4 * A.lam),
      add_nonneg (add_nonneg (div_nonneg (by positivity) hlam.le) hW2)
        (div_nonneg (mul_nonneg Op.Csup_nonneg hWknn) (by linarith only [hlam])), ?_⟩
    calc -⟪Op.cAct ((u : H1amb Ω) 0), (v : H1amb Ω) 0⟫
        ≤ Op.Csup * ‖(u : H1amb Ω) 0‖
            * ((exists_abs_bound hξ).choose * ‖mulTest hξ (Dg k)‖
              + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose * ‖D0‖) := hcv1
      _ = Op.Csup * (exists_abs_bound hξ).choose * ‖mulTest hξ (Dg k)‖ * ‖(u : H1amb Ω) 0‖
            + Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose
                * ‖(u : H1amb Ω) 0‖ * ‖D0‖ := by ring
      _ ≤ (A.lam / 4 / 2 * ‖mulTest hξ (Dg k)‖ ^ 2
              + (Op.Csup * (exists_abs_bound hξ).choose) ^ 2 / (2 * (A.lam / 4))
                  * ‖(u : H1amb Ω) 0‖ ^ 2)
            + Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
                * (‖(u : H1amb Ω) 0‖ ^ 2 + ‖D0‖ ^ 2) := by linarith only [hb1, hb2]
      _ ≤ (A.lam / 8 * E
              + (Op.Csup * (exists_abs_bound hξ).choose) ^ 2 / (2 * (A.lam / 4)) * P)
            + Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
                * (P + P / (2 * A.lam)) := by
          have t1 : A.lam / 4 / 2 * ‖mulTest hξ (Dg k)‖ ^ 2 ≤ A.lam / 8 * E := by
            rw [show A.lam / 4 / 2 = A.lam / 8 by ring]; exact hmkE
          have t2 := mul_le_mul_of_nonneg_left hu0P hK
          have t3 := mul_le_mul_of_nonneg_left (add_le_add hu0P hD0P) hW2
          linarith only [t1, t2, t3]
      _ = A.lam / 8 * E + (2 * (Op.Csup * (exists_abs_bound hξ).choose) ^ 2 / A.lam
            + Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
            + Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose
                / (4 * A.lam)) * P := by
          field_simp
          ring
  obtain ⟨Ccr, hCcrnn, hcr⟩ :
      ∃ Ccr : ℝ, 0 ≤ Ccr ∧ -CROSS ≤ A.lam / 8 * E + Ccr * P := by
    set SW : ℝ := ∑ j : Fin d, (exists_abs_bound_partialD hξ j).choose with hSWdef
    set C : ℝ := (2 * A.Λ * SW) ^ 2 / (2 * (A.lam / 4)) with hCdef
    have hCnn : (0 : ℝ) ≤ C := by rw [hCdef]; positivity
    -- Per-index bound (sum over `j` inside), then Young.
    have hper : ∀ i : Fin d,
        |∑ j : Fin d, 2 * ⟪A'.actL i j (mulTest hξ (Dg i)), mulTestPartial hξ j D0⟫|
          ≤ A.lam / 8 * ‖mulTest hξ (Dg i)‖ ^ 2 + C * ‖D0‖ ^ 2 := by
      intro i
      have hj : ∀ j : Fin d,
          |2 * ⟪A'.actL i j (mulTest hξ (Dg i)), mulTestPartial hξ j D0⟫|
            ≤ 2 * A.Λ * (exists_abs_bound_partialD hξ j).choose
                * ‖mulTest hξ (Dg i)‖ * ‖D0‖ := by
        intro j
        rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
        have h1 := abs_real_inner_le_norm (A'.actL i j (mulTest hξ (Dg i)))
          (mulTestPartial hξ j D0)
        have h2 : ‖A'.actL i j (mulTest hξ (Dg i))‖ ≤ A.Λ * ‖mulTest hξ (Dg i)‖ :=
          A'.norm_actL_le i j _
        have h3 : ‖mulTestPartial hξ j D0‖
            ≤ (exists_abs_bound_partialD hξ j).choose * ‖D0‖ := norm_mulTestPartial_le hξ j D0
        have h4 : |⟪A'.actL i j (mulTest hξ (Dg i)), mulTestPartial hξ j D0⟫|
            ≤ (A.Λ * ‖mulTest hξ (Dg i)‖)
                * ((exists_abs_bound_partialD hξ j).choose * ‖D0‖) :=
          le_trans h1 (mul_le_mul h2 h3 (norm_nonneg _)
            (mul_nonneg A.Λ_nonneg (norm_nonneg _)))
        nlinarith only [h4]
      have habs :
          |∑ j : Fin d, 2 * ⟪A'.actL i j (mulTest hξ (Dg i)), mulTestPartial hξ j D0⟫|
            ≤ ∑ j : Fin d, 2 * A.Λ * (exists_abs_bound_partialD hξ j).choose
                * ‖mulTest hξ (Dg i)‖ * ‖D0‖ :=
        le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun j _ => hj j))
      have hsumj : ∑ j : Fin d, 2 * A.Λ * (exists_abs_bound_partialD hξ j).choose
              * ‖mulTest hξ (Dg i)‖ * ‖D0‖
          = 2 * A.Λ * ‖mulTest hξ (Dg i)‖ * ‖D0‖ * SW := by
        rw [hSWdef, Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
      have hyoung := young_peterPaul (lam := A.lam / 4) (B := 2 * A.Λ * SW)
        (x := ‖mulTest hξ (Dg i)‖) (y := ‖D0‖) (by positivity)
      rw [hCdef]
      calc |∑ j : Fin d, 2 * ⟪A'.actL i j (mulTest hξ (Dg i)), mulTestPartial hξ j D0⟫|
          ≤ 2 * A.Λ * ‖mulTest hξ (Dg i)‖ * ‖D0‖ * SW := by rw [← hsumj]; exact habs
        _ = 2 * A.Λ * SW * ‖mulTest hξ (Dg i)‖ * ‖D0‖ := by ring
        _ ≤ A.lam / 8 * ‖mulTest hξ (Dg i)‖ ^ 2
              + (2 * A.Λ * SW) ^ 2 / (2 * (A.lam / 4)) * ‖D0‖ ^ 2 := by
            have : A.lam / 4 / 2 = A.lam / 8 := by ring
            linarith only [hyoung, this]
    -- Sum the per-index bound.
    have hCROSSabs : -CROSS ≤ A.lam / 8 * E + (d : ℝ) * (C * ‖D0‖ ^ 2) := by
      rw [hCROSSdef]
      have hle : |∑ i : Fin d, ∑ j : Fin d,
            2 * ⟪A'.actL i j (mulTest hξ (Dg i)), mulTestPartial hξ j D0⟫|
          ≤ ∑ i : Fin d, (A.lam / 8 * ‖mulTest hξ (Dg i)‖ ^ 2 + C * ‖D0‖ ^ 2) :=
        le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun i _ => hper i))
      have hsplit : ∑ i : Fin d, (A.lam / 8 * ‖mulTest hξ (Dg i)‖ ^ 2 + C * ‖D0‖ ^ 2)
          = A.lam / 8 * E + (d : ℝ) * (C * ‖D0‖ ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hEdef, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hneg : -(∑ i : Fin d, ∑ j : Fin d,
          2 * ⟪A'.actL i j (mulTest hξ (Dg i)), mulTestPartial hξ j D0⟫)
          ≤ |∑ i : Fin d, ∑ j : Fin d,
            2 * ⟪A'.actL i j (mulTest hξ (Dg i)), mulTestPartial hξ j D0⟫| := neg_le_abs _
      linarith only [hle, hsplit, hneg]
    have hd0 : (0 : ℝ) ≤ (d : ℝ) * C := mul_nonneg (by positivity) hCnn
    refine ⟨(d : ℝ) * C / (2 * A.lam), div_nonneg hd0 (by positivity), ?_⟩
    have hDC : (d : ℝ) * (C * ‖D0‖ ^ 2) ≤ (d : ℝ) * C / (2 * A.lam) * P :=
      calc (d : ℝ) * (C * ‖D0‖ ^ 2) = (d : ℝ) * C * ‖D0‖ ^ 2 := by ring
        _ ≤ (d : ℝ) * C * (P / (2 * A.lam)) := mul_le_mul_of_nonneg_left hD0P hd0
        _ = (d : ℝ) * C / (2 * A.lam) * P := by ring
    linarith only [hCROSSabs, hDC]
  obtain ⟨Cre, hCrenn, hre⟩ :
      ∃ Cre : ℝ, 0 ≤ Cre ∧ -REST ≤ A.lam / 8 * E + Cre * P := by
    have hXi : (0 : ℝ) ≤ (exists_abs_bound hξ).choose :=
      le_trans (abs_nonneg _) ((exists_abs_bound hξ).choose_spec 0)
    have hA1 : (0 : ℝ) ≤ hA.A1 := hA.A1_nonneg
    set Xi : ℝ := (exists_abs_bound hξ).choose with hXidef
    set Wq : Fin d → ℝ := fun j => (exists_abs_bound_partialD (isTestFn_mul hξ hξ) j).choose
      with hWqdef
    have hWqnn : ∀ j, (0 : ℝ) ≤ Wq j := fun j =>
      le_trans (abs_nonneg _) ((exists_abs_bound_partialD (isTestFn_mul hξ hξ) j).choose_spec 0)
    -- coefficients of the per-(i,j) upper bound
    set a : Fin d → ℝ := fun j =>
      (Xi * hA.A1) ^ 2 * (2 * (d : ℝ) / A.lam) + hA.A1 / 2 * Wq j with hadef
    set b : Fin d → ℝ := fun j => hA.A1 / 2 * Wq j with hbdef
    have hanN : ∀ j, (0 : ℝ) ≤ a j := fun j => by
      rw [hadef]; have := hWqnn j; positivity
    have hbnN : ∀ j, (0 : ℝ) ≤ b j := fun j => by rw [hbdef]; have := hWqnn j; positivity
    -- per (i,j) bound
    have hij : ∀ i j : Fin d,
        |⟪mulTest (isTestFn_mul hξ hξ) (Dg j) + mulTestPartial (isTestFn_mul hξ hξ) j D0,
            Sr i j⟫|
          ≤ A.lam / (8 * (d : ℝ)) * ‖mulTest hξ (Dg j)‖ ^ 2
            + a j * ‖(u : H1amb Ω) i.succ‖ ^ 2 + b j * ‖D0‖ ^ 2 := by
      intro i j
      have hSrn : ‖Sr i j‖ ≤ hA.A1 * ‖(u : H1amb Ω) i.succ‖ := by
        rw [hSrdef]; exact norm_diffQuotD_actL_sub_le hA hΩm i j k hh ((u : H1amb Ω) i.succ)
      have hFn : ‖mulTest (isTestFn_mul hξ hξ) (Dg j)
            + mulTestPartial (isTestFn_mul hξ hξ) j D0‖
          ≤ Xi * ‖mulTest hξ (Dg j)‖ + Wq j * ‖D0‖ := by
        refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
        · exact norm_mulTest_sq_le hξ (Dg j)
        · exact norm_mulTestPartial_le (isTestFn_mul hξ hξ) j D0
      have hCS : |⟪mulTest (isTestFn_mul hξ hξ) (Dg j)
            + mulTestPartial (isTestFn_mul hξ hξ) j D0, Sr i j⟫|
          ≤ (Xi * ‖mulTest hξ (Dg j)‖ + Wq j * ‖D0‖) * (hA.A1 * ‖(u : H1amb Ω) i.succ‖) := by
        refine le_trans (abs_real_inner_le_norm _ _) (mul_le_mul hFn hSrn (norm_nonneg _) ?_)
        exact add_nonneg (mul_nonneg hXi (norm_nonneg _)) (mul_nonneg (hWqnn j) (norm_nonneg _))
      have hyoung := young_peterPaul (lam := A.lam / (4 * (d : ℝ))) (B := Xi * hA.A1)
        (x := ‖mulTest hξ (Dg j)‖) (y := ‖(u : H1amb Ω) i.succ‖)
        (by positivity)
      have hAM : Wq j * ‖D0‖ * (hA.A1 * ‖(u : H1amb Ω) i.succ‖)
          ≤ hA.A1 / 2 * Wq j * (‖D0‖ ^ 2 + ‖(u : H1amb Ω) i.succ‖ ^ 2) := by
        nlinarith only [sq_nonneg (‖D0‖ - ‖(u : H1amb Ω) i.succ‖), mul_nonneg (hWqnn j) hA1,
          norm_nonneg D0, norm_nonneg ((u : H1amb Ω) i.succ)]
      have hlamsplit : A.lam / (4 * (d : ℝ)) / 2 = A.lam / (8 * (d : ℝ)) := by ring
      have hBsplit : (Xi * hA.A1) ^ 2 / (2 * (A.lam / (4 * (d : ℝ))))
          = (Xi * hA.A1) ^ 2 * (2 * (d : ℝ) / A.lam) := by
        rw [div_eq_iff (by positivity)]; field_simp; ring
      rw [hadef, hbdef]
      calc |⟪mulTest (isTestFn_mul hξ hξ) (Dg j)
              + mulTestPartial (isTestFn_mul hξ hξ) j D0, Sr i j⟫|
          ≤ (Xi * ‖mulTest hξ (Dg j)‖ + Wq j * ‖D0‖) * (hA.A1 * ‖(u : H1amb Ω) i.succ‖) := hCS
        _ = Xi * hA.A1 * ‖mulTest hξ (Dg j)‖ * ‖(u : H1amb Ω) i.succ‖
              + Wq j * ‖D0‖ * (hA.A1 * ‖(u : H1amb Ω) i.succ‖) := by ring
        _ ≤ A.lam / (8 * (d : ℝ)) * ‖mulTest hξ (Dg j)‖ ^ 2
              + ((Xi * hA.A1) ^ 2 * (2 * (d : ℝ) / A.lam) + hA.A1 / 2 * Wq j)
                  * ‖(u : H1amb Ω) i.succ‖ ^ 2 + hA.A1 / 2 * Wq j * ‖D0‖ ^ 2 := by
            rw [← hlamsplit, ← hBsplit]; nlinarith only [hyoung, hAM]
    -- sum the per-(i,j) bound
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    have hs1 : ∑ i : Fin d, ∑ j : Fin d,
          A.lam / (8 * (d : ℝ)) * ‖mulTest hξ (Dg j)‖ ^ 2 = A.lam / 8 * E := by
      rw [hEdef]
      simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
    have hs2 : ∑ i : Fin d, ∑ j : Fin d, a j * ‖(u : H1amb Ω) i.succ‖ ^ 2
        = (∑ j : Fin d, a j) * U1 := by
      rw [hU1def, Finset.sum_mul_sum]
      exact Finset.sum_comm
    have hs3 : ∑ i : Fin d, ∑ j : Fin d, b j * ‖D0‖ ^ 2
        = (d : ℝ) * (∑ j : Fin d, b j) * ‖D0‖ ^ 2 := by
      simp only [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    have hsum : ∑ i : Fin d, ∑ j : Fin d,
          (A.lam / (8 * (d : ℝ)) * ‖mulTest hξ (Dg j)‖ ^ 2
            + a j * ‖(u : H1amb Ω) i.succ‖ ^ 2 + b j * ‖D0‖ ^ 2)
        = A.lam / 8 * E
          + ((∑ j : Fin d, a j) * U1 + (d : ℝ) * (∑ j : Fin d, b j) * ‖D0‖ ^ 2) := by
      simp only [Finset.sum_add_distrib]
      rw [hs1, hs2, hs3]
      ring
    -- assemble
    have hREST : -REST ≤ A.lam / 8 * E
        + ((∑ j : Fin d, a j) * U1 + (d : ℝ) * (∑ j : Fin d, b j) * ‖D0‖ ^ 2) := by
      rw [hRESTdef]
      have hle : |∑ i : Fin d, ∑ j : Fin d, ⟪mulTest (isTestFn_mul hξ hξ) (Dg j)
            + mulTestPartial (isTestFn_mul hξ hξ) j D0, Sr i j⟫|
          ≤ ∑ i : Fin d, ∑ j : Fin d,
              (A.lam / (8 * (d : ℝ)) * ‖mulTest hξ (Dg j)‖ ^ 2
                + a j * ‖(u : H1amb Ω) i.succ‖ ^ 2 + b j * ‖D0‖ ^ 2) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ Finset.univ) (Finset.sum_le_sum ?_)
        intro i _
        exact le_trans (Finset.abs_sum_le_sum_abs _ Finset.univ)
          (Finset.sum_le_sum (fun j _ => hij i j))
      rw [hsum] at hle
      exact le_trans (neg_le_abs _) hle
    -- data factors are ≤ P
    have hAsumnn : (0 : ℝ) ≤ ∑ j : Fin d, a j := Finset.sum_nonneg (fun j _ => hanN j)
    have hBsumnn : (0 : ℝ) ≤ (d : ℝ) * ∑ j : Fin d, b j :=
      mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => hbnN j))
    refine ⟨((∑ j : Fin d, a j) + (d : ℝ) * ∑ j : Fin d, b j) / (2 * A.lam),
      div_nonneg (by linarith only [hAsumnn, hBsumnn]) (by positivity), ?_⟩
    have hdata : (∑ j : Fin d, a j) * U1 + (d : ℝ) * (∑ j : Fin d, b j) * ‖D0‖ ^ 2
        ≤ ((∑ j : Fin d, a j) + (d : ℝ) * ∑ j : Fin d, b j) / (2 * A.lam) * P := by
      have h1 : (∑ j : Fin d, a j) * U1 ≤ (∑ j : Fin d, a j) * (P / (2 * A.lam)) :=
        mul_le_mul_of_nonneg_left hU1P2 hAsumnn
      have h2 : (d : ℝ) * (∑ j : Fin d, b j) * ‖D0‖ ^ 2
          ≤ (d : ℝ) * (∑ j : Fin d, b j) * (P / (2 * A.lam)) :=
        mul_le_mul_of_nonneg_left hD0P hBsumnn
      calc (∑ j : Fin d, a j) * U1 + (d : ℝ) * (∑ j : Fin d, b j) * ‖D0‖ ^ 2
          ≤ (∑ j : Fin d, a j) * (P / (2 * A.lam))
              + (d : ℝ) * (∑ j : Fin d, b j) * (P / (2 * A.lam)) := add_le_add h1 h2
        _ = ((∑ j : Fin d, a j) + (d : ℝ) * ∑ j : Fin d, b j) / (2 * A.lam) * P := by ring
    linarith only [hREST, hdata]
  refine ⟨Cf + Cc + Ccr + Cre, by linarith only [hCfnn, hCcnn, hCcrnn, hCrenn], ?_⟩
  have hcomb : A.lam * E ≤ ⟪f, (v : H1amb Ω) 0⟫
      - ⟪Op.cAct ((u : H1amb Ω) 0), (v : H1amb Ω) 0⟫ - CROSS - REST := by
    rw [← hweak]; linarith only [hLE, hbil]
  change A.lam / 2 * E ≤ (Cf + Cc + Ccr + Cre) * P
  linarith only [hcomb, hfv, hcv, hcr, hre]

end EllipticDirichlet.Regularity
