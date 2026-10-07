/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.WeakDerivChain
public import EllipticPdes.Form.DivForm
public import EllipticPdes.Poincare.GraphBounded
public import EllipticPdes.Sobolev.GraphLattice

/-!
# Weak maximum principle over a finite-dimensional inner product space

A weak subsolution of a transport-free divergence-form equation with nonnegative zeroth-order
coefficient is bounded above by its boundary values. The boundary inequality `u ≤ k on ∂Ω` for
a Sobolev class is read, following Gilbarg and Trudinger, as membership of `(u - k)⁺` in
`H₀¹(μ, Ω)`, and the conclusion is `u ≤ k` almost everywhere for every `k ≥ 0` with that
property.

The proof is the transport-free case the source singles out. Testing the subsolution inequality
against `v = (u - k)⁺`, the zeroth-order term is nonnegative because `u v ≥ 0`, so the principal
term is nonpositive. The weak gradient of `v` is the gradient of `u` where `u > k` and zero
elsewhere, so the principal term is the energy of `v` itself, which ellipticity bounds below by
the gradient norm. The gradient of `v` therefore vanishes, and the Poincaré inequality on `H₀¹`
of a bounded set makes `v` vanish.

The subsolution inequality is taken against every nonnegative element of `H₀¹(μ, Ω)`, which is
the form the source uses in the proof, having extended the inequality from `C¹` test functions by
density. Membership of `(u - k)⁺` in `H₀¹(μ, Ω)` for a subsolution of `H₀¹` is
`EllipticPdes.H1Graph.exists_mem_H01_posPart_sub_const`.

## Main declarations

* `EllipticPdes.DivForm.FullEllipticOp.weak_maximum_principle`: the weak maximum principle for a
  transport-free operator with nonnegative zeroth-order coefficient.
* `EllipticPdes.DivForm.FullEllipticOp.weak_maximum_principle_H01`: a subsolution in `H₀¹` is
  nonpositive.
* `EllipticPdes.DivForm.FullEllipticOp.eq_zero_of_weakSolution_H01`: uniqueness of the
  generalised Dirichlet problem.

## References

D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§8.1 Theorem 8.1 and Corollary 8.2 (pp. 179–180);
L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.4.1 Theorem 2 (p. 346).
-/

@[expose] public section

open MeasureTheory Set Filter TopologicalSpace
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes

set_option linter.unusedSectionVars false

/-- If `V` and `0` agree almost everywhere and `V` is the truncation `(u - k)⁺`, then `u ≤ k`
almost everywhere. -/
theorem ae_le_of_ae_eq_max_sub_of_ae_eq_zero {α : Type*} {mα : MeasurableSpace α}
    {μ : Measure α} {u V : α → ℝ} {k : ℝ} (hV : V =ᵐ[μ] fun x => max (u x - k) 0)
    (hzero : V =ᵐ[μ] 0) : ∀ᵐ x ∂μ, u x ≤ k := by
  filter_upwards [hV, hzero] with x hx hx0
  rw [hx0, Pi.zero_apply] at hx
  by_contra hlt
  rw [max_eq_left (by linarith [not_le.mp hlt])] at hx
  linarith [not_le.mp hlt]

namespace H1Graph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

/-- **The gradient of a truncation.** If the function part of `V ∈ W^{1,2}` is the truncation
`(u - k)⁺` of the function part of `U ∈ W^{1,2}`, the gradient part of `V` is that of `U` on
`{u > k}` and zero elsewhere. -/
theorem gradL_eq_ite_of_fnL_eq_max (hΩ : IsOpen Ω) {U V : H1Graph μ Ω} (hU : U ∈ W12 μ Ω)
    (hV : V ∈ W12 μ Ω) {k : ℝ} (hV0 : ⇑(fnL V) =ᵐ[μ.restrict Ω] fun x => max (fnL U x - k) 0) :
    ⇑(gradL V) =ᵐ[μ.restrict Ω] fun x => if k < fnL U x then gradL U x else 0 := by
  have hw := (((mem_W12_iff_hasWeakFDerivOn hΩ U).1 hU).sub_const k).posPart
  have hwV := ((mem_W12_iff_hasWeakFDerivOn hΩ V).1 hV).congr_ae hV0 EventuallyEq.rfl
  filter_upwards [hwV.ae_eq hw] with x hx
  refine ext_inner_right ℝ fun v => ?_
  have := congrArg (fun L : E →L[ℝ] ℝ => L v) hx
  split_ifs at this ⊢ with h1 h2 h2
  · exact this
  · exact absurd (sub_pos.2 h1) h2
  · exact absurd (sub_pos.1 h2) h1
  · simpa using this

end H1Graph

namespace DivForm

namespace FullEllipticOp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}
  (Op : FullEllipticOp μ)

open H1Graph

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The zeroth-order pairing of a subsolution with its truncation is nonnegative when `c ≥ 0`
and `k ≥ 0`. -/
theorem inner_cAct_truncation_nonneg (hc : ∀ᵐ x ∂μ, 0 ≤ Op.c x) {U V : H1Graph μ Ω} {k : ℝ}
    (hk : 0 ≤ k) (hV0 : ⇑(fnL V) =ᵐ[μ.restrict Ω] fun x => max (fnL U x - k) 0) :
    0 ≤ ⟪Op.cAct Ω (fnL U), fnL V⟫ := by
  rw [L2.inner_def]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_of_ae hc, hV0, Op.coeFn_cAct Ω (fnL U)] with x hcx hx hxc
  simp only [Pi.zero_apply, RCLike.inner_apply, conj_trivial, hxc, hx]
  by_cases hxk : k < fnL U x
  · exact mul_nonneg (le_max_right _ _) (mul_nonneg hcx (hk.trans hxk.le))
  · rw [max_eq_right (by linarith [not_lt.mp hxk]), zero_mul]

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- With no transport term the drift acts as zero. -/
theorem bAct_eq_zero (hb : ∀ x, Op.b x = 0) (g : Lp E 2 (μ.restrict Ω)) : Op.bAct Ω g = 0 := by
  refine Lp.ext ?_
  filter_upwards [Op.coeFn_bAct Ω g, Lp.coeFn_zero ℝ 2 (μ.restrict Ω)] with x hx hx0
  rw [hx, hb x, hx0]
  simp

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The zeroth-order term of a subsolution against its truncation is nonnegative when `c ≥ 0`,
`k ≥ 0` and the transport term vanishes. -/
theorem lowerForm_truncation_nonneg (hb : ∀ x, Op.b x = 0) (hc : ∀ᵐ x ∂μ, 0 ≤ Op.c x)
    {U V : H1Graph μ Ω} {k : ℝ} (hk : 0 ≤ k)
    (hV0 : ⇑(fnL V) =ᵐ[μ.restrict Ω] fun x => max (fnL U x - k) 0) :
    0 ≤ Op.lowerForm Ω U V := by
  rw [lowerForm_apply, bAct_eq_zero Op hb, inner_zero_left, zero_add]
  exact inner_cAct_truncation_nonneg Op hc hk hV0

/-- The principal form of a subsolution against its truncation is the energy of the
truncation. -/
theorem form_truncation_eq (hΩ : IsOpen Ω) {U V : H1Graph μ Ω} (hU : U ∈ W12 μ Ω)
    (hV : V ∈ W12 μ Ω) {k : ℝ}
    (hV0 : ⇑(fnL V) =ᵐ[μ.restrict Ω] fun x => max (fnL U x - k) 0) :
    Op.toEllipticCoeff.form Ω U V = Op.toEllipticCoeff.form Ω V V := by
  have hVg := gradL_eq_ite_of_fnL_eq_max hΩ hU hV hV0
  rw [EllipticCoeff.form_eq_integral, EllipticCoeff.form_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hVg] with x hx
  by_cases hxk : k < fnL U x
  · simp only [hxk, ite_true] at hx
    rw [hx]
  · simp only [hxk, ite_false] at hx
    rw [hx]
    simp

/-- **Weak maximum principle** (Gilbarg and Trudinger Theorem 8.1, in the transport-free case).
Let `Ω` be a bounded open set in a nontrivial space, `L` a divergence-form operator with no
transport term and nonnegative zeroth-order coefficient, and `U ∈ H¹(Ω)` a weak subsolution,
meaning the bilinear pairing of `U` against every nonnegative `V ∈ H₀¹(Ω)` is nonpositive. If
`k ≥ 0` and `(u - k)⁺` is the function part of some element of `H₀¹(Ω)`, then `u ≤ k` almost
everywhere on `Ω`. -/
theorem weak_maximum_principle [Nontrivial E] (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hb : ∀ x, Op.b x = 0) (hc : ∀ᵐ x ∂μ, 0 ≤ Op.c x) {U : H1Graph μ Ω}
    (hU : U ∈ W12 μ Ω)
    (hsub : ∀ V : H01 μ Ω, (∀ᵐ x ∂(μ.restrict Ω), 0 ≤ fnL (V : H1Graph μ Ω) x) →
      Op.form Ω U V ≤ 0)
    {k : ℝ} (hk : 0 ≤ k)
    (hbd : ∃ V : H01 μ Ω, ⇑(fnL (V : H1Graph μ Ω)) =ᵐ[μ.restrict Ω]
      fun x => max (fnL U x - k) 0) :
    ∀ᵐ x ∂(μ.restrict Ω), fnL U x ≤ k := by
  obtain ⟨V, hV0⟩ := hbd
  have hVW : (V : H1Graph μ Ω) ∈ W12 μ Ω := H01_le_W12 V.2
  have hVnn : ∀ᵐ x ∂(μ.restrict Ω), 0 ≤ fnL (V : H1Graph μ Ω) x := by
    filter_upwards [hV0] with x hx
    rw [hx]
    exact le_max_right _ _
  have hineq := hsub V hVnn
  rw [form_apply, form_truncation_eq Op hΩ hU hVW hV0] at hineq
  have hlow := lowerForm_truncation_nonneg Op hb hc hk hV0
  have henergy := Op.toEllipticCoeff.form_self_ge Ω (V : H1Graph μ Ω)
  have hgrad : ‖gradL (V : H1Graph μ Ω)‖ ^ 2 ≤ 0 := by
    by_contra hpos
    have := mul_pos Op.lam_pos (not_le.mp hpos)
    linarith
  obtain ⟨C, hC, hpoin⟩ := poincare_H01_of_bounded (μ := μ) hΩb
  have hV0norm : ‖fnL (V : H1Graph μ Ω)‖ ^ 2 ≤ 0 := (hpoin V V.2).trans (by nlinarith)
  have hV0zero : fnL (V : H1Graph μ Ω) = 0 :=
    norm_eq_zero.mp (by nlinarith [norm_nonneg (fnL (V : H1Graph μ Ω))])
  exact ae_le_of_ae_eq_max_sub_of_ae_eq_zero hV0 (by rw [hV0zero]; exact Lp.coeFn_zero _ _ _)

/-- **Weak maximum principle for a subsolution in `H₀¹`.** With the boundary inequality `u ≤ 0`
supplied by membership of the subsolution in `H₀¹(μ, Ω)`, a subsolution of a transport-free
operator with nonnegative zeroth-order coefficient on a bounded open set is nonpositive almost
everywhere. -/
theorem weak_maximum_principle_H01 [Nontrivial E] (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hb : ∀ x, Op.b x = 0) (hc : ∀ᵐ x ∂μ, 0 ≤ Op.c x) (U : H01 μ Ω)
    (hsub : ∀ V : H01 μ Ω, (∀ᵐ x ∂(μ.restrict Ω), 0 ≤ fnL (V : H1Graph μ Ω) x) →
      Op.form Ω U V ≤ 0) :
    ∀ᵐ x ∂(μ.restrict Ω), fnL (U : H1Graph μ Ω) x ≤ 0 := by
  obtain ⟨W, hW, hW0, -⟩ := exists_mem_H01_posPart_sub_const hΩ U.2 (le_refl (0 : ℝ))
  exact weak_maximum_principle Op hΩ hΩb hb hc (H01_le_W12 U.2) hsub (le_refl (0 : ℝ))
    ⟨⟨W, hW⟩, hW0⟩

/-- **Uniqueness of the generalised Dirichlet problem** (Gilbarg and Trudinger Corollary 8.2,
transport-free case). A weak solution in `H₀¹(μ, Ω)` of the homogeneous equation for a
transport-free operator with nonnegative zeroth-order coefficient on a bounded open set is
zero. -/
theorem eq_zero_of_weakSolution_H01 [Nontrivial E] (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hb : ∀ x, Op.b x = 0) (hc : ∀ᵐ x ∂μ, 0 ≤ Op.c x) (U : H01 μ Ω)
    (hsol : ∀ V : H01 μ Ω, Op.form Ω U V = 0) : U = 0 := by
  have hle := weak_maximum_principle_H01 Op hΩ hΩb hb hc U fun V _ => (hsol V).le
  have hge := weak_maximum_principle_H01 Op hΩ hΩb hb hc (-U) fun V _ => by
    simp [hsol V]
  have h0 : fnL (U : H1Graph μ Ω) = 0 := by
    refine Lp.ext ?_
    filter_upwards [hle, hge, Lp.coeFn_neg (fnL (U : H1Graph μ Ω)),
      Lp.coeFn_zero ℝ 2 (μ.restrict Ω)]
      with x hx1 hx2 hx3 hx4
    simp only [Submodule.coe_neg, map_neg] at hx2
    rw [hx3, Pi.neg_apply] at hx2
    rw [hx4, Pi.zero_apply]
    linarith
  have hae : ⇑(fnL (U : H1Graph μ Ω)) =ᵐ[μ.restrict Ω] (0 : E → ℝ) := by
    rw [h0]
    exact Lp.coeFn_zero ℝ 2 _
  have hw := ((mem_W12_iff_hasWeakFDerivOn hΩ _).1 (H01_le_W12 U.2)).congr_ae hae
    EventuallyEq.rfl
  have hg : gradL (U : H1Graph μ Ω) = 0 := by
    refine Lp.ext ?_
    filter_upwards [hw.ae_eq hasWeakFDerivOn_zero, Lp.coeFn_zero E 2 (μ.restrict Ω)] with x hx hx0
    rw [hx0]
    refine ext_inner_right ℝ fun v => ?_
    simpa using congrArg (fun L : E →L[ℝ] ℝ => L v) hx
  exact Subtype.ext (H1Graph.ext h0 hg)

end FullEllipticOp

end DivForm

end EllipticPdes
