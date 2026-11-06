/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Spectrum.PoincareWirtinger
public import EllipticPdes.Spectrum.RellichW12Haar
public import EllipticPdes.Embedding.H01SobolevHaar

/-!
# Poincaré's inequality with the mean subtracted for any additive Haar measure

`Sobolev.poincare_wirtinger` bounds the `L²` distance of an element of `W^{1,2}(Ω)` from its mean
by a constant times the `L²` norm of its gradient, as a coordinate statement for the volume.
The mean depends on the measure. The transfer therefore goes through a form that does not mention
it: some class almost everywhere equal to a constant lies within `C ‖∇u‖` of `u`. Rescaling the
measure and transport along a linear equivalence send constants to constants and scale the two
sides of the inequality by the same factor or by a bounded one.

The mean comes back at the end. In `L²(ρ)` for a finite measure `ρ`, the mean of `f` times the
constant one is the orthogonal projection of `f` onto the line of constants. That projection is
the constant closest to `f`.

## Main declarations

* `EllipticPdes.norm_sub_proj_le`: projection onto a line minimises distance.
* `EllipticPdes.L2Mean.one`, `EllipticPdes.L2Mean.mean`: the constant one and the mean in
  `L²(ρ)`, with `L2Mean.mean_eq` reading the mean as an integral.
* `EllipticPdes.H1Graph.poincare_wirtinger_haar`: the inequality in the graph space for any
  additive Haar measure on `ℝᵈ`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace EllipticPdes

/-! ### Projection onto a line -/

section Projection

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The residual of the projection onto the line through `e` is orthogonal to `e`. -/
lemma Internal.inner_sub_proj_eq_zero {e : F} (he : ⟪e, e⟫ ≠ 0) (x : F) :
    ⟪e, x - (⟪e, x⟫ / ⟪e, e⟫) • e⟫ = 0 := by
  rw [inner_sub_right, real_inner_smul_right, div_mul_cancel₀ _ he, sub_self]

/-- Pythagoras for the projection onto the line through `e`. -/
lemma Internal.norm_sub_smul_sq {e : F} (he : ⟪e, e⟫ ≠ 0) (x : F) (a : ℝ) :
    ‖x - a • e‖ ^ 2 =
      ‖x - (⟪e, x⟫ / ⟪e, e⟫) • e‖ ^ 2 + ‖(⟪e, x⟫ / ⟪e, e⟫ - a) • e‖ ^ 2 := by
  rw [show x - a • e = (x - (⟪e, x⟫ / ⟪e, e⟫) • e) + (⟪e, x⟫ / ⟪e, e⟫ - a) • e by module]
  simp only [sq]
  refine norm_add_sq_eq_norm_sq_add_norm_sq_real ?_
  rw [real_inner_smul_right]
  exact mul_eq_zero_of_right _ ((real_inner_comm e _).trans (Internal.inner_sub_proj_eq_zero he x))

/-- **Projection onto a line minimises distance.** No multiple of `e` is closer to `x` than
`(⟪e, x⟫ / ⟪e, e⟫) • e`. -/
theorem norm_sub_proj_le (e x : F) (a : ℝ) :
    ‖x - (⟪e, x⟫ / ⟪e, e⟫) • e‖ ≤ ‖x - a • e‖ := by
  rcases eq_or_ne ⟪e, e⟫ 0 with he | he
  · rw [(inner_self_eq_zero (𝕜 := ℝ)).1 he, smul_zero, smul_zero]
  · exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      ((le_add_of_nonneg_right (sq_nonneg _)).trans_eq (Internal.norm_sub_smul_sq he x a).symm)

end Projection

/-! ### The mean in `L²` -/

namespace L2Mean

variable {α : Type*} [MeasurableSpace α] (ρ : Measure α) [IsFiniteMeasure ρ]

/-- The class of the constant one in `L²(ρ)`. -/
def one : Lp ℝ 2 ρ := Lp.const 2 ρ 1

/-- The mean of a class in `L²(ρ)`, the coefficient of its projection onto the constants. -/
def mean (f : Lp ℝ 2 ρ) : ℝ := ⟪one ρ, f⟫ / ⟪one ρ, one ρ⟫

/-- `one ρ` is almost everywhere the constant one. -/
lemma coeFn_one : ⇑(one ρ) =ᵐ[ρ] fun _ => (1 : ℝ) := Lp.coeFn_const 2 ρ 1

/-- The inner product with the constant one is the integral. -/
lemma inner_one_left (f : Lp ℝ 2 ρ) : ⟪one ρ, f⟫ = ∫ x, f x ∂ρ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_one ρ] with x hx
  simp [hx]

/-- The squared norm of the constant one is the total mass. -/
lemma inner_one_one : ⟪one ρ, one ρ⟫ = ρ.real univ := by
  rw [inner_one_left, integral_congr_ae (coeFn_one ρ), integral_const, smul_eq_mul, mul_one]

/-- **The mean is the integral over the total mass.** -/
theorem mean_eq (f : Lp ℝ 2 ρ) : mean ρ f = (ρ.real univ)⁻¹ * ∫ x, f x ∂ρ := by
  rw [mean, inner_one_left, inner_one_one, div_eq_inv_mul]

/-- **The mean is the closest constant.** -/
theorem norm_sub_mean_le (f : Lp ℝ 2 ρ) (a : ℝ) :
    ‖f - mean ρ f • one ρ‖ ≤ ‖f - a • one ρ‖ :=
  norm_sub_proj_le _ _ _

/-- A class almost everywhere equal to the constant `a` is `a` times the constant one. -/
lemma smul_one_eq_of_ae {g : Lp ℝ 2 ρ} {a : ℝ} (hg : ⇑g =ᵐ[ρ] fun _ => a) : a • one ρ = g :=
  Lp.ext (by
    filter_upwards [Lp.coeFn_smul a (one ρ), coeFn_one ρ, hg] with x h1 h2 h3
    rw [h1, Pi.smul_apply, h2, h3, smul_eq_mul, mul_one])

/-- The mean is at least as close as any class almost everywhere equal to a constant. -/
theorem norm_sub_mean_le_of_ae (f : Lp ℝ 2 ρ) {g : Lp ℝ 2 ρ} {a : ℝ}
    (hg : ⇑g =ᵐ[ρ] fun _ => a) : ‖f - mean ρ f • one ρ‖ ≤ ‖f - g‖ :=
  (norm_sub_mean_le ρ f a).trans_eq (by rw [smul_one_eq_of_ae ρ hg])

variable {ρ} in
/-- A bound by some constant class bounds the distance from the mean. -/
theorem norm_sub_mean_le_of_exists {f : Lp ℝ 2 ρ} {r : ℝ}
    (h : ∃ g : Lp ℝ 2 ρ, (∃ a : ℝ, ⇑g =ᵐ[ρ] fun _ => a) ∧ ‖f - g‖ ≤ r) :
    ‖f - mean ρ f • one ρ‖ ≤ r :=
  h.elim fun _ hg => hg.1.elim fun _ ha => (norm_sub_mean_le_of_ae ρ f ha).trans hg.2

end L2Mean

/-! ### The graph space -/

namespace H1Graph

section Volume

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The function part of `U` is the coordinate embedding of its preimage under `w12Equiv`. -/
lemma Internal.fnL_eq_embW12 (U : W12 volume Ω) :
    fnL (U : H1Graph volume Ω) = Sobolev.embW12 Ω ((w12Equiv Ω).symm U) :=
  congrFun (embW12G_eq_embW12 Ω) U

/-- The gradient norm of `U` is the root of the sum of the squared coordinate norms. -/
lemma Internal.norm_gradL_eq_sqrt (U : W12 volume Ω) :
    ‖gradL (U : H1Graph volume Ω)‖ =
      √(∑ k : Fin d, ‖((w12Equiv Ω).symm U : Sobolev.H1amb Ω) k.succ‖ ^ 2) := by
  rw [← norm_gradL_w12Equiv_sq, LinearIsometryEquiv.apply_symm_apply,
    Real.sqrt_sq (norm_nonneg _)]

/-- One instance of the inequality for the volume, in the form with a constant class. -/
lemma Internal.exists_const_le_volume (hΩb : Bornology.IsBounded Ω) {C : ℝ}
    (h : ∀ U : Sobolev.W12 Ω,
      ‖Sobolev.embW12 Ω U - Sobolev.constL2 hΩb (Sobolev.meanL2 hΩb (Sobolev.embW12 Ω U))‖ ≤
        C * √(∑ k : Fin d, ‖(U : Sobolev.H1amb Ω) k.succ‖ ^ 2))
    (U : W12 volume Ω) :
    ∃ g : Lp ℝ 2 (volume.restrict Ω), (∃ a : ℝ, ⇑g =ᵐ[volume.restrict Ω] fun _ => a) ∧
      ‖fnL (U : H1Graph volume Ω) - g‖ ≤ max C 0 * ‖gradL (U : H1Graph volume Ω)‖ :=
  ⟨Sobolev.constL2 hΩb (Sobolev.meanL2 hΩb (Sobolev.embW12 Ω ((w12Equiv Ω).symm U))),
    ⟨_, Sobolev.coeFn_constL2 hΩb _⟩, by
      rw [Internal.fnL_eq_embW12, Internal.norm_gradL_eq_sqrt]
      exact (h _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))⟩

/-- The inequality for the volume, in the form with a constant class. -/
theorem Internal.exists_const_le_of_volume (hd : 0 < d) (hΩopen : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hC1 : Extension.HasC1Boundary Ω) (hconn : IsPreconnected Ω)
    (hne : Ω.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U ∈ W12 volume Ω, ∃ g : Lp ℝ 2 (volume.restrict Ω),
      (∃ a : ℝ, ⇑g =ᵐ[volume.restrict Ω] fun _ => a) ∧ ‖fnL U - g‖ ≤ C * ‖gradL U‖ :=
  (Sobolev.poincare_wirtinger hd hΩopen hΩb hC1 hconn hne).elim fun C hC =>
    ⟨max C 0, le_max_right _ _, fun U hU => Internal.exists_const_le_volume hΩb hC ⟨U, hU⟩⟩

end Volume

section Smul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ν : Measure E} {Ω : Set E} {c : ℝ≥0}

/-- A bound between rescaled classes is the same bound between the classes. -/
lemma Internal.norm_le_of_lpSmulL {α : Type*} [MeasurableSpace α] {ρ ρ' : Measure α}
    {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] (hc : c ≠ 0) (h : ρ' = c • ρ) {x : Lp F 2 ρ'} {y : Lp G 2 ρ'}
    {C : ℝ} (hxy : ‖lpSmulL hc h x‖ ≤ C * ‖lpSmulL hc h y‖) : ‖x‖ ≤ C * ‖y‖ := by
  rwa [Internal.norm_lpSmulL_eq, Internal.norm_lpSmulL_eq, mul_div_assoc',
    div_le_div_iff_of_pos_right (Real.sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)))]
    at hxy

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A constant class for the rescaled image gives one for `U`. -/
lemma Internal.exists_const_le_smul_of {C : ℝ} (hc : c ≠ 0) {U : H1Graph (c • ν) Ω}
    {g : Lp ℝ 2 (ν.restrict Ω)}
    (hg : (∃ a : ℝ, ⇑g =ᵐ[ν.restrict Ω] fun _ => a) ∧
      ‖fnL (smulMeasureL ν Ω c hc U) - g‖ ≤ C * ‖gradL (smulMeasureL ν Ω c hc U)‖) :
    ∃ g' : Lp ℝ 2 ((c • ν).restrict Ω), (∃ a : ℝ, ⇑g' =ᵐ[(c • ν).restrict Ω] fun _ => a) ∧
      ‖fnL U - g'‖ ≤ C * ‖gradL U‖ :=
  ⟨lpSmulInvL (Measure.restrict_smul c ν Ω) g,
    hg.1.elim fun a ha => ⟨a, (coeFn_lpSmulInvL _ g).trans (Internal.ae_restrict_smul ha)⟩,
    Internal.norm_le_of_lpSmulL hc (Measure.restrict_smul c ν Ω) (by
      rw [map_sub, lpSmulL_lpSmulInvL, ← fnL_smulMeasureL, ← gradL_smulMeasureL]
      exact hg.2)⟩

variable [IsFiniteMeasureOnCompacts ν]

omit [FiniteDimensional ℝ E] in
/-- **The form with a constant class is invariant under rescaling the measure.** -/
lemma Internal.exists_const_le_smul (hc : c ≠ 0) {C : ℝ}
    (h : ∀ V ∈ W12 ν Ω, ∃ g : Lp ℝ 2 (ν.restrict Ω),
      (∃ a : ℝ, ⇑g =ᵐ[ν.restrict Ω] fun _ => a) ∧ ‖fnL V - g‖ ≤ C * ‖gradL V‖)
    {U : H1Graph (c • ν) Ω} (hU : U ∈ W12 (c • ν) Ω) :
    ∃ g : Lp ℝ 2 ((c • ν).restrict Ω), (∃ a : ℝ, ⇑g =ᵐ[(c • ν).restrict Ω] fun _ => a) ∧
      ‖fnL U - g‖ ≤ C * ‖gradL U‖ :=
  (h _ (smulMeasureL_mem_W12 hc hU)).elim fun _ hg => Internal.exists_const_le_smul_of hc hg

end Smul

variable {d : ℕ}

/-- The inequality for any additive Haar measure on `ℝᵈ`, in the form with a constant class. -/
theorem Internal.exists_const_le_haar (hd : 0 < d) (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [μ.IsAddHaarMeasure] {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩopen : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hC1 : Extension.HasC1Boundary Ω) (hconn : IsPreconnected Ω)
    (hne : Ω.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U ∈ W12 μ Ω, ∃ g : Lp ℝ 2 (μ.restrict Ω),
      (∃ a : ℝ, ⇑g =ᵐ[μ.restrict Ω] fun _ => a) ∧ ‖fnL U - g‖ ≤ C * ‖gradL U‖ := by
  obtain ⟨c, hc, rfl⟩ := exists_eq_smul_volume μ
  exact (Internal.exists_const_le_of_volume hd hΩopen hΩb hC1 hconn hne).elim fun C hC =>
    ⟨C, hC.1, fun _ hU => Internal.exists_const_le_smul hc hC.2 hU⟩

/-- **Poincaré's inequality with the mean subtracted for any additive Haar measure.** On a
bounded, connected, open domain with `C¹` boundary in `ℝᵈ`, `d > 0`, one constant bounds the `L²`
distance of every element of `W^{1,2}(Ω)` from its mean by the `L²` norm of its gradient. The
finiteness of `μ.restrict Ω` follows from boundedness and is taken as an instance. -/
theorem poincare_wirtinger_haar (hd : 0 < d) (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [μ.IsAddHaarMeasure] {Ω : Set (EuclideanSpace ℝ (Fin d))} [IsFiniteMeasure (μ.restrict Ω)]
    (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hC1 : Extension.HasC1Boundary Ω)
    (hconn : IsPreconnected Ω) (hne : Ω.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U ∈ W12 μ Ω,
      ‖fnL U - L2Mean.mean (μ.restrict Ω) (fnL U) • L2Mean.one (μ.restrict Ω)‖ ≤
        C * ‖gradL U‖ :=
  (Internal.exists_const_le_haar hd μ hΩopen hΩb hC1 hconn hne).elim fun C hC =>
    ⟨C, hC.1, fun U hU => L2Mean.norm_sub_mean_le_of_exists (hC.2 U hU)⟩

end H1Graph

end EllipticPdes
