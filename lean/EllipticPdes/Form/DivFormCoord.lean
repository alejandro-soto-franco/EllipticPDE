/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Form.DivFormEuclidean

/-!
# Divergence-form operators on `ℝᵈ` as coordinate operators

A `DivForm.FullEllipticOp` for Lebesgue measure on `EuclideanSpace ℝ (Fin d)` with measurable
coefficients has a matrix `aᵢⱼ x = ⟪a x eᵢ, eⱼ⟫`, a drift `bᵢ x = (b x)ᵢ` and a potential `c`.
`FullEllipticOp.toCoord` reads these as a `Sobolev.FullEllipticOp d`, and `ofCoord_toCoord_a`,
`ofCoord_toCoord_b` show that `FullEllipticOp.ofCoord` returns the same coefficients. The forms
therefore agree under `H1Graph.h01Equiv`.

## Main declarations

* `EllipticPdes.DivForm.FullEllipticOp.toCoord`: the coordinate operator.
* `EllipticPdes.DivForm.FullEllipticOp.form_congr`: the form depends on `a`, `b`, `c` only.
* `EllipticPdes.DivForm.FullEllipticOp.formOn_h01Equiv_toCoord`: the forms correspond.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.DivForm

variable {d : ℕ}

/-- The pairing of an endomorphism of `ℝᵈ` with two vectors is the sum over its matrix entries
`⟪T eᵢ, eⱼ⟫`. -/
lemma inner_apply_eq_sum (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (ξ η : EuclideanSpace ℝ (Fin d)) :
    ⟪T ξ, η⟫ = ∑ i, ∑ j, ⟪T (EuclideanSpace.single i (1 : ℝ)), EuclideanSpace.single j (1 : ℝ)⟫
      * ξ i * η j := by
  have hξ : ξ = ∑ i, ξ i • EuclideanSpace.single i (1 : ℝ) := by
    simpa using ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr ξ).symm
  have hη : η = ∑ j, η j • EuclideanSpace.single j (1 : ℝ) := by
    simpa using ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr η).symm
  conv_lhs => rw [hξ, hη]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

namespace FullEllipticOp

variable (Op : FullEllipticOp (volume : Measure (EuclideanSpace ℝ (Fin d))))

/-- **The coordinate operator of a measurable divergence-form operator on `ℝᵈ`.** Its matrix
is `aᵢⱼ x = ⟪a x eᵢ, eⱼ⟫`, its drift is the coordinate vector `b x` and its potential is `c`. -/
def toCoord (ha : Measurable Op.a) (hb : Measurable Op.b) (hc : Measurable Op.c) :
    Sobolev.FullEllipticOp d where
  a x i j := ⟪Op.a x (EuclideanSpace.single i (1 : ℝ)), EuclideanSpace.single j (1 : ℝ)⟫
  lam := Op.lam
  Λ := Op.Λ
  lam_pos := Op.lam_pos
  Λ_nonneg := Op.Λ_nonneg
  measurable i j := by fun_prop
  bdd i j := by
    filter_upwards [Op.norm_le] with x hx
    refine (abs_real_inner_le_norm _ _).trans ?_
    have h1 : ‖(EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin d))‖ = 1 := by simp
    rw [h1, mul_one]
    calc _ ≤ ‖Op.a x‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ := (Op.a x).le_opNorm _
      _ ≤ Op.Λ := by simpa using hx
  elliptic := by
    filter_upwards [Op.coercive] with x hx ξ
    have h := hx (WithLp.toLp 2 ξ)
    rwa [EuclideanSpace.real_norm_sq_eq, inner_apply_eq_sum] at h
  b x i := Op.b x i
  c := Op.c
  Bsup := Op.Bsup
  Csup := Op.Csup
  Bsup_nonneg := Op.Bsup_nonneg
  Csup_nonneg := Op.Csup_nonneg
  b_meas i := (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.comp hb
  c_meas := hc
  b_bdd i := by
    filter_upwards [Op.norm_b_le] with x hx
    exact (PiLp.norm_apply_le (Op.b x) i).trans hx
  c_bdd := Op.abs_c_le

variable (ha : Measurable Op.a) (hb : Measurable Op.b) (hc : Measurable Op.c)

/-- `ofCoord` returns the coefficient field of `toCoord`'s source. -/
lemma ofCoord_toCoord_a (x : EuclideanSpace ℝ (Fin d)) :
    (FullEllipticOp.ofCoord (Op.toCoord ha hb hc)).a x = Op.a x := by
  refine ContinuousLinearMap.ext fun ξ => ext_inner_right ℝ fun η => ?_
  change ⟪(EllipticCoeff.ofCoord (Op.toCoord ha hb hc).toEllipticCoeff).a x ξ, η⟫ = _
  rw [EllipticCoeff.inner_ofCoord_a, inner_apply_eq_sum]
  rfl

/-- `ofCoord` returns the drift of `toCoord`'s source. -/
lemma ofCoord_toCoord_b : (FullEllipticOp.ofCoord (Op.toCoord ha hb hc)).b = Op.b := rfl

/-- `ofCoord` returns the potential of `toCoord`'s source. -/
lemma ofCoord_toCoord_c : (FullEllipticOp.ofCoord (Op.toCoord ha hb hc)).c = Op.c := rfl

end FullEllipticOp

section FormCongr

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  {μ : Measure E} (Op Op' : FullEllipticOp μ) (Ω : Set E)

/-- The full form depends on the operator through `a`, `b` and `c` only. -/
lemma FullEllipticOp.form_congr (ha : Op.a = Op'.a) (hb : Op.b = Op'.b) (hc : Op.c = Op'.c)
    (U V : H1Graph μ Ω) : Op.form Ω U V = Op'.form Ω U V := by
  rw [form_apply, form_apply, EllipticCoeff.form_eq_integral, EllipticCoeff.form_eq_integral,
    lowerForm_eq_integral, lowerForm_eq_integral, ha, hb, hc]

end FormCongr

namespace FullEllipticOp

variable (Op : FullEllipticOp (volume : Measure (EuclideanSpace ℝ (Fin d))))
  (ha : Measurable Op.a) (hb : Measurable Op.b) (hc : Measurable Op.c)

/-- **The forms correspond under `h01Equiv`.** The form of `Op` on the graph space is the
coordinate form of `Op.toCoord`. -/
theorem formOn_h01Equiv_toCoord (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : Sobolev.H01 Ω) :
    Op.formOn Ω (H1Graph.H01 volume Ω) (H1Graph.h01Equiv Ω U) (H1Graph.h01Equiv Ω V) =
      (Op.toCoord ha hb hc).fullBilin Ω U V := by
  rw [← form_h01Equiv (Op.toCoord ha hb hc) Ω U V]
  exact form_congr _ _ Ω (funext fun x => (ofCoord_toCoord_a Op ha hb hc x).symm)
    (ofCoord_toCoord_b Op ha hb hc).symm (ofCoord_toCoord_c Op ha hb hc).symm _ _

end FullEllipticOp

end EllipticPdes.DivForm
