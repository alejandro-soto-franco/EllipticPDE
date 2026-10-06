/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.RellichLq
public import EllipticPdes.Embedding.SobolevSharp
public import EllipticPdes.Analysis.WeakCompactness
public import EllipticPdes.Analysis.LqEulerLagrange
public import EllipticPdes.Analysis.DirectMethodForm

/-!
# Direct method under a subcritical constraint

Minimising the `H₀¹` norm over the functions of unit `L^q(Ω)` norm has a solution when
`q < 2⋆`. This is the direct method of the calculus of variations, and it is where the two
halves of the compactness chapter meet: `EllipticPdes.Analysis.exists_weakLimit` supplies a
weak limit of a minimising sequence, and
`EllipticPdes.Embedding.rellichEmbL_isCompact_of_lt` supplies the strong `L^q` convergence
that takes the constraint to that limit.

At `q = 2⋆` the second half fails, which `EllipticPdes.Embedding.not_isCompactOperator_critEmb`
records, and the minimum need not be attained. That is the exponent restriction Guo writes as
`p + 1 < 2⋆` for the semilinear problem `-Δu = u^p`, whose Euler-Lagrange equation this
minimiser solves once the constraint is differentiated.

## Main declarations

* `EllipticPdes.Embedding.exists_minimiser_of_lt`: the minimiser exists.
* `EllipticPdes.Embedding.exists_weakSolution_semilinear_of_lt`: it solves the equation.

## References

Y. Guo, *Partial Differential Equations*, Section IX.1; L. C. Evans, *Partial Differential
Equations* (2nd ed.), §8.2.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Bornology
open scoped NNReal ENNReal RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev EllipticPdes.Analysis

variable {d : ℕ} {p' q : ℝ≥0}

section

variable [Fact (1 ≤ (q : ℝ≥0∞))]

/-- The unit ball of `ℝ^d`, where the argument runs. -/
local notation "B1" => ball (0 : EuclideanSpace ℝ (Fin d)) 1

/-- The `L^q` seminorm of a graph coordinate is the seminorm of the function it represents. -/
private lemma norm_rellichEmbL_eq (hΩb : IsBounded (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
    (hd : 2 < d) (hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) (U : H01 B1) :
    ‖rellichEmbL measurableSet_ball hΩb hd hq U‖
      = (eLpNorm (((U : H1amb B1)) 0) (q : ℝ≥0∞) (volume.restrict B1)).toReal := by
  have hcoe : ⇑(rellichEmbL measurableSet_ball hΩb hd hq U)
      =ᵐ[volume.restrict B1] ⇑((U : H1amb B1) 0) := coeFn_sobolevEmbL _ U
  rw [Lp.norm_def, eLpNorm_congr_ae hcoe]

/-- **Direct method.** Below the critical exponent the `H₀¹` norm attains its minimum on the
functions of unit `L^q` norm. It is the minimisation of the inner product, a coercive symmetric
form, over `{U | ‖T U‖ = 1}` for the compact embedding `T`. -/
theorem exists_minimiser_of_lt (hΩb : IsBounded (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
    (hd : 2 < d) (hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) (hq0 : q ≠ 0)
    (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹) (hp'0 : p' ≠ 0) (hqlt : q < p')
    (_hq2 : (2 : ℝ≥0) ≤ q)
    (hne : ∃ V : H01 B1, ‖rellichEmbL measurableSet_ball hΩb hd hq V‖ = 1) :
    ∃ U : H01 B1, ‖rellichEmbL measurableSet_ball hΩb hd hq U‖ = 1 ∧
      ∀ V : H01 B1, ‖rellichEmbL measurableSet_ball hΩb hd hq V‖ = 1 → ‖U‖ ≤ ‖V‖ := by
  have hco : IsCoercive (innerSL ℝ : H01 B1 →L[ℝ] H01 B1 →L[ℝ] ℝ) :=
    ⟨1, one_pos, fun u => by
      change 1 * ‖u‖ * ‖u‖ ≤ ⟪u, u⟫
      rw [real_inner_self_eq_norm_mul_norm, one_mul]⟩
  obtain ⟨U, hU, hmin⟩ := exists_bilin_minimiser hco (fun U V => real_inner_comm V U)
    (rellichEmbL measurableSet_ball hΩb hd hq)
    (rellichEmbL_isCompact_of_lt measurableSet_ball hΩb hd hq hq0 hp' hp'0 hqlt) hne
  refine ⟨U, hU, fun V hV => ?_⟩
  have h := hmin V hV
  change ⟪U, U⟫ ≤ ⟪V, V⟫ at h
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact le_of_sq_le_sq h (norm_nonneg V)

/-- The constraint set is inhabited: a renormalised bump sits on it. -/
theorem exists_norm_rellichEmbL_eq_one
    (hΩb : IsBounded (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) (hd : 2 < d) (hq0 : q ≠ 0)
    (hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) :
    ∃ V : H01 B1, ‖rellichEmbL measurableSet_ball hΩb hd hq V‖ = 1 := by
  set V0 : H01 B1 := sharpElt d (show (0 : ℝ) < 1 / 2 by norm_num) le_rfl with hV0
  have hfin : eLpNorm (⇑(sharpBump d)) (q : ℝ≥0∞) volume ≠ ⊤ :=
    ((sharpBump d).continuous.memLp_of_hasCompactSupport
      (μ := volume) (p := (q : ℝ≥0∞)) (sharpBump d).hasCompactSupport).eLpNorm_lt_top.ne
  have hne : eLpNorm (⇑(sharpBump d)) (q : ℝ≥0∞) volume ≠ 0 :=
    eLpNorm_sharpBump_ne_zero (by simpa using hq0)
  have hnorm : ‖rellichEmbL measurableSet_ball hΩb hd hq V0‖
      = (ENNReal.ofReal ((1 / 2 : ℝ) ^ (1 - (d : ℝ) / 2 + (d : ℝ) * (1 / ((q : ℝ≥0∞)).toReal)))
          * eLpNorm (⇑(sharpBump d)) (q : ℝ≥0∞) volume).toReal := by
    rw [norm_rellichEmbL_eq, hV0, eLpNorm_sharpElt_zero,
      eLpNorm_sharpFamily (by norm_num) (by simpa using hq0) (by simp)]
  have hpos : 0 < ‖rellichEmbL measurableSet_ball hΩb hd hq V0‖ := by
    rw [hnorm, ENNReal.toReal_pos_iff]
    refine ⟨ENNReal.mul_pos ?_ hne, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.mpr hfin)⟩
    exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)).ne'
  refine ⟨(‖rellichEmbL measurableSet_ball hΩb hd hq V0‖)⁻¹ • V0, ?_⟩
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
    inv_mul_cancel₀ hpos.ne']

/-- **Minimiser as a weak solution.** Differentiating the constraint through
`EllipticPdes.Analysis.euler_lagrange_of_norm_min` turns the subcritical minimiser into a weak
solution of `-Δu + u = λ|u|^{q-2}u` on the unit ball, with `λ = ‖u‖²_{H₀¹}`: the graph inner
product `⟪U, V⟫` is `∫ uv + ∫ ∇u · ∇v`, so the identity below is the weak form of that equation.
The multiplier is the square of the minimum, so no unknown constant survives. -/
theorem exists_weakSolution_semilinear_of_lt
    (hΩb : IsBounded (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
    (hd : 2 < d) (hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) (hq0 : q ≠ 0)
    (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹) (hp'0 : p' ≠ 0) (hqlt : q < p')
    (hq2 : (2 : ℝ≥0) ≤ q) :
    ∃ U : H01 B1, ‖rellichEmbL measurableSet_ball hΩb hd hq U‖ = 1 ∧
      ∀ V : H01 B1, ⟪U, V⟫
        = ‖U‖ ^ 2 * ∫ x, |(rellichEmbL measurableSet_ball hΩb hd hq U) x| ^ ((q : ℝ) - 2)
            * (rellichEmbL measurableSet_ball hΩb hd hq U) x
            * (rellichEmbL measurableSet_ball hΩb hd hq V) x ∂(volume.restrict B1) := by
  obtain ⟨U, hU, hmin⟩ := exists_minimiser_of_lt hΩb hd hq hq0 hp' hp'0 hqlt hq2
    (exists_norm_rellichEmbL_eq_one hΩb hd hq0 hq)
  refine ⟨U, hU, fun V => ?_⟩
  have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hp1 : 1 < ((q : ℝ≥0∞)).toReal := by
    rw [ENNReal.coe_toReal]
    linarith
  have h := euler_lagrange_of_norm_min (p := (q : ℝ≥0∞))
    (by simpa using hq0) ENNReal.coe_ne_top hp1
    (rellichEmbL measurableSet_ball hΩb hd hq) hU hmin V
  simpa using h

end

end EllipticPdes.Embedding
