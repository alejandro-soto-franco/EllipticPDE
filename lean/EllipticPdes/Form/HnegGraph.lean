/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.Graph

/-!
# Characterisation of `H⁻¹(Ω)` over a general inner product space

Let `E` be a finite-dimensional real inner product space, `μ` a measure on `E` and `Ω ⊆ E`. The
dual `H⁻¹` of `H1Graph.H01 μ Ω` is represented by pairs `(f₀, F)` with `f₀ ∈ L²(Ω)` and
`F ∈ L²(Ω; E)` through

  `⟨f, v⟩ = ⟪f₀, v⟫ - ⟪F, ∇v⟫ = ∫_Ω (f₀ v - ⟪F, ∇v⟫)`,

that is `f = f₀ - div F`. The norm `‖f‖` is the least value of `‖(f₀, F)‖`, attained at the
Riesz representative.

## Main declarations

* `EllipticPdes.H1Graph.IsHnegRepr`: the pair `(f₀, F)` represents `f`.
* `EllipticPdes.H1Graph.exists_isHnegRepr_norm_eq`: a representation of norm `‖f‖` exists.
* `EllipticPdes.H1Graph.norm_le_of_isHnegRepr`: every representation has norm at least `‖f‖`.
* `EllipticPdes.H1Graph.hneg_characterization`: the characterisation theorem.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.H1Graph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  {μ : Measure E} {Ω : Set E}

/-- The gradient flip `(u, g) ↦ (u, -g)`, the sign convention of `f = f₀ - div F`. -/
def flip (U : H1Graph μ Ω) : H1Graph μ Ω := mk (fnL U) (-gradL U)

/-- The function part of the flip is unchanged. -/
@[simp] lemma fnL_flip (U : H1Graph μ Ω) : fnL (flip U) = fnL U := rfl

/-- The gradient part of the flip is negated. -/
@[simp] lemma gradL_flip (U : H1Graph μ Ω) : gradL (flip U) = -gradL U := rfl

/-- The gradient flip is an involution. -/
lemma flip_flip (U : H1Graph μ Ω) : flip (flip U) = U := by
  ext <;> simp

/-- The gradient flip preserves the norm. -/
lemma norm_flip (U : H1Graph μ Ω) : ‖flip U‖ = ‖U‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq, norm_sq_eq]
  simp

/-- The pairing with a flipped vector is the function term minus the gradient term. -/
lemma inner_flip_left (U V : H1Graph μ Ω) :
    ⟪flip U, V⟫ = ⟪fnL U, fnL V⟫ - ⟪gradL U, gradL V⟫ := by
  rw [inner_eq]
  simp [sub_eq_add_neg]

variable [FiniteDimensional ℝ E] [BorelSpace E] [IsFiniteMeasureOnCompacts μ]

variable (μ Ω) in
/-- The pair `(f₀, F)` of `L²(Ω)` and `L²(Ω; E)` represents `f ∈ H⁻¹(Ω)` when
`f v = ⟪f₀, v⟫ - ⟪F, ∇v⟫` for every `v ∈ H₀¹(Ω)`. -/
def IsHnegRepr (f₀ : Lp ℝ 2 (μ.restrict Ω)) (F : Lp E 2 (μ.restrict Ω))
    (f : H01 μ Ω →L[ℝ] ℝ) : Prop :=
  ∀ v : H01 μ Ω, f v = ⟪f₀, fnL (v : H1Graph μ Ω)⟫ - ⟪F, gradL (v : H1Graph μ Ω)⟫

/-- A pair represents `f` exactly when its gradient flip is a Riesz vector for `f` on `H₀¹`. -/
lemma isHnegRepr_iff_inner (f₀ : Lp ℝ 2 (μ.restrict Ω)) (F : Lp E 2 (μ.restrict Ω))
    (f : H01 μ Ω →L[ℝ] ℝ) :
    IsHnegRepr μ Ω f₀ F f ↔ ∀ v : H01 μ Ω, f v = ⟪flip (mk f₀ F), (v : H1Graph μ Ω)⟫ := by
  simp only [IsHnegRepr, inner_flip_left, fnL_mk, gradL_mk]

/-- The representation property in integral form: `⟨f, v⟩ = ∫_Ω (f₀ v - ⟪F, ∇v⟫)`. -/
lemma isHnegRepr_iff_integral (f₀ : Lp ℝ 2 (μ.restrict Ω)) (F : Lp E 2 (μ.restrict Ω))
    (f : H01 μ Ω →L[ℝ] ℝ) :
    IsHnegRepr μ Ω f₀ F f ↔ ∀ v : H01 μ Ω,
      f v = (∫ x in Ω, ⟪f₀ x, fnL (v : H1Graph μ Ω) x⟫ ∂μ)
        - ∫ x in Ω, ⟪F x, gradL (v : H1Graph μ Ω) x⟫ ∂μ := by
  simp only [IsHnegRepr, L2.inner_def]

/-- **Existence of a norm-attaining representation.** The flip of the Riesz representative of
`f` on `H₀¹` represents `f` with tuple norm `‖f‖`. -/
theorem exists_isHnegRepr_norm_eq (f : H01 μ Ω →L[ℝ] ℝ) :
    ∃ (f₀ : Lp ℝ 2 (μ.restrict Ω)) (F : Lp E 2 (μ.restrict Ω)),
      IsHnegRepr μ Ω f₀ F f ∧ ‖mk f₀ F‖ = ‖f‖ := by
  set w : H01 μ Ω := (InnerProductSpace.toDual ℝ (H01 μ Ω)).symm f with hw
  refine ⟨fnL (w : H1Graph μ Ω), -gradL (w : H1Graph μ Ω), ?_, ?_⟩
  · rw [isHnegRepr_iff_inner]
    intro v
    have h : flip (mk (fnL (w : H1Graph μ Ω)) (-gradL (w : H1Graph μ Ω))) = w := by
      ext <;> simp
    rw [h]
    exact (InnerProductSpace.toDual_symm_apply (x := v) (y := f)).symm
  · have h : mk (fnL (w : H1Graph μ Ω)) (-gradL (w : H1Graph μ Ω)) = flip (w : H1Graph μ Ω) :=
      rfl
    rw [h, norm_flip]
    exact (InnerProductSpace.toDual ℝ (H01 μ Ω)).symm.norm_map f

/-- **Minimality.** A representing pair has norm at least `‖f‖`, by Cauchy-Schwarz. -/
theorem norm_le_of_isHnegRepr {f₀ : Lp ℝ 2 (μ.restrict Ω)} {F : Lp E 2 (μ.restrict Ω)}
    {f : H01 μ Ω →L[ℝ] ℝ} (hF : IsHnegRepr μ Ω f₀ F f) : ‖f‖ ≤ ‖mk f₀ F‖ := by
  rw [isHnegRepr_iff_inner] at hF
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun v => ?_)
  rw [hF v]
  calc ‖⟪flip (mk f₀ F), (v : H1Graph μ Ω)⟫‖
      ≤ ‖flip (mk f₀ F)‖ * ‖(v : H1Graph μ Ω)‖ := norm_inner_le_norm _ _
    _ = ‖mk f₀ F‖ * ‖v‖ := by rw [norm_flip]; rfl

/-- The norms of the representing pairs have `‖f‖` as least element. -/
theorem hneg_norm_isLeast (f : H01 μ Ω →L[ℝ] ℝ) :
    IsLeast {r : ℝ | ∃ (f₀ : Lp ℝ 2 (μ.restrict Ω)) (F : Lp E 2 (μ.restrict Ω)),
      IsHnegRepr μ Ω f₀ F f ∧ ‖mk f₀ F‖ = r} ‖f‖ := by
  refine ⟨?_, ?_⟩
  · obtain ⟨f₀, F, hF, hn⟩ := exists_isHnegRepr_norm_eq f
    exact ⟨f₀, F, hF, hn⟩
  · rintro r ⟨f₀, F, hF, rfl⟩
    exact norm_le_of_isHnegRepr hF

/-- **Characterisation of `H⁻¹(Ω)`** over a finite-dimensional inner product space `E`. Every
`f ∈ H₀¹(Ω)'` is `f = f₀ - div F` with `f₀ ∈ L²(Ω)` and `F ∈ L²(Ω; E)`, that is
`⟨f, v⟩ = ∫_Ω (f₀ v - ⟪F, ∇v⟫)`, and the pair can be chosen with `‖(f₀, F)‖ = ‖f‖`, the least
norm among all representing pairs. -/
theorem hneg_characterization (f : H01 μ Ω →L[ℝ] ℝ) :
    ∃ (f₀ : Lp ℝ 2 (μ.restrict Ω)) (F : Lp E 2 (μ.restrict Ω)),
      (∀ v : H01 μ Ω, f v = (∫ x in Ω, ⟪f₀ x, fnL (v : H1Graph μ Ω) x⟫ ∂μ)
        - ∫ x in Ω, ⟪F x, gradL (v : H1Graph μ Ω) x⟫ ∂μ)
      ∧ ‖mk f₀ F‖ = ‖f‖
      ∧ ∀ (g₀ : Lp ℝ 2 (μ.restrict Ω)) (G : Lp E 2 (μ.restrict Ω)),
          (∀ v : H01 μ Ω, f v = (∫ x in Ω, ⟪g₀ x, fnL (v : H1Graph μ Ω) x⟫ ∂μ)
            - ∫ x in Ω, ⟪G x, gradL (v : H1Graph μ Ω) x⟫ ∂μ) →
          ‖mk f₀ F‖ ≤ ‖mk g₀ G‖ := by
  obtain ⟨f₀, F, hF, hn⟩ := exists_isHnegRepr_norm_eq f
  refine ⟨f₀, F, (isHnegRepr_iff_integral f₀ F f).mp hF, hn, fun g₀ G hG => ?_⟩
  rw [hn]
  exact norm_le_of_isHnegRepr ((isHnegRepr_iff_integral g₀ G f).mpr hG)

end EllipticPdes.H1Graph
