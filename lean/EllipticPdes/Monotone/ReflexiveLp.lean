/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Analysis.LpDuality
public import EllipticPdes.Analysis.OperatorBackground
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Reflexivity of `L^p` and its subspaces

For `1 < p < ∞` and a finite measure the space `L^p` is reflexive. The proof composes the two
Riesz identifications `L^q ≅ (L^p)*` and `L^p ≅ (L^q)*` given by `lpDualMap`: a functional on
`(L^p)*` pulls back along `lpDualMap μ p q` to a functional on `L^q`, which is an element `f` of
`L^p`, and `f` evaluates every `ξ = lpDualMap μ p q g` as `∫ f g`.

A closed subspace of a reflexive space is reflexive. A functional on the dual of the subspace
pulls back along restriction to an evaluation at a point `x` of the ambient space, and the
Hahn–Banach separation theorem puts `x` in the subspace (Brezis Proposition 3.20, p. 70).
A space which is a finite sum of retracts of a reflexive space is reflexive. This gives the product
`WithLp p (X × Y)`, transport along a continuous linear equivalence, and vector-valued `L^p` over a
finite-dimensional codomain.

## Main declarations

* `EllipticPdes.Analysis.isReflexive_Lp`: `L^p` is reflexive for `1 < p < ∞` on a finite measure.
* `EllipticPdes.Analysis.IsReflexive.submodule`: a closed subspace of a reflexive space.
* `EllipticPdes.Analysis.IsReflexive.continuousLinearEquiv`: transport along `X ≃L[ℝ] Y`.
* `EllipticPdes.Analysis.IsReflexive.prod`: the product `WithLp p (X × Y)`.
* `EllipticPdes.Analysis.isReflexive_Lp_finiteDimensional`: `L^p(μ; F)` for `F` finite-dimensional.

## References

H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
Theorem 4.10 (p. 95).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace EllipticPdes.Analysis

section Retract

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Precomposition `ξ ↦ ξ ∘ T` as a map of dual spaces. -/
private def precompDual (T : X →L[ℝ] Y) : StrongDual ℝ Y →L[ℝ] StrongDual ℝ X :=
  (ContinuousLinearMap.compL ℝ X Y ℝ).flip T

private theorem precompDual_apply (T : X →L[ℝ] Y) (ξ : StrongDual ℝ Y) (x : X) :
    precompDual T ξ x = ξ (T x) := rfl

/-- **Reflexivity from a finite family of retractions.** If `z = ∑ ιᵢ (πᵢ z)` for continuous
linear maps `πᵢ : Z → X` and `ιᵢ : X → Z` and `X` is reflexive, then `Z` is reflexive. -/
theorem isReflexive_of_sum_retract {ι : Type*} [Fintype ι] (hX : IsReflexive X)
    (incl : ι → X →L[ℝ] Z) (proj : ι → Z →L[ℝ] X) (h : ∀ z, ∑ i, incl i (proj i z) = z) :
    IsReflexive Z := by
  rw [isReflexive_iff] at hX ⊢
  intro φ
  choose x hx using fun i => hX (φ.comp (precompDual (proj i)))
  refine ⟨∑ i, incl i (x i), fun ξ => ?_⟩
  have hξ : ξ = ∑ i, precompDual (proj i) (ξ.comp (incl i)) := by
    ext z
    conv_lhs => rw [← h z]
    simp [precompDual_apply]
  calc φ ξ = ∑ i, φ (precompDual (proj i) (ξ.comp (incl i))) := by
        conv_lhs => rw [hξ]
        exact map_sum φ _ _
    _ = ∑ i, ξ (incl i (x i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have := hx i (ξ.comp (incl i))
        simpa using this
    _ = ξ (∑ i, incl i (x i)) := (map_sum ξ _ _).symm

/-- **Transport of reflexivity.** A space isomorphic to a reflexive space is reflexive. -/
theorem IsReflexive.continuousLinearEquiv (hX : IsReflexive X) (e : X ≃L[ℝ] Y) :
    IsReflexive Y :=
  isReflexive_of_sum_retract (ι := Unit) hX (fun _ => (e : X →L[ℝ] Y))
    (fun _ => (e.symm : Y →L[ℝ] X)) (by simp)

/-- **Closed subspace of a reflexive space.** Brezis Proposition 3.20 (p. 70). -/
theorem IsReflexive.submodule (hX : IsReflexive X) (S : Submodule ℝ X)
    (hS : IsClosed (S : Set X)) : IsReflexive S := by
  rw [isReflexive_iff] at hX ⊢
  intro φ
  obtain ⟨x, hx⟩ := hX (φ.comp (precompDual S.subtypeL))
  have hxS : x ∈ S := by
    by_contra hnot
    obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point S.convex hS hnot
    have hu : 0 < u := by simpa using hfu 0 S.zero_mem
    have hf0 : ∀ a ∈ S, f a = 0 := by
      intro a ha
      by_contra hne
      have := hfu ((2 * u / f a) • a) (S.smul_mem _ ha)
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
      linarith
    have hzero : precompDual S.subtypeL f = 0 := by
      ext a
      exact hf0 a a.2
    have := hx f
    simp only [ContinuousLinearMap.comp_apply, hzero, map_zero] at this
    linarith [hux]
  refine ⟨⟨x, hxS⟩, fun g => ?_⟩
  obtain ⟨F, hF, -⟩ := exists_extension_norm_eq S g
  have hg : g = precompDual S.subtypeL F := by
    ext a
    exact (hF a).symm
  calc φ g = φ (precompDual S.subtypeL F) := by rw [← hg]
    _ = F x := hx F
    _ = g ⟨x, hxS⟩ := hF ⟨x, hxS⟩

/-- **Products.** If `X` and `Y` are reflexive then so is `X × Y`. -/
theorem isReflexive_prod (hX : IsReflexive X) (hY : IsReflexive Y) : IsReflexive (X × Y) := by
  rw [isReflexive_iff] at hX hY ⊢
  intro φ
  obtain ⟨x, hx⟩ := hX (φ.comp (precompDual (ContinuousLinearMap.fst ℝ X Y)))
  obtain ⟨y, hy⟩ := hY (φ.comp (precompDual (ContinuousLinearMap.snd ℝ X Y)))
  refine ⟨(x, y), fun ξ => ?_⟩
  set i₁ := ContinuousLinearMap.inl ℝ X Y
  set i₂ := ContinuousLinearMap.inr ℝ X Y
  set π₁ := ContinuousLinearMap.fst ℝ X Y
  set π₂ := ContinuousLinearMap.snd ℝ X Y
  have hξ : ξ = precompDual π₁ (ξ.comp i₁) + precompDual π₂ (ξ.comp i₂) := by
    refine ContinuousLinearMap.ext fun z => ?_
    simp only [add_apply, precompDual_apply, ContinuousLinearMap.comp_apply]
    rw [← map_add]
    simp [i₁, i₂, π₁, π₂]
  have e1 := hx (ξ.comp i₁)
  have e2 := hy (ξ.comp i₂)
  simp only [ContinuousLinearMap.comp_apply] at e1 e2
  calc φ ξ = φ (precompDual π₁ (ξ.comp i₁)) + φ (precompDual π₂ (ξ.comp i₂)) := by
        conv_lhs => rw [hξ]
        exact map_add φ _ _
    _ = ξ (x, y) := by
        rw [e1, e2, ← map_add]
        simp [i₁, i₂]

/-- **Products with an `ℓ^p` norm.** If `X` and `Y` are reflexive then so is `WithLp p (X × Y)`
for `1 ≤ p`. -/
theorem IsReflexive.prod (p : ℝ≥0∞) [Fact (1 ≤ p)] (hX : IsReflexive X) (hY : IsReflexive Y) :
    IsReflexive (WithLp p (X × Y)) :=
  (isReflexive_prod hX hY).continuousLinearEquiv (WithLp.prodContinuousLinearEquiv p ℝ X Y).symm

end Retract

section Lp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}

/-- **Reflexivity of `L^p`.** For `1 < p < ∞` and a finite measure, `L^p` is reflexive. A
functional `Φ` on the dual of `L^p` pulls back along `lpDualMap μ p q` to a functional on `L^q`,
which is `lpDualMap μ q p f` for some `f ∈ L^p`. Then `Φ ξ = ξ f` for `ξ = lpDualMap μ p q g`.
Brezis Theorem 4.10 (p. 95). -/
theorem isReflexive_Lp [Fact (1 ≤ p)] [IsFiniteMeasure μ] (hp1 : 1 < p) (hpt : p ≠ ∞) :
    IsReflexive (Lp ℝ p μ) := by
  obtain ⟨q, hpq⟩ : ∃ q, p.HolderConjugate q := ⟨_, ENNReal.HolderConjugate.inv_one_sub_inv' hp1.le⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hq : q ≠ ∞ := fun h => hp1.ne' ((ENNReal.HolderConjugate.eq_top_iff_eq_one q p).1 h)
  rw [isReflexive_iff]
  intro Φ
  obtain ⟨f, hf⟩ := lpDualMap_surjective_of_finite (μ := μ) (p := q) (q := p) hq
    (Φ.comp (lpDualMap μ p q))
  refine ⟨f, fun ξ => ?_⟩
  obtain ⟨g, rfl⟩ := lpDualMap_surjective_of_finite (μ := μ) (p := p) (q := q) hpt ξ
  have h1 : Φ (lpDualMap μ p q g) = lpDualMap μ q p f g := by rw [hf]; rfl
  rw [h1, lpDualMap_apply, lpDualMap_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

/-- **Reflexivity of vector-valued `L^p`.** For `1 < p < ∞`, a finite measure and a
finite-dimensional codomain `F`, the space `L^p(μ; F)` is reflexive. A basis of `F` writes
`L^p(μ; F)` as the sum of the retracts of `L^p(μ)` given by the coordinates. -/
theorem isReflexive_Lp_finiteDimensional [Fact (1 ≤ p)] [IsFiniteMeasure μ] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (hp1 : 1 < p) (hpt : p ≠ ∞) :
    IsReflexive (Lp F p μ) := by
  set b := Module.finBasis ℝ F
  let incl : Fin (Module.finrank ℝ F) → Lp ℝ p μ →L[ℝ] Lp F p μ := fun i =>
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (b i)).compLpL p μ
  let proj : Fin (Module.finrank ℝ F) → Lp F p μ →L[ℝ] Lp ℝ p μ := fun i =>
    (LinearMap.toContinuousLinearMap (b.coord i)).compLpL p μ
  refine isReflexive_of_sum_retract (isReflexive_Lp hp1 hpt) incl proj fun z => ?_
  have key : ∀ s : Finset (Fin (Module.finrank ℝ F)),
      (⇑(∑ i ∈ s, incl i (proj i z)) : α → F) =ᵐ[μ] fun a => ∑ i ∈ s, b.coord i (z a) • b i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      filter_upwards [Lp.coeFn_zero F p μ] with a ha
      simpa using ha
    | insert i s hi ih =>
      filter_upwards [ih, Lp.coeFn_add (incl i (proj i z)) (∑ j ∈ s, incl j (proj j z)),
        ContinuousLinearMap.coeFn_compLpL (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (b i))
          (proj i z),
        ContinuousLinearMap.coeFn_compLpL (LinearMap.toContinuousLinearMap (b.coord i)) z]
        with a h1 h2 h3 h4
      have h5 : (proj i z : α → ℝ) a = b.coord i (z a) := h4
      rw [Finset.sum_insert hi, Finset.sum_insert hi, h2, Pi.add_apply, h1, h3]
      simp [h5]
  refine Lp.ext ((key Finset.univ).trans (Filter.Eventually.of_forall fun a => ?_))
  simp

end Lp

end EllipticPdes.Analysis
