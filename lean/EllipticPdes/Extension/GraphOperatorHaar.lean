/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.GraphOperator
public import EllipticPdes.Spectrum.RellichW12Haar

/-!
# Extension operator in the graph space for any additive Haar measure

`Sobolev.exists_extW12` extends `W^{1,2}(Ω)` in coordinates for a bounded open set with `C¹`
boundary. Read through `H1Graph.w12Equiv` it extends `H1Graph.W12 volume Ω`, and conjugated by the
rescaling of the measure it extends `H1Graph.W12 μ Ω` for any additive Haar measure `μ`.

## Main declarations

* `EllipticPdes.H1Graph.smulMeasureW12Equiv`: rescaling the measure as an equivalence of the
  `W^{1,2}` spaces.
* `EllipticPdes.H1Graph.exists_extW12G`: the extension operator for the volume.
* `EllipticPdes.H1Graph.exists_extW12G_haar`: the extension operator for any additive Haar
  measure.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

noncomputable section

namespace EllipticPdes.H1Graph

/-! ### Rescaling as an equivalence of `W^{1,2}` -/

section Smul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [IsFiniteMeasureOnCompacts ν] {Ω : Set E}
  {c : ℝ≥0}

omit [FiniteDimensional ℝ E] in
/-- The inverse rescaling maps `W^{1,2}(ν, Ω)` into `W^{1,2}(c • ν, Ω)`. -/
theorem smulMeasureInvL_mem_W12 (hc : c ≠ 0) {V : H1Graph ν Ω} (hV : V ∈ W12 ν Ω) :
    smulMeasureInvL ν Ω c V ∈ W12 (c • ν) Ω :=
  (smulMeasureL_mem_W12_iff hc _).1 (by rwa [smulMeasureL_smulMeasureInvL])

/-- The inverse rescaling restricted to `W^{1,2}`. -/
def smulMeasureInvW12 (hc : c ≠ 0) : W12 ν Ω →L[ℝ] W12 (c • ν) Ω :=
  ((smulMeasureInvL ν Ω c).comp (W12 ν Ω).subtypeL).codRestrict _ fun V =>
    smulMeasureInvL_mem_W12 hc V.2

/-- **Rescaling the measure as an equivalence of the `W^{1,2}` spaces.** -/
def smulMeasureW12Equiv (hc : c ≠ 0) : W12 (c • ν) Ω ≃L[ℝ] W12 ν Ω :=
  ContinuousLinearEquiv.equivOfInverse (smulMeasureW12 hc) (smulMeasureInvW12 hc)
    (fun U => Subtype.ext ((smulMeasureEquiv ν Ω c hc).symm_apply_apply (U : H1Graph (c • ν) Ω)))
    (fun V => Subtype.ext ((smulMeasureEquiv ν Ω c hc).apply_symm_apply (V : H1Graph ν Ω)))

end Smul

/-! ### The extension for the volume -/

variable {d : ℕ}

/-- The `i`-th coordinate of the gradient part of `w12Equiv W` is the coordinate `i.succ` of `W`. -/
theorem gradL_w12Equiv_coord_ae (Ω : Set (EuclideanSpace ℝ (Fin d))) (W : Sobolev.W12 Ω)
    (i : Fin d) :
    (fun x => (gradL (w12Equiv Ω W : H1Graph volume Ω) x) i) =ᵐ[volume.restrict Ω]
      ⇑((W : Sobolev.H1amb Ω) i.succ) := by
  rw [← h1Equiv_w12Equiv Ω W, h1Equiv_apply_succ]
  filter_upwards [ContinuousLinearMap.coeFn_compLp
    (EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (gradL (w12Equiv Ω W : H1Graph volume Ω))] with x hx
  exact hx.symm

/-- Two `L²` vector fields whose coordinates agree almost everywhere agree almost everywhere. -/
theorem ae_eq_of_coord_ae_eq {ρ : Measure (EuclideanSpace ℝ (Fin d))}
    {f g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (h : ∀ i : Fin d, (fun x => f x i) =ᵐ[ρ] fun x => g x i) : f =ᵐ[ρ] g := by
  filter_upwards [ae_all_iff.2 h] with x hx
  exact PiLp.ext hx

section Volume

variable {Ω : Set (EuclideanSpace ℝ (Fin d))}
  (T : Sobolev.W12 Ω →L[ℝ] Sobolev.W12 (univ : Set (EuclideanSpace ℝ (Fin d))))

/-- A coordinate extension operator read in the graph spaces. -/
def extW12GOf : W12 volume Ω →L[ℝ] W12 volume (univ : Set (EuclideanSpace ℝ (Fin d))) :=
  (w12Equiv (univ : Set (EuclideanSpace ℝ (Fin d)))).toContinuousLinearEquiv.toContinuousLinearMap
    |>.comp
    (T.comp (w12Equiv Ω).symm.toContinuousLinearEquiv.toContinuousLinearMap)

lemma extW12GOf_apply (U : W12 volume Ω) :
    extW12GOf T U = w12Equiv (univ : Set (EuclideanSpace ℝ (Fin d))) (T ((w12Equiv Ω).symm U)) :=
  rfl

/-- The function part of `extW12GOf T U` is the function coordinate of `T`. -/
lemma fnL_extW12GOf (U : W12 volume Ω) :
    fnL (extW12GOf T U : H1Graph volume univ) =
      (T ((w12Equiv Ω).symm U)).1 0 := by
  rw [extW12GOf_apply, fnL_w12Equiv]

/-- The function part of `U` is the function coordinate of `(w12Equiv Ω).symm U`. -/
lemma fnL_eq_w12Equiv_symm (U : W12 volume Ω) :
    fnL (U : H1Graph volume Ω) = ((w12Equiv Ω).symm U).1 0 := by
  rw [← fnL_w12Equiv, LinearIsometryEquiv.apply_symm_apply]

/-- The gradient coordinates of `U` are the coordinates of `(w12Equiv Ω).symm U`. -/
lemma gradL_coord_eq_w12Equiv_symm (U : W12 volume Ω) (i : Fin d) :
    (fun x => (gradL (U : H1Graph volume Ω) x) i) =ᵐ[volume.restrict Ω]
      ⇑(((w12Equiv Ω).symm U).1 i.succ) := by
  simpa using gradL_w12Equiv_coord_ae Ω ((w12Equiv Ω).symm U) i

end Volume

/-- The graph-space extension built from a coordinate extension operator and its properties. -/
theorem Internal.exists_extW12G_of {Ω O : Set (EuclideanSpace ℝ (Fin d))}
    (T : Sobolev.W12 Ω →L[ℝ] Sobolev.W12 (univ : Set (EuclideanSpace ℝ (Fin d)))) (C : ℝ)
    (hagree : ∀ U : Sobolev.W12 Ω,
      (((T U : Sobolev.W12 (univ : Set (EuclideanSpace ℝ (Fin d)))) : Sobolev.H1amb univ) 0 :
          EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] (fun x => ((U : Sobolev.H1amb Ω) 0 : Sobolev.L2D Ω) x) ∧
      ∀ k : Fin d,
        (((T U : Sobolev.W12 (univ : Set (EuclideanSpace ℝ (Fin d)))) : Sobolev.H1amb univ)
            k.succ : EuclideanSpace ℝ (Fin d) → ℝ)
          =ᵐ[volume.restrict Ω] (fun x => ((U : Sobolev.H1amb Ω) k.succ : Sobolev.L2D Ω) x))
    (hsupp : ∀ U : Sobolev.W12 Ω, ∀ᵐ y ∂volume, y ∉ O →
      (((T U : Sobolev.W12 (univ : Set (EuclideanSpace ℝ (Fin d)))) : Sobolev.H1amb univ) 0 :
        EuclideanSpace ℝ (Fin d) → ℝ) y = 0)
    (hnorm : ∀ U : Sobolev.W12 Ω, ‖T U‖ ≤ C * ‖U‖) :
    ∃ (Ext : W12 volume Ω →L[ℝ] W12 volume (univ : Set (EuclideanSpace ℝ (Fin d)))) (C : ℝ),
      (∀ U : W12 volume Ω,
        ⇑(fnL (Ext U : H1Graph volume univ)) =ᵐ[volume.restrict Ω] ⇑(fnL (U : H1Graph volume Ω)) ∧
        ⇑(gradL (Ext U : H1Graph volume univ)) =ᵐ[volume.restrict Ω]
          ⇑(gradL (U : H1Graph volume Ω))) ∧
      (∀ U : W12 volume Ω, ∀ᵐ y ∂volume, y ∉ O → fnL (Ext U : H1Graph volume univ) y = 0) ∧
      ∀ U : W12 volume Ω, ‖Ext U‖ ≤ C * ‖U‖ := by
  refine ⟨extW12GOf T, C, fun U => ⟨?_, ?_⟩, fun U => ?_, fun U => ?_⟩
  · rw [fnL_extW12GOf, fnL_eq_w12Equiv_symm]
    exact (hagree ((w12Equiv Ω).symm U)).1
  · refine ae_eq_of_coord_ae_eq fun i => ?_
    have h : (fun x => (gradL (extW12GOf T U : H1Graph volume univ) x) i) =ᵐ[volume.restrict Ω]
        ⇑((T ((w12Equiv Ω).symm U)).1 i.succ) :=
      ae_restrict_of_ae_restrict_of_subset (subset_univ Ω)
        (gradL_w12Equiv_coord_ae univ (T ((w12Equiv Ω).symm U)) i)
    exact h.trans (((hagree ((w12Equiv Ω).symm U)).2 i).trans
      (gradL_coord_eq_w12Equiv_symm U i).symm)
  · rw [fnL_extW12GOf]
    exact hsupp ((w12Equiv Ω).symm U)
  · rw [extW12GOf_apply, LinearIsometryEquiv.norm_map]
    exact (hnorm _).trans_eq (by rw [LinearIsometryEquiv.norm_map])

/-- **Extension operator in the graph space for the volume** (Evans §5.4 Theorem 1 at `p = 2`).
On a bounded open set with `C¹` boundary, and for any open set containing its closure, there is a
bounded linear map from `W^{1,2}(Ω)` to `W^{1,2}(ℝᵈ)` that agrees with each element on `Ω`, in
the function and in the gradient, and whose function part vanishes almost everywhere outside the
open set. -/
theorem exists_extW12G (hd : 0 < d) {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hC1 : Extension.HasC1Boundary Ω)
    {O : Set (EuclideanSpace ℝ (Fin d))} (hO : IsOpen O) (hsub : closure Ω ⊆ O) :
    ∃ (Ext : W12 volume Ω →L[ℝ] W12 volume (univ : Set (EuclideanSpace ℝ (Fin d)))) (C : ℝ),
      (∀ U : W12 volume Ω,
        ⇑(fnL (Ext U : H1Graph volume univ)) =ᵐ[volume.restrict Ω] ⇑(fnL (U : H1Graph volume Ω)) ∧
        ⇑(gradL (Ext U : H1Graph volume univ)) =ᵐ[volume.restrict Ω]
          ⇑(gradL (U : H1Graph volume Ω))) ∧
      (∀ U : W12 volume Ω, ∀ᵐ y ∂volume, y ∉ O → fnL (Ext U : H1Graph volume univ) y = 0) ∧
      ∀ U : W12 volume Ω, ‖Ext U‖ ≤ C * ‖U‖ :=
  (Extension.exists_extW12 hd hΩo hΩb hC1 hO hsub).elim fun T hT => hT.elim fun C hC =>
    Internal.exists_extW12G_of T C hC.1 hC.2.1 hC.2.2

/-! ### The extension for any additive Haar measure -/

section Haar

variable {Ω O : Set (EuclideanSpace ℝ (Fin d))} {c : ℝ≥0}

/-- A statement true almost everywhere on `s` for the volume is true almost everywhere on `s` for
`c • volume`. -/
theorem Internal.ae_restrict_smul_volume {p : EuclideanSpace ℝ (Fin d) → Prop}
    {s : Set (EuclideanSpace ℝ (Fin d))} (h : ∀ᵐ x ∂(volume : Measure _).restrict s, p x) :
    ∀ᵐ x ∂(c • (volume : Measure (EuclideanSpace ℝ (Fin d)))).restrict s, p x :=
  Internal.ae_restrict_smul h

/-- An equality almost everywhere on `univ` is an equality almost everywhere. -/
theorem Internal.ae_eq_of_restrict_univ {ρ : Measure (EuclideanSpace ℝ (Fin d))}
    {f g : EuclideanSpace ℝ (Fin d) → ℝ} (h : f =ᵐ[ρ.restrict univ] g) : f =ᵐ[ρ] g := by
  rwa [Measure.restrict_univ] at h

/-- The rescaled extension. -/
def extW12GSmul (hc : c ≠ 0)
    (Ext : W12 volume Ω →L[ℝ] W12 volume (univ : Set (EuclideanSpace ℝ (Fin d)))) :
    W12 (c • volume) Ω →L[ℝ] W12 (c • volume) (univ : Set (EuclideanSpace ℝ (Fin d))) :=
  (smulMeasureInvW12 hc).comp (Ext.comp (smulMeasureW12 hc))

lemma coe_extW12GSmul (hc : c ≠ 0)
    (Ext : W12 volume Ω →L[ℝ] W12 volume (univ : Set (EuclideanSpace ℝ (Fin d))))
    (U : W12 (c • volume) Ω) :
    (extW12GSmul hc Ext U : H1Graph (c • volume) univ) =
      smulMeasureInvL volume univ c (Ext (smulMeasureW12 hc U)).1 := rfl

/-- The function part of the rescaled extension agrees on `Ω` with that of the extension. -/
lemma fnL_extW12GSmul_ae (hc : c ≠ 0)
    (Ext : W12 volume Ω →L[ℝ] W12 volume (univ : Set (EuclideanSpace ℝ (Fin d))))
    (U : W12 (c • volume) Ω) :
    ⇑(fnL (extW12GSmul hc Ext U : H1Graph (c • volume) univ)) =ᵐ[(c • volume).restrict univ]
      ⇑(fnL (Ext (smulMeasureW12 hc U)).1) :=
  coeFn_lpSmulInvL (Measure.restrict_smul c volume univ) _

/-- The gradient part of the rescaled extension agrees with that of the extension. -/
lemma gradL_extW12GSmul_ae (hc : c ≠ 0)
    (Ext : W12 volume Ω →L[ℝ] W12 volume (univ : Set (EuclideanSpace ℝ (Fin d))))
    (U : W12 (c • volume) Ω) :
    ⇑(gradL (extW12GSmul hc Ext U : H1Graph (c • volume) univ)) =ᵐ[(c • volume).restrict univ]
      ⇑(gradL (Ext (smulMeasureW12 hc U)).1) :=
  coeFn_lpSmulInvL (Measure.restrict_smul c volume univ) _

/-- The rescaled extension built from an extension for the volume. -/
theorem Internal.exists_extW12G_smul (hc : c ≠ 0)
    (Ext : W12 volume Ω →L[ℝ] W12 volume (univ : Set (EuclideanSpace ℝ (Fin d)))) (C : ℝ)
    (hagree : ∀ U : W12 volume Ω,
      ⇑(fnL (Ext U : H1Graph volume univ)) =ᵐ[volume.restrict Ω] ⇑(fnL (U : H1Graph volume Ω)) ∧
      ⇑(gradL (Ext U : H1Graph volume univ)) =ᵐ[volume.restrict Ω]
        ⇑(gradL (U : H1Graph volume Ω)))
    (hsupp : ∀ U : W12 volume Ω, ∀ᵐ y ∂volume, y ∉ O → fnL (Ext U : H1Graph volume univ) y = 0)
    (hnorm : ∀ U : W12 volume Ω, ‖Ext U‖ ≤ C * ‖U‖) :
    ∃ (Ext' : W12 (c • volume) Ω →L[ℝ] W12 (c • volume) (univ : Set (EuclideanSpace ℝ (Fin d))))
      (C' : ℝ),
      (∀ U : W12 (c • volume) Ω,
        ⇑(fnL (Ext' U : H1Graph (c • volume) univ)) =ᵐ[(c • volume).restrict Ω]
          ⇑(fnL (U : H1Graph (c • volume) Ω)) ∧
        ⇑(gradL (Ext' U : H1Graph (c • volume) univ)) =ᵐ[(c • volume).restrict Ω]
          ⇑(gradL (U : H1Graph (c • volume) Ω))) ∧
      (∀ U : W12 (c • volume) Ω, ∀ᵐ y ∂(c • volume), y ∉ O →
        fnL (Ext' U : H1Graph (c • volume) univ) y = 0) ∧
      ∀ U : W12 (c • volume) Ω, ‖Ext' U‖ ≤ C' * ‖U‖ := by
  refine ⟨extW12GSmul hc Ext,
    ‖smulMeasureInvW12 (ν := (volume : Measure (EuclideanSpace ℝ (Fin d)))) (Ω := univ) hc‖ *
      max C 0 * ‖smulMeasureW12 (ν := (volume : Measure (EuclideanSpace ℝ (Fin d)))) (Ω := Ω) hc‖,
    fun U => ⟨?_, ?_⟩, fun U => ?_, fun U => ?_⟩
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset (subset_univ Ω)
        (fnL_extW12GSmul_ae hc Ext U), Internal.ae_restrict_smul_volume (hagree _).1,
      Internal.ae_restrict_smul_volume (coeFn_lpSmulL hc (Measure.restrict_smul c volume Ω)
        (fnL (U : H1Graph (c • volume) Ω)))] with x h1 h2 h3
    rw [h1, h2]
    exact h3
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset (subset_univ Ω)
        (gradL_extW12GSmul_ae hc Ext U), Internal.ae_restrict_smul_volume (hagree _).2,
      Internal.ae_restrict_smul_volume (coeFn_lpSmulL hc (Measure.restrict_smul c volume Ω)
        (gradL (U : H1Graph (c • volume) Ω)))] with x h1 h2 h3
    rw [h1, h2]
    exact h3
  · filter_upwards [Internal.ae_eq_of_restrict_univ (fnL_extW12GSmul_ae hc Ext U),
      Measure.smul_absolutelyContinuous.ae_le (hsupp (smulMeasureW12 hc U))]
      with y h1 h2 hy
    rw [h1, h2 hy]
  · calc ‖extW12GSmul hc Ext U‖
        ≤ ‖smulMeasureInvW12 (ν := (volume : Measure (EuclideanSpace ℝ (Fin d)))) (Ω := univ) hc‖ *
          ‖Ext (smulMeasureW12 hc U)‖ :=
          (smulMeasureInvW12 (ν := (volume : Measure (EuclideanSpace ℝ (Fin d)))) (Ω := univ)
            hc).le_opNorm (Ext (smulMeasureW12 hc U))
      _ ≤ ‖smulMeasureInvW12 (ν := (volume : Measure (EuclideanSpace ℝ (Fin d)))) (Ω := univ) hc‖ *
          (max C 0 * (‖smulMeasureW12 (ν := (volume : Measure (EuclideanSpace ℝ (Fin d))))
            (Ω := Ω) hc‖ * ‖U‖)) := by
          gcongr
          exact (hnorm _).trans (mul_le_mul (le_max_left _ _) (ContinuousLinearMap.le_opNorm _ _)
            (norm_nonneg _) (le_max_right _ _))
      _ = _ := by ring

end Haar

/-- **Extension operator in the graph space for any additive Haar measure** (Evans §5.4
Theorem 1 at `p = 2`). The statement of `exists_extW12G` with the volume replaced by an additive
Haar measure `μ`. The target set `T` is any set equal to `univ`, which the transfer to a normed
space supplies as an image. -/
theorem exists_extW12G_haar (hd : 0 < d) (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [μ.IsAddHaarMeasure] {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hC1 : Extension.HasC1Boundary Ω)
    {O : Set (EuclideanSpace ℝ (Fin d))} (hO : IsOpen O) (hsub : closure Ω ⊆ O)
    {T : Set (EuclideanSpace ℝ (Fin d))} (hT : T = univ) :
    ∃ (Ext : W12 μ Ω →L[ℝ] W12 μ T) (C : ℝ),
      (∀ U : W12 μ Ω,
        ⇑(fnL (Ext U : H1Graph μ T)) =ᵐ[μ.restrict Ω] ⇑(fnL (U : H1Graph μ Ω)) ∧
        ⇑(gradL (Ext U : H1Graph μ T)) =ᵐ[μ.restrict Ω] ⇑(gradL (U : H1Graph μ Ω))) ∧
      (∀ U : W12 μ Ω, ∀ᵐ y ∂μ, y ∉ O → fnL (Ext U : H1Graph μ T) y = 0) ∧
      ∀ U : W12 μ Ω, ‖Ext U‖ ≤ C * ‖U‖ := by
  subst hT
  obtain ⟨c, hc, rfl⟩ := exists_eq_smul_volume μ
  exact (exists_extW12G hd hΩo hΩb hC1 hO hsub).elim fun Ext hE => hE.elim fun C hC =>
    Internal.exists_extW12G_smul hc Ext C hC.1 hC.2.1 hC.2.2

end EllipticPdes.H1Graph
