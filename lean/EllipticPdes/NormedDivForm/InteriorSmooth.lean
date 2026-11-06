/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.NormedDivForm.Theorems
public import EllipticPdes.Regularity.InteriorSmoothHaar

/-!
# Interior smoothness on a normed space

Infinite differentiability in the interior for a divergence-form operator on a finite-dimensional
real normed space with an additive Haar measure. The transfer along `toEuclidean` sends the
operator to `FullEllipticOp.transfer`, whose coefficients stay smooth with bounded derivatives of
every order (`Regularity.IsSmoothBdd.comp_clm`). It sends the weak solution, the datum and the
compact set to their images, and `DivForm.FullEllipticOp.interior_smooth_haar` applies on the
Euclidean image. The smooth representative comes back by composition with `toEuclidean`.

## Main declarations

* `EllipticPdes.NormedDivForm.FullEllipticOp.interior_smooth`
* `EllipticPdes.NormedDivForm.FullEllipticOp.exists_weakSolution_interior_smooth`
-/

@[expose] public section

open MeasureTheory Module
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes

namespace NormedDivForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

local notation "𝔽" => EuclideanSpace ℝ (Fin (finrank ℝ E))
local notation "𝓛" => (toEuclidean (E := E))
local notation "𝓛'" => ContinuousLinearEquiv.symm (toEuclidean (E := E))

omit [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- `transferMat` as a continuous linear map. -/
def transferMatL : (StrongDual ℝ E →L[ℝ] E) →L[ℝ] (𝔽 →L[ℝ] 𝔽) :=
  LinearMap.mkContinuous
    { toFun := transferMat
      map_add' := fun M N => by ext; simp [transferMat_apply]
      map_smul' := fun r M => by ext; simp [transferMat_apply] }
    (‖(𝓛 : E →L[ℝ] 𝔽)‖ * ‖(toEuclideanCovector : 𝔽 →L[ℝ] StrongDual ℝ E)‖) fun M =>
      ((𝓛 : E →L[ℝ] 𝔽).opNorm_comp_le _).trans (by
        rw [mul_assoc]; gcongr
        exact (M.opNorm_comp_le _).trans_eq (mul_comm _ _))

omit [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
lemma transferMatL_apply (M : StrongDual ℝ E →L[ℝ] E) : transferMatL M = transferMat M := rfl

namespace FullEllipticOp

variable (Op : FullEllipticOp μ)

omit [μ.IsAddHaarMeasure] in
lemma isSmoothBdd_transfer_a (hA : Regularity.IsSmoothBdd Op.a) :
    Regularity.IsSmoothBdd Op.transfer.a :=
  (hA.comp_clm (𝓛' : 𝔽 →L[ℝ] E)).clm_comp transferMatL

omit [μ.IsAddHaarMeasure] in
lemma isSmoothBdd_transfer_b (hB : Regularity.IsSmoothBdd Op.b) :
    Regularity.IsSmoothBdd Op.transfer.b :=
  (hB.comp_clm (𝓛' : 𝔽 →L[ℝ] E)).clm_comp (𝓛 : E →L[ℝ] 𝔽)

omit [μ.IsAddHaarMeasure] in
lemma isSmoothBdd_transfer_c (hC : Regularity.IsSmoothBdd Op.c) :
    Regularity.IsSmoothBdd Op.transfer.c :=
  hC.comp_clm (𝓛' : 𝔽 →L[ℝ] E)

end FullEllipticOp

section Data

variable {Ω : Set E}

omit [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
lemma Internal.isOpen_image (hΩo : IsOpen Ω) : IsOpen (𝓛 '' Ω) :=
  (toEuclidean (E := E)).toHomeomorph.isOpenMap _ hΩo

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
lemma Internal.finrank_euclidean {n : ℕ} (hd : finrank ℝ E = n + 1) : finrank ℝ 𝔽 = n + 1 := by
  simpa using hd

omit [μ.IsAddHaarMeasure] in
/-- The transferred datum, `f ∘ L.symm`. -/
def transferDatum (f : Lp ℝ 2 (μ.restrict Ω)) : Lp ℝ 2 ((μ.map 𝓛).restrict (𝓛 '' Ω)) :=
  Lp.compMeasurePreserving 𝓛' (measurePreserving_symm_restrict_image 𝓛 μ Ω) f

omit [μ.IsAddHaarMeasure] in
lemma Internal.transferDatum_ae_eq {f : Lp ℝ 2 (μ.restrict Ω)} {g : E → ℝ}
    (hfg : f =ᵐ[μ.restrict Ω] g) :
    ⇑(transferDatum f) =ᵐ[(μ.map 𝓛).restrict (𝓛 '' Ω)] g ∘ 𝓛' :=
  (Lp.coeFn_compMeasurePreserving _ _).trans
    ((measurePreserving_symm_restrict_image 𝓛 μ Ω).quasiMeasurePreserving.ae_eq_comp hfg)

/-- The function part of a transferred element is the transfer of its function part. -/
lemma Internal.embL2_transferEquiv (v : W1p0 2 μ Ω) :
    H1Graph.embL2 (μ.map 𝓛) (𝓛 '' Ω) (transferEquiv μ Ω v) =
      Lp.compMeasurePreserving 𝓛' (measurePreserving_symm_restrict_image 𝓛 μ Ω) (W1p0.fnL v) :=
  Lp.ext ((W1p0.fnL_mapEquiv 𝓛 v).trans (Lp.coeFn_compMeasurePreserving _ _).symm)

/-- The transfer preserves the pairing of the datum with a function part. -/
lemma Internal.inner_transferDatum (f : Lp ℝ 2 (μ.restrict Ω)) (v : W1p0 2 μ Ω) :
    ⟪transferDatum f, H1Graph.embL2 (μ.map 𝓛) (𝓛 '' Ω) (transferEquiv μ Ω v)⟫ =
      ⟪f, W1p0.fnL v⟫ := by
  rw [Internal.embL2_transferEquiv]
  exact (Lp.compMeasurePreservingₗᵢ ℝ 𝓛'
    (measurePreserving_symm_restrict_image 𝓛 μ Ω)).inner_map_map f (W1p0.fnL v)

/-- **Transfer of the weak equation.** -/
lemma Internal.weak_transfer (Op : FullEllipticOp μ) (u : W1p0 2 μ Ω) (f : Lp ℝ 2 (μ.restrict Ω))
    (hweak : ∀ v : W1p0 2 μ Ω, Op.formOn Ω u v = ⟪f, W1p0.fnL v⟫)
    (v : H1Graph.H01 (μ.map 𝓛) (𝓛 '' Ω)) :
    Op.transfer.formOn (𝓛 '' Ω) (H1Graph.H01 (μ.map 𝓛) (𝓛 '' Ω)) (transferEquiv μ Ω u) v =
      ⟪transferDatum f, H1Graph.embL2 (μ.map 𝓛) (𝓛 '' Ω) v⟫ :=
  calc Op.transfer.formOn (𝓛 '' Ω) (H1Graph.H01 (μ.map 𝓛) (𝓛 '' Ω)) (transferEquiv μ Ω u) v
      = Op.formOn Ω u ((transferEquiv μ Ω).symm v) :=
        (congrArg (Op.transfer.formOn (𝓛 '' Ω) (H1Graph.H01 (μ.map 𝓛) (𝓛 '' Ω))
          (transferEquiv μ Ω u)) ((transferEquiv μ Ω).apply_symm_apply v)).symm.trans
          (FullEllipticOp.formOn_transfer Op Ω u _).symm
    _ = ⟪f, W1p0.fnL ((transferEquiv μ Ω).symm v)⟫ := hweak _
    _ = ⟪transferDatum f, H1Graph.embL2 (μ.map 𝓛) (𝓛 '' Ω) v⟫ :=
        (Internal.inner_transferDatum f _).symm.trans (congrArg
          (fun w => ⟪transferDatum f, H1Graph.embL2 (μ.map 𝓛) (𝓛 '' Ω) w⟫)
          ((transferEquiv μ Ω).apply_symm_apply v))

omit [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
lemma Internal.image_interior (V : Set E) : 𝓛 '' interior V = interior (𝓛 '' V) :=
  (toEuclidean (E := E)).toHomeomorph.image_interior V

omit [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- A smooth function on the interior of the image pulls back to a smooth function on the interior
of `V`. -/
lemma Internal.contDiffOn_comp {V : Set E} {w : 𝔽 → ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (interior (𝓛 '' V))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (w ∘ 𝓛) (interior V) :=
  hw.comp (𝓛 : E →L[ℝ] 𝔽).contDiff.contDiffOn fun _ hx => by
    rw [← Internal.image_interior]
    exact Set.mem_image_of_mem _ hx

/-- A representative on the interior of the image pulls back to a representative on the interior
of `V`. -/
lemma Internal.ae_eq_comp {V : Set E} (hVΩ : V ⊆ Ω) (u : W1p0 2 μ Ω) {w : 𝔽 → ℝ}
    (hw : w =ᵐ[(μ.map 𝓛).restrict (interior (𝓛 '' V))]
      ⇑(H1Graph.embL2 (μ.map 𝓛) (𝓛 '' Ω) (transferEquiv μ Ω u))) :
    w ∘ 𝓛 =ᵐ[μ.restrict (interior V)] ⇑(W1p0.fnL u) := by
  rw [← Internal.image_interior] at hw
  exact ((measurePreserving_restrict_image 𝓛 μ (interior V)).quasiMeasurePreserving.ae_eq_comp
    hw).trans
    (ae_restrict_of_ae_restrict_of_subset (interior_subset.trans hVΩ) (fnL_transferEquiv_ae Ω u))

end Data

namespace FullEllipticOp

variable (Op : FullEllipticOp μ) {Ω : Set E}

/-- **Infinite differentiability in the interior (Evans, *Partial Differential Equations*
(2nd ed.), §6.3.1, Theorem 3, p. 334), over a finite-dimensional real normed space.** For an
operator whose coefficients `a`, `b`, `c` are smooth with bounded derivatives of every order, a
datum `f ∈ L²(Ω)` that is the restriction of a smooth compactly supported function `g`, and a
weak solution `u ∈ W₀^{1,2}(Ω)` of `B[u, v] = ⟪f, v⟫`, the function part of `u` has a
representative that is smooth on the interior of every compact `V ⊆ Ω`. -/
theorem interior_smooth {n : ℕ} (hd : finrank ℝ E = n + 1) (hΩm : MeasurableSet Ω)
    (hΩo : IsOpen Ω) (hA : Regularity.IsSmoothBdd Op.a) (hB : Regularity.IsSmoothBdd Op.b)
    (hC : Regularity.IsSmoothBdd Op.c) (u : W1p0 2 μ Ω) (f : Lp ℝ 2 (μ.restrict Ω)) {g : E → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (hfg : f =ᵐ[μ.restrict Ω] g)
    (hweak : ∀ v : W1p0 2 μ Ω, Op.formOn Ω u v = ⟪f, W1p0.fnL v⟫)
    {V : Set E} (hVc : IsCompact V) (hVΩ : V ⊆ Ω) :
    ∃ u' : E → ℝ, u' =ᵐ[μ.restrict (interior V)] ⇑(W1p0.fnL u) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) u' (interior V) := by
  obtain ⟨w, hae, hsm⟩ := DivForm.FullEllipticOp.interior_smooth_haar
    (Internal.finrank_euclidean hd) (μ.map 𝓛) Op.transfer (measurableSet_toEuclidean_image hΩm)
    (Internal.isOpen_image hΩo) (Op.isSmoothBdd_transfer_a hA) (Op.isSmoothBdd_transfer_b hB)
    (Op.isSmoothBdd_transfer_c hC) (transferEquiv μ Ω u) (transferDatum f)
    (hg.comp (𝓛' : 𝔽 →L[ℝ] E).contDiff) (hgc.comp_homeomorph (𝓛').toHomeomorph)
    (Internal.transferDatum_ae_eq hfg) (Internal.weak_transfer Op u f hweak)
    (hVc.image (toEuclidean (E := E)).continuous) (Set.image_mono hVΩ)
  exact ⟨w ∘ 𝓛, Internal.ae_eq_comp hVΩ u hae, Internal.contDiffOn_comp hsm⟩

/-- **Solvability with a smooth interior representative on a finite-dimensional real normed
space.** On a bounded open set, for an operator with no drift and a nonnegative zeroth-order
coefficient, whose coefficients are smooth with bounded derivatives of every order, and for a
datum that is the restriction of a smooth compactly supported function, the Dirichlet problem has
a weak solution in `W₀^{1,2}(Ω)` whose function part has a representative smooth on the interior
of every compact `V ⊆ Ω`. -/
theorem exists_weakSolution_interior_smooth {n : ℕ} (hd : finrank ℝ E = n + 1)
    (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hb : ∀ᵐ x ∂μ.restrict Ω, Op.b x = 0) (hc : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ Op.c x)
    (hA : Regularity.IsSmoothBdd Op.a) (hB : Regularity.IsSmoothBdd Op.b)
    (hC : Regularity.IsSmoothBdd Op.c) (f : Lp ℝ 2 (μ.restrict Ω)) {g : E → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (hfg : f =ᵐ[μ.restrict Ω] g)
    {V : Set E} (hVc : IsCompact V) (hVΩ : V ⊆ Ω) :
    ∃ u : W1p0 2 μ Ω, (∀ v : W1p0 2 μ Ω, Op.formOn Ω u v = ⟪f, W1p0.fnL v⟫) ∧
      ∃ u' : E → ℝ, u' =ᵐ[μ.restrict (interior V)] ⇑(W1p0.fnL u) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) u' (interior V) := by
  have : Nontrivial E := Module.finrank_pos_iff.1 (by rw [hd]; exact Nat.succ_pos n)
  obtain ⟨⟨u, hu, -⟩, -⟩ := (Op.weak_solution_of_nonneg_zeroth_of_bounded hΩb hb hc).choose_spec.2 f
  exact ⟨u, hu, Op.interior_smooth hd hΩm hΩo hA hB hC u f hg hgc hfg hu hVc hVΩ⟩

end FullEllipticOp

end NormedDivForm

end EllipticPdes
