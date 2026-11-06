/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.NormedDivForm.Theorems
public import EllipticPdes.Existence.DivFormMaximum

/-!
# Weak maximum principle on a normed space

The weak maximum principle of `DivFormMaximum.lean` for a divergence-form operator on a
finite-dimensional real normed space `E` with an additive Haar measure `μ`, proved by transfer
along `toEuclidean`. The lattice operation in the statement is the truncation `(u - k)⁺`; the
transfer commutes with it because `toEuclidean.symm` is measure-preserving, which is
`transferEquiv_posPart`.

The subsolution is taken in `W₀^{1,2}(Ω)`, the space on which `Op.formOn` is defined. The
inner-product twin takes a subsolution in `W^{1,2}(Ω)`; the normed setting has no such
submodule and no form on graph elements outside `W₀^{1,2}`.

## Main declarations

* `EllipticPdes.NormedDivForm.FullEllipticOp.transferEquiv_posPart`
* `EllipticPdes.NormedDivForm.FullEllipticOp.weak_maximum_principle`
* `EllipticPdes.NormedDivForm.FullEllipticOp.weak_maximum_principle_H01`
* `EllipticPdes.NormedDivForm.FullEllipticOp.eq_zero_of_weakSolution_H01`
-/

@[expose] public section

open MeasureTheory Module
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace EllipticPdes

namespace NormedDivForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

local notation "𝔽" => EuclideanSpace ℝ (Fin (finrank ℝ E))
local notation "𝓛" => (toEuclidean (E := E))
local notation "𝓛'" => ContinuousLinearEquiv.symm (toEuclidean (E := E))

namespace FullEllipticOp

section Lattice

variable (Ω : Set E)

/-- The function part of `transferEquiv u` is `u ∘ L.symm` almost everywhere. -/
lemma fnL_transferEquiv_symm_ae (u : W1p0 2 μ Ω) :
    ⇑(H1Graph.fnL (transferEquiv μ Ω u : H1Graph (μ.map 𝓛) (𝓛 '' Ω))) =ᵐ[
      (μ.map 𝓛).restrict (𝓛 '' Ω)] ⇑(W1p0.fnL u) ∘ 𝓛' :=
  W1p0.fnL_mapEquiv 𝓛 u

/-- A pointwise relation between the function parts of two elements is true almost everywhere on
`Ω` exactly when their transfers satisfy it almost everywhere on `L '' Ω`. -/
lemma ae_iff_transfer (u v : W1p0 2 μ Ω) (P : ℝ → ℝ → Prop) :
    (∀ᵐ x ∂μ.restrict Ω, P (W1p0.fnL u x) (W1p0.fnL v x)) ↔
      ∀ᵐ y ∂(μ.map 𝓛).restrict (𝓛 '' Ω),
        P (H1Graph.fnL (transferEquiv μ Ω u : H1Graph (μ.map 𝓛) (𝓛 '' Ω)) y)
          (H1Graph.fnL (transferEquiv μ Ω v : H1Graph (μ.map 𝓛) (𝓛 '' Ω)) y) := by
  constructor
  · intro h
    filter_upwards [fnL_transferEquiv_symm_ae Ω u, fnL_transferEquiv_symm_ae Ω v,
      (measurePreserving_symm_restrict_image 𝓛 μ Ω).quasiMeasurePreserving.ae h]
      with y h1 h2 h3
    exact Eq.mp (congrArg₂ P h1.symm h2.symm) h3
  · intro h
    filter_upwards [fnL_transferEquiv_ae Ω u, fnL_transferEquiv_ae Ω v,
      (measurePreserving_restrict_image 𝓛 μ Ω).quasiMeasurePreserving.ae h]
      with x h1 h2 h3
    have e1 : H1Graph.fnL (transferEquiv μ Ω u : H1Graph (μ.map 𝓛) (𝓛 '' Ω)) (𝓛 x) =
      W1p0.fnL u x := h1
    have e2 : H1Graph.fnL (transferEquiv μ Ω v : H1Graph (μ.map 𝓛) (𝓛 '' Ω)) (𝓛 x) =
      W1p0.fnL v x := h2
    exact Eq.mp (congrArg₂ P e1 e2) h3

/-- **Transfer commutes with the truncation.** `v = (u - k)⁺` almost everywhere on `Ω` exactly
when the transfers satisfy the same relation on `L '' Ω`. -/
theorem transferEquiv_posPart (u v : W1p0 2 μ Ω) (k : ℝ) :
    (⇑(W1p0.fnL v) =ᵐ[μ.restrict Ω] fun x => max (W1p0.fnL u x - k) 0) ↔
      ⇑(H1Graph.fnL (transferEquiv μ Ω v : H1Graph (μ.map 𝓛) (𝓛 '' Ω))) =ᵐ[(μ.map 𝓛).restrict
        (𝓛 '' Ω)] fun y => max (H1Graph.fnL
          (transferEquiv μ Ω u : H1Graph (μ.map 𝓛) (𝓛 '' Ω)) y - k) 0 :=
  ae_iff_transfer Ω u v (fun a b => b = max (a - k) 0)

/-- Nonnegativity of the function part transfers. -/
lemma ae_nonneg_iff_transfer (u : W1p0 2 μ Ω) :
    (∀ᵐ x ∂μ.restrict Ω, 0 ≤ W1p0.fnL u x) ↔
      ∀ᵐ y ∂(μ.map 𝓛).restrict (𝓛 '' Ω),
        0 ≤ H1Graph.fnL (transferEquiv μ Ω u : H1Graph (μ.map 𝓛) (𝓛 '' Ω)) y :=
  ae_iff_transfer Ω u u (fun a _ => 0 ≤ a)

end Lattice

variable (Op : FullEllipticOp μ) (Ω : Set E)

/-- The subsolution inequality transfers. -/
lemma form_nonpos_of_sub (U : W1p0 2 μ Ω)
    (hsub : ∀ V : W1p0 2 μ Ω, (∀ᵐ x ∂μ.restrict Ω, 0 ≤ W1p0.fnL V x) → Op.formOn Ω U V ≤ 0)
    (V : H1Graph.H01 (μ.map 𝓛) (𝓛 '' Ω))
    (hV : ∀ᵐ y ∂(μ.map 𝓛).restrict (𝓛 '' Ω), 0 ≤ H1Graph.fnL (V : H1Graph (μ.map 𝓛) (𝓛 '' Ω)) y) :
    Op.transfer.form (𝓛 '' Ω) (transferEquiv μ Ω U : H1Graph (μ.map 𝓛) (𝓛 '' Ω))
      (V : H1Graph (μ.map 𝓛) (𝓛 '' Ω)) ≤ 0 := by
  have hnn : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ W1p0.fnL ((transferEquiv μ Ω).symm V) x := by
    have key : ∀ (W : W1p0 2 μ Ω) (V' : H1Graph.H01 (μ.map 𝓛) (𝓛 '' Ω)),
        transferEquiv μ Ω W = V' → (∀ᵐ y ∂(μ.map 𝓛).restrict (𝓛 '' Ω),
          0 ≤ H1Graph.fnL (V' : H1Graph (μ.map 𝓛) (𝓛 '' Ω)) y) →
        ∀ᵐ x ∂μ.restrict Ω, 0 ≤ W1p0.fnL W x := by
      intro W V' hW hV'
      subst hW
      exact (ae_nonneg_iff_transfer Ω W).2 hV'
    exact key _ V (ContinuousLinearEquiv.apply_symm_apply _ _) hV
  have h1 := hsub _ hnn
  have h : transferEquiv μ Ω ((transferEquiv μ Ω).symm V) = V :=
    ContinuousLinearEquiv.apply_symm_apply _ _
  have e : Op.formOn Ω U ((transferEquiv μ Ω).symm V) =
      Op.transfer.formOn (𝓛 '' Ω) (H1Graph.H01 (μ.map 𝓛) (𝓛 '' Ω)) (transferEquiv μ Ω U) V :=
    (formOn_transfer Op Ω U _).trans
      (congrArg (Op.transfer.formOn (𝓛 '' Ω) (H1Graph.H01 (μ.map 𝓛) (𝓛 '' Ω))
        (transferEquiv μ Ω U)) h)
  have e2 : Op.transfer.formOn (𝓛 '' Ω) (H1Graph.H01 (μ.map 𝓛) (𝓛 '' Ω)) (transferEquiv μ Ω U) V =
      Op.transfer.form (𝓛 '' Ω) (transferEquiv μ Ω U : H1Graph (μ.map 𝓛) (𝓛 '' Ω))
        (V : H1Graph (μ.map 𝓛) (𝓛 '' Ω)) := rfl
  exact (e2.symm.trans e.symm).trans_le h1

variable {Ω}

/-- **Weak maximum principle** (Gilbarg and Trudinger Theorem 8.1, in the transport-free case).
Let `Ω` be a bounded open set in a nontrivial normed space, `L` a divergence-form operator with
no transport term and nonnegative zeroth-order coefficient, and `U ∈ W₀^{1,2}(Ω)` a weak
subsolution, meaning the form of `U` against every nonnegative `V ∈ W₀^{1,2}(Ω)` is nonpositive.
If `k ≥ 0` and `(u - k)⁺` is the function part of some element of `W₀^{1,2}(Ω)`, then `u ≤ k`
almost everywhere on `Ω`. The subsolution lies in `W₀^{1,2}(Ω)`, where the inner-product twin
takes `W^{1,2}(Ω)`. -/
theorem weak_maximum_principle [Nontrivial E] (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hb : ∀ x, Op.b x = 0) (hc : ∀ᵐ x ∂μ, 0 ≤ Op.c x) {U : W1p0 2 μ Ω}
    (hsub : ∀ V : W1p0 2 μ Ω, (∀ᵐ x ∂μ.restrict Ω, 0 ≤ W1p0.fnL V x) →
      Op.formOn Ω U V ≤ 0)
    {k : ℝ} (hk : 0 ≤ k)
    (hbd : ∃ V : W1p0 2 μ Ω, ⇑(W1p0.fnL V) =ᵐ[μ.restrict Ω]
      fun x => max (W1p0.fnL U x - k) 0) :
    ∀ᵐ x ∂μ.restrict Ω, W1p0.fnL U x ≤ k := by
  have : Nontrivial 𝔽 := (toEuclidean (E := E)).symm.surjective.nontrivial
  have hΩ' : IsOpen (𝓛 '' Ω) := (toEuclidean (E := E)).toHomeomorph.isOpenMap _ hΩ
  have hb' : ∀ y, Op.transfer.b y = 0 := fun y => by simp [transfer, hb]
  have hc' : ∀ᵐ y ∂(μ.map 𝓛), 0 ≤ Op.transfer.c y := by
    filter_upwards [measurePreserving_symm_map.quasiMeasurePreserving.ae hc] with y hy
    simpa [transfer] using hy
  obtain ⟨V, hV⟩ := hbd
  have key := Op.transfer.weak_maximum_principle hΩ' (isBounded_image hΩb) hb' hc'
    (U := (transferEquiv μ Ω U : H1Graph (μ.map 𝓛) (𝓛 '' Ω)))
    (H1Graph.H01_le_W12 (transferEquiv μ Ω U).2) (form_nonpos_of_sub Op Ω U hsub) hk
    ⟨transferEquiv μ Ω V, (transferEquiv_posPart Ω U V k).1 hV⟩
  exact (ae_iff_transfer Ω U U (fun a _ => a ≤ k)).2 key

/-- **Weak maximum principle for a subsolution in `W₀^{1,2}`.** A subsolution of a
transport-free operator with nonnegative zeroth-order coefficient on a bounded open set is
nonpositive almost everywhere. -/
theorem weak_maximum_principle_H01 [Nontrivial E] (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hb : ∀ x, Op.b x = 0) (hc : ∀ᵐ x ∂μ, 0 ≤ Op.c x)
    (U : W1p0 2 μ Ω)
    (hsub : ∀ V : W1p0 2 μ Ω, (∀ᵐ x ∂μ.restrict Ω, 0 ≤ W1p0.fnL V x) →
      Op.formOn Ω U V ≤ 0) :
    ∀ᵐ x ∂μ.restrict Ω, W1p0.fnL U x ≤ 0 := by
  have : Nontrivial 𝔽 := (toEuclidean (E := E)).symm.surjective.nontrivial
  have hΩ' : IsOpen (𝓛 '' Ω) := (toEuclidean (E := E)).toHomeomorph.isOpenMap _ hΩ
  have hb' : ∀ y, Op.transfer.b y = 0 := fun y => by simp [transfer, hb]
  have hc' : ∀ᵐ y ∂(μ.map 𝓛), 0 ≤ Op.transfer.c y := by
    filter_upwards [measurePreserving_symm_map.quasiMeasurePreserving.ae hc] with y hy
    simpa [transfer] using hy
  have key := Op.transfer.weak_maximum_principle_H01 hΩ' (isBounded_image hΩb) hb' hc'
    (transferEquiv μ Ω U) (form_nonpos_of_sub Op Ω U hsub)
  exact (ae_iff_transfer Ω U U (fun a _ => a ≤ 0)).2 key

/-- **Uniqueness of the generalised Dirichlet problem** (Gilbarg and Trudinger Corollary 8.2,
transport-free case). A weak solution in `W₀^{1,2}(Ω)` of the homogeneous equation for a
transport-free operator with nonnegative zeroth-order coefficient on a bounded open set is
zero. -/
theorem eq_zero_of_weakSolution_H01 [Nontrivial E] (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hb : ∀ x, Op.b x = 0) (hc : ∀ᵐ x ∂μ, 0 ≤ Op.c x)
    (U : W1p0 2 μ Ω) (hsol : ∀ V : W1p0 2 μ Ω, Op.formOn Ω U V = 0) : U = 0 := by
  have : Nontrivial 𝔽 := (toEuclidean (E := E)).symm.surjective.nontrivial
  have hΩ' : IsOpen (𝓛 '' Ω) := (toEuclidean (E := E)).toHomeomorph.isOpenMap _ hΩ
  have hb' : ∀ y, Op.transfer.b y = 0 := fun y => by simp [transfer, hb]
  have hc' : ∀ᵐ y ∂(μ.map 𝓛), 0 ≤ Op.transfer.c y := by
    filter_upwards [measurePreserving_symm_map.quasiMeasurePreserving.ae hc] with y hy
    simpa [transfer] using hy
  have key := Op.transfer.eq_zero_of_weakSolution_H01 hΩ' (isBounded_image hΩb) hb' hc'
    (transferEquiv μ Ω U) (fun V => by
      have h : transferEquiv μ Ω ((transferEquiv μ Ω).symm V) = V :=
        ContinuousLinearEquiv.apply_symm_apply _ _
      have e : Op.formOn Ω U ((transferEquiv μ Ω).symm V) =
          Op.transfer.formOn (𝓛 '' Ω) (H1Graph.H01 (μ.map 𝓛) (𝓛 '' Ω)) (transferEquiv μ Ω U) V :=
        (formOn_transfer Op Ω U _).trans
          (congrArg (Op.transfer.formOn (𝓛 '' Ω) (H1Graph.H01 (μ.map 𝓛) (𝓛 '' Ω))
            (transferEquiv μ Ω U)) h)
      exact e.symm.trans (hsol _))
  exact (transferEquiv μ Ω).map_eq_zero_iff.1 key

end FullEllipticOp

end NormedDivForm

end EllipticPdes
