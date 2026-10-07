/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.DivFormInstances
public import EllipticPdes.Existence.DivFormExistence
public import EllipticPdes.Regularity.ClassicalSolvability
public import EllipticPdes.Regularity.Localise.Datum
public import EllipticPdes.Regularity.SmoothBdd

/-!
# Interior smoothness over a finite-dimensional inner product space

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 3 (p. 334), for a
divergence-form operator on a finite-dimensional real inner product space `E` with its canonical
volume. A linear isometry equivalence `e : E ≃ₗᵢ[ℝ] ℝᵈ` carries the problem to the coordinate
problem (`DivForm.FullEllipticOp.mapIsometry`, `H1Graph.mapH01`, `FullEllipticOp.toCoordIso`),
the coordinate theorem `Regularity.interior_smooth` applies, and the smooth representative is
carried back by composition with `e`.

The coefficients are smooth with bounded derivatives of every order (`Regularity.IsSmoothBdd`),
and the datum is the restriction of a smooth compactly supported function.

## Main declarations

* `EllipticPdes.DivForm.FullEllipticOp.interior_smooth`: a weak solution in `H₀¹(Ω)` has a
  representative smooth on the interior of each compact `V ⊆ Ω`.
* `EllipticPdes.DivForm.FullEllipticOp.exists_weakSolution_interior_smooth`: on a bounded open
  set, the Dirichlet problem has such a weak solution.
-/

@[expose] public section

open MeasureTheory Module
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.DivForm.FullEllipticOp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The transported datum has weak derivatives of every order in `L²`, bounded. -/
lemma datum_pullFn {d : ℕ} (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) {Ω : Set E}
    (f : Lp ℝ 2 (volume.restrict Ω)) {g : E → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (hfg : f =ᵐ[volume.restrict Ω] g) (k : ℕ) :
    ∃ hfk : Regularity.HasIteratedWeakDerivOn (e.symm ⁻¹' Ω) k (H1Graph.pullFn e Ω f),
      ∃ M : ℝ, Regularity.IteratedL2Bound hfk M := by
  have hg' : ContDiff ℝ (⊤ : ℕ∞) (g ∘ e.symm) := hg.comp e.symm.contDiff
  have hgc' : HasCompactSupport (g ∘ e.symm) :=
    hgc.comp_isClosedEmbedding e.symm.toHomeomorph.isClosedEmbedding
  have hEq : H1Graph.pullFn e Ω f = Regularity.toL2 hg' hgc' (e.symm ⁻¹' Ω) := by
    have h0 : ⇑(Regularity.toL2 hg' hgc' (e.symm ⁻¹' Ω)) =ᵐ[volume.restrict (e.symm ⁻¹' Ω)]
        g ∘ e.symm := MemLp.coeFn_toLp _
    refine Lp.ext ?_
    filter_upwards [H1Graph.coeFn_pullFn e Ω f,
      (H1Graph.measurePreserving_symm_restrict e Ω).quasiMeasurePreserving.ae hfg, h0]
      with y h1 h2 h3
    rw [h1, h3]
    exact h2
  rw [hEq]
  exact Regularity.datum_hyp hg' hgc' _ k

/-- The extension by zero of a class on `Ω` agrees with the class on any measurable subset. -/
lemma coeFn_extendL2_ae {d : ℕ} {Ω W : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    (g : Sobolev.L2D Ω) (hW : MeasurableSet W) (hWΩ : W ⊆ Ω) :
    ⇑(Regularity.extendL2 hΩm g) =ᵐ[volume.restrict W] ⇑g := by
  filter_upwards [ae_restrict_of_ae (Regularity.coeFn_extendL2 hΩm g),
    ae_restrict_mem hW] with y hy hmem
  rw [hy, Set.indicator_of_mem (hWΩ hmem)]

/-- A representative smooth on the interior of `e.symm ⁻¹' V` for the transported class gives a
representative smooth on the interior of `V` for the class. -/
lemma contDiffOn_of_pullFn {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E'] (e : E ≃ₗᵢ[ℝ] E') {Ω V : Set E}
    (U : Lp ℝ 2 (volume.restrict Ω)) (hVΩ : V ⊆ Ω) {u' : E' → ℝ}
    (hae : u' =ᵐ[volume.restrict (interior (e.symm ⁻¹' V))] ⇑(H1Graph.pullFn e Ω U))
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) u' (interior (e.symm ⁻¹' V))) :
    ∃ w : E → ℝ, w =ᵐ[volume.restrict (interior V)] ⇑U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) w (interior V) := by
  have hint : interior (e.symm ⁻¹' V) = e.symm ⁻¹' interior V :=
    (e.symm.toHomeomorph.preimage_interior V).symm
  have hsub : interior (e.symm ⁻¹' V) ⊆ e.symm ⁻¹' Ω :=
    interior_subset.trans (Set.preimage_mono hVΩ)
  have h2 : ⇑(H1Graph.pullFn e Ω U) =ᵐ[volume.restrict (interior (e.symm ⁻¹' V))]
      fun y => U (e.symm y) :=
    (H1Graph.coeFn_pullFn e Ω U).filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  rw [hint] at hae h2 hsm
  refine ⟨fun x => u' (e x), ?_, ?_⟩
  · filter_upwards [(H1Graph.measurePreserving_restrict e (interior V)).quasiMeasurePreserving.ae
      (hae.trans h2)] with x hx
    simpa using hx
  · exact hsm.comp e.contDiff.contDiffOn fun x hx => by simpa using hx

/-- **Infinite differentiability in the interior (Evans, *Partial Differential Equations*
(2nd ed.), §6.3.1, Theorem 3, p. 334), over a finite-dimensional inner product space.** For an
operator whose coefficients `a`, `b`, `c` are smooth with bounded derivatives of every order, a
datum `f ∈ L²(Ω)` that is the restriction of a smooth compactly supported function `g`, and a
weak solution `u ∈ H₀¹(Ω)` of `B[u, v] = ⟪f, v⟫`, the function part of `u` has a representative
that is smooth on the interior of every compact `V ⊆ Ω`. -/
theorem interior_smooth {n : ℕ} (hd : finrank ℝ E = n + 1)
    (Op : FullEllipticOp (volume : Measure E)) {Ω : Set E} (hΩm : MeasurableSet Ω)
    (hΩo : IsOpen Ω) (hA : Regularity.IsSmoothBdd Op.a) (hB : Regularity.IsSmoothBdd Op.b)
    (hC : Regularity.IsSmoothBdd Op.c) (u : H1Graph.H01 volume Ω)
    (f : Lp ℝ 2 (volume.restrict Ω)) {g : E → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (hfg : f =ᵐ[volume.restrict Ω] g)
    (hweak : ∀ v : H1Graph.H01 volume Ω,
      Op.formOn Ω (H1Graph.H01 volume Ω) u v = ⟪f, H1Graph.embL2 volume Ω v⟫)
    {V : Set E} (hVc : IsCompact V) (hVΩ : V ⊆ Ω) :
    ∃ u' : E → ℝ, u' =ᵐ[volume.restrict (interior V)] ⇑(H1Graph.embL2 volume Ω u) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) u' (interior V) := by
  let e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    ((stdOrthonormalBasis ℝ E).reindex (finCongr hd)).repr
  have hΩ'm : MeasurableSet (e.symm ⁻¹' Ω) := e.symm.continuous.measurable hΩm
  have hΩ'o : IsOpen (e.symm ⁻¹' Ω) := hΩo.preimage e.symm.continuous
  have ha := hA.contDiff.continuous
  have hb := hB.contDiff.continuous
  have hc := hC.contDiff.continuous
  have hV'c : IsCompact (e.symm ⁻¹' V) := e.symm.toHomeomorph.isCompact_preimage.2 hVc
  have hV'Ω : e.symm ⁻¹' V ⊆ e.symm ⁻¹' Ω := Set.preimage_mono hVΩ
  obtain ⟨u', hae, hsm⟩ := Regularity.interior_smooth (toCoordIso e Op ha hb hc) hΩ'm hΩ'o
    ((ckCoeffToCoordIso e Op ha hb hc hA 1).toIsC1Coeff le_rfl).toIsLipCoeff
    (fun k => (ckCoeffToCoordIso e Op ha hb hc hA k).toIsWkInftyCoeff)
    (fun k => wkInftyLowerToCoordIso e Op ha hb hc hB hC k)
    ((H1Graph.h01Equiv (e.symm ⁻¹' Ω)).symm (H1Graph.mapH01 e Ω u)) (H1Graph.pullFn e Ω f)
    (datum_pullFn e f hg hgc hfg) (weak_toCoordIso e Op ha hb hc Ω u f hweak) hV'c hV'Ω
  have hsub : interior (e.symm ⁻¹' V) ⊆ e.symm ⁻¹' Ω := interior_subset.trans hV'Ω
  have hu0 : ((H1Graph.h01Equiv (e.symm ⁻¹' Ω)).symm (H1Graph.mapH01 e Ω u) :
      Sobolev.H01 (e.symm ⁻¹' Ω)).1 0 = H1Graph.pullFn e Ω (H1Graph.embL2 volume Ω u) := by
    rw [← H1Graph.fnL_h01Equiv, LinearIsometryEquiv.apply_symm_apply]
    rfl
  rw [hu0] at hae
  exact contDiffOn_of_pullFn e (H1Graph.embL2 volume Ω u) hVΩ
    (hae.trans (coeFn_extendL2_ae hΩ'm _ isOpen_interior.measurableSet hsub)) hsm

/-- **Solvability with a smooth interior representative, over a finite-dimensional inner product
space.** On a bounded open set, for an operator with no drift and a nonnegative zeroth-order
coefficient, whose coefficients are smooth with bounded derivatives of every order, and for a
datum that is the restriction of a smooth compactly supported function, the Dirichlet problem has
a weak solution in `H₀¹(Ω)` whose function part has a representative smooth on the interior of
every compact `V ⊆ Ω`. -/
theorem exists_weakSolution_interior_smooth {n : ℕ} (hd : finrank ℝ E = n + 1)
    (Op : FullEllipticOp (volume : Measure E)) {Ω : Set E} (hΩm : MeasurableSet Ω)
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hb : ∀ᵐ x ∂(volume : Measure E).restrict Ω, Op.b x = 0)
    (hc : ∀ᵐ x ∂(volume : Measure E).restrict Ω, 0 ≤ Op.c x)
    (hA : Regularity.IsSmoothBdd Op.a) (hB : Regularity.IsSmoothBdd Op.b)
    (hC : Regularity.IsSmoothBdd Op.c) (f : Lp ℝ 2 (volume.restrict Ω)) {g : E → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (hfg : f =ᵐ[volume.restrict Ω] g)
    {V : Set E} (hVc : IsCompact V) (hVΩ : V ⊆ Ω) :
    ∃ u : H1Graph.H01 volume Ω,
      (∀ v : H1Graph.H01 volume Ω,
        Op.formOn Ω (H1Graph.H01 volume Ω) u v = ⟪f, H1Graph.embL2 volume Ω v⟫) ∧
      ∃ u' : E → ℝ, u' =ᵐ[volume.restrict (interior V)] ⇑(H1Graph.embL2 volume Ω u) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) u' (interior V) := by
  have : 0 < finrank ℝ E := by omega
  have : Nontrivial E := Module.finrank_pos_iff.1 this
  obtain ⟨_CP, _hCP, hsol⟩ := weak_solution_of_nonneg_zeroth_of_bounded Op hΩb hb hc
  obtain ⟨⟨u, hu, -⟩, -⟩ := hsol f
  exact ⟨u, hu, interior_smooth hd Op hΩm hΩo hA hB hC u f hg hgc hfg hu hVc hVΩ⟩

end EllipticPdes.DivForm.FullEllipticOp
