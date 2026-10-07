/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Form.DivFormCoord
public import EllipticPdes.Form.DivFormIsometry
public import EllipticPdes.Regularity.CoeffBridge
public import EllipticPdes.Regularity.CoeffLip
public import EllipticPdes.Regularity.LowerOrderWkInfty

/-!
# Smooth coefficients with bounded derivatives, transported to coordinates

`IsSmoothBdd f` says that `f` is smooth and has a bound on its derivative of each order. Over a
finite-dimensional inner product space `E` the hypothesis is basis free, and it survives
composition with a linear isometry and with a continuous linear map. Hence a divergence-form
operator on `E` with `IsSmoothBdd` coefficients has a transported coordinate operator whose
matrix entries, drift components and potential satisfy the hypotheses of the interior regularity
theory (`IsCkCoeff` at every order, `IsWkInfty` at every order).

## Main declarations

* `EllipticPdes.Regularity.IsSmoothBdd`: smooth with bounded derivatives of every order.
* `EllipticPdes.Regularity.IsSmoothBdd.clm_comp`, `comp_isometry`: stability.
* `EllipticPdes.DivForm.FullEllipticOp.toCoordIso`: the coordinate operator of an operator on `E`
  along `e : E ≃ₗᵢ[ℝ] ℝᵈ`.
* `EllipticPdes.DivForm.FullEllipticOp.ckCoeffToCoordIso`,
  `wkInftyLowerToCoordIso`: the transported hypotheses.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes

set_option linter.unusedSectionVars false

namespace Regularity

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A smooth map whose derivative of each order is bounded. -/
structure IsSmoothBdd (f : E → F) : Prop where
  /-- The map is infinitely differentiable. -/
  contDiff : ContDiff ℝ (⊤ : ℕ∞) f
  /-- The derivative of each order is bounded. -/
  bdd : ∀ m : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ C

namespace IsSmoothBdd

/-- A nonnegative bound on the derivative of order `m`. -/
def bound {f : E → F} (hf : IsSmoothBdd f) (m : ℕ) : ℝ := max 0 (hf.bdd m).choose

/-- The bound is nonnegative. -/
lemma bound_nonneg {f : E → F} (hf : IsSmoothBdd f) (m : ℕ) : 0 ≤ hf.bound m := le_max_left _ _

/-- The derivative of order `m` is at most `hf.bound m` everywhere. -/
lemma norm_iteratedFDeriv_le {f : E → F} (hf : IsSmoothBdd f) (m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m f x‖ ≤ hf.bound m :=
  ((hf.bdd m).choose_spec x).trans (le_max_right _ _)

/-- The derivative of order `m` of `L ∘ f` is at most `‖L‖` times that of `f`. -/
lemma norm_iteratedFDeriv_clm_comp_le {f : E → F} (hf : IsSmoothBdd f) (L : F →L[ℝ] G) (m : ℕ)
    (x : E) :
    ‖iteratedFDeriv ℝ m (fun y => L (f y)) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ m f x‖ :=
  L.norm_iteratedFDeriv_comp_left (hf.contDiff.contDiffAt (x := x)) (by exact_mod_cast le_top)

/-- The image of a smooth map with bounded derivatives under a continuous linear map has the
same property. -/
lemma clm_comp {f : E → F} (hf : IsSmoothBdd f) (L : F →L[ℝ] G) :
    IsSmoothBdd (fun x => L (f x)) where
  contDiff := L.contDiff.comp hf.contDiff
  bdd m := ⟨‖L‖ * hf.bound m, fun x =>
    (hf.norm_iteratedFDeriv_clm_comp_le L m x).trans
      (by gcongr; exact hf.norm_iteratedFDeriv_le m x)⟩

/-- Composition with a linear isometry equivalence on the right preserves the property. -/
lemma comp_isometry {f : E → F} (hf : IsSmoothBdd f) (g : G ≃ₗᵢ[ℝ] E) :
    IsSmoothBdd (fun x => f (g x)) where
  contDiff := hf.contDiff.comp g.contDiff
  bdd m := ⟨hf.bound m, fun x => by
    have h := g.norm_iteratedFDeriv_comp_right f x m
    exact (le_of_eq h).trans (hf.norm_iteratedFDeriv_le m _)⟩

end IsSmoothBdd

end Regularity

namespace DivForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {d : ℕ}

/-- The functional `T ↦ ⟪w, e (T v)⟫` on endomorphisms of `E`, a matrix entry in the coordinates
of `e`. -/
def entryL (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (v : E) (w : EuclideanSpace ℝ (Fin d)) :
    (E →L[ℝ] E) →L[ℝ] ℝ :=
  ((innerSL ℝ w).comp (e.toContinuousLinearEquiv : E →L[ℝ] EuclideanSpace ℝ (Fin d))).comp
    (ContinuousLinearMap.apply ℝ E v)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `entryL e v w` evaluates to `⟪w, e (T v)⟫`. -/
@[simp] lemma entryL_apply (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (v : E)
    (w : EuclideanSpace ℝ (Fin d)) (T : E →L[ℝ] E) : entryL e v w T = ⟪w, e (T v)⟫ := rfl

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- A matrix entry functional of unit vectors has norm at most one. -/
lemma norm_entryL_le (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) {v : E}
    {w : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) : ‖entryL e v w‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => by
    rw [entryL_apply, one_mul]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hw, one_mul, LinearIsometryEquiv.norm_map]
    simpa [hv] using T.le_opNorm v

namespace FullEllipticOp

/-- **The coordinate operator of an operator on `E`, along `e : E ≃ₗᵢ[ℝ] ℝᵈ`.** It is
`toCoord` of the transported operator `mapIsometry e Op`, for continuous coefficients. -/
def toCoordIso (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (Op : FullEllipticOp (volume : Measure E)) (ha : Continuous Op.a) (hb : Continuous Op.b)
    (hc : Continuous Op.c) : Sobolev.FullEllipticOp d :=
  (Op.mapIsometry e).toCoord ((continuous_conjIso e).comp (ha.comp e.symm.continuous)).measurable
    (e.continuous.comp (hb.comp e.symm.continuous)).measurable
    (hc.comp e.symm.continuous).measurable

variable (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (Op : FullEllipticOp (volume : Measure E))
  (ha : Continuous Op.a) (hb : Continuous Op.b) (hc : Continuous Op.c)

/-- The matrix entries of `toCoordIso`. -/
lemma toCoordIso_a (x : EuclideanSpace ℝ (Fin d)) (i j : Fin d) :
    (toCoordIso e Op ha hb hc).a x i j =
      ⟪e (Op.a (e.symm x) (e.symm (EuclideanSpace.single i (1 : ℝ)))),
        EuclideanSpace.single j (1 : ℝ)⟫ := rfl

/-- The drift components of `toCoordIso`. -/
lemma toCoordIso_b (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    (toCoordIso e Op ha hb hc).b x i = (e (Op.b (e.symm x))) i := rfl

/-- The potential of `toCoordIso`. -/
lemma toCoordIso_c (x : EuclideanSpace ℝ (Fin d)) :
    (toCoordIso e Op ha hb hc).c x = Op.c (e.symm x) := rfl

/-- The coordinate form of `toCoordIso` is the form of the transported operator on the graph
space. -/
lemma fullBilin_toCoordIso (Ω' : Set (EuclideanSpace ℝ (Fin d))) (U V : Sobolev.H01 Ω') :
    (toCoordIso e Op ha hb hc).fullBilin Ω' U V =
      (Op.mapIsometry e).formOn Ω' (H1Graph.H01 volume Ω') (H1Graph.h01Equiv Ω' U)
        (H1Graph.h01Equiv Ω' V) :=
  (formOn_h01Equiv_toCoord (Op.mapIsometry e) _ _ _ Ω' U V).symm

/-- **A weak solution on `E` is a weak solution of the coordinate operator.** -/
theorem weak_toCoordIso (Ω : Set E) (u : H1Graph.H01 volume Ω) (f : Lp ℝ 2 (volume.restrict Ω))
    (h : ∀ v : H1Graph.H01 volume Ω,
      Op.formOn Ω (H1Graph.H01 volume Ω) u v = ⟪f, H1Graph.embL2 volume Ω v⟫)
    (w : Sobolev.H01 (e.symm ⁻¹' Ω)) :
    (toCoordIso e Op ha hb hc).fullBilin (e.symm ⁻¹' Ω)
        ((H1Graph.h01Equiv (e.symm ⁻¹' Ω)).symm (H1Graph.mapH01 e Ω u)) w =
      ∫ x in e.symm ⁻¹' Ω, (H1Graph.pullFn e Ω f x : ℝ) *
        ((w : Sobolev.H1amb (e.symm ⁻¹' Ω)) 0 x : ℝ) := by
  rw [fullBilin_toCoordIso, (H1Graph.h01Equiv _).apply_symm_apply,
    weak_mapH01 e Op Ω u f h, H1Graph.embL2_h01Equiv, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- **The transported coefficient matrix is a `Cᵏ` bundle at every order.** The entries are
`(entryL e v w) ∘ a ∘ e.symm` for unit vectors `v`, `w`, so the bounds of `a` apply. -/
def ckCoeffToCoordIso (hOp : Regularity.IsSmoothBdd Op.a) (k : ℕ) :
    Regularity.IsCkCoeff (toCoordIso e Op ha hb hc).toEllipticCoeff k where
  contDiff i j := by
    have h : (fun x => (toCoordIso e Op ha hb hc).a x i j) = fun x =>
        entryL e (e.symm (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ))
          (Op.a (e.symm x)) := by
      funext x; rw [toCoordIso_a, entryL_apply, real_inner_comm]
    rw [h]
    exact (((hOp.comp_isometry e.symm).clm_comp _).contDiff).of_le (by exact_mod_cast le_top)
  bound m := hOp.bound m
  bound_nonneg m := hOp.bound_nonneg m
  iteratedFDeriv_bdd i j m _ _ x := by
    have h : (fun x => (toCoordIso e Op ha hb hc).a x i j) = fun x =>
        entryL e (e.symm (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ))
          (Op.a (e.symm x)) := by
      funext x; rw [toCoordIso_a, entryL_apply, real_inner_comm]
    have hv : ‖e.symm (EuclideanSpace.single i (1 : ℝ))‖ = 1 := by simp
    have hw : ‖(EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin d))‖ = 1 := by simp
    rw [h]
    calc _ ≤ ‖entryL e _ _‖ * ‖iteratedFDeriv ℝ m (fun x => Op.a (e.symm x)) x‖ :=
          (hOp.comp_isometry e.symm).norm_iteratedFDeriv_clm_comp_le _ m x
      _ ≤ 1 * hOp.bound m := by
          have h2 := LinearIsometryEquiv.norm_iteratedFDeriv_comp_right e.symm Op.a x m
          change ‖iteratedFDeriv ℝ m (Op.a ∘ e.symm) x‖ = _ at h2
          change _ * ‖iteratedFDeriv ℝ m (Op.a ∘ e.symm) x‖ ≤ _
          rw [h2]
          gcongr
          · exact norm_entryL_le e hv hw
          · exact hOp.norm_iteratedFDeriv_le m _
      _ = _ := one_mul _

/-- **The transported drift and potential are in `W^{k,∞}`.** -/
def wkInftyLowerToCoordIso (hOb : Regularity.IsSmoothBdd Op.b)
    (hOc : Regularity.IsSmoothBdd Op.c) (k : ℕ) :
    Regularity.IsWkInftyLower (toCoordIso e Op ha hb hc) k := by
  refine Regularity.IsWkInftyLower.ofBundles (fun i => ?_) ?_
  · have hf : Regularity.IsSmoothBdd
        (fun x => ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).comp
          (e.toContinuousLinearEquiv : E →L[ℝ] EuclideanSpace ℝ (Fin d))) (Op.b (e.symm x))) :=
      (hOb.comp_isometry e.symm).clm_comp _
    exact Regularity.IsWkInfty.ofContDiff (B := hf.bound) (hf.contDiff.of_le
      (by exact_mod_cast le_top)) hf.bound_nonneg fun m _ x => hf.norm_iteratedFDeriv_le m x
  · have hf := hOc.comp_isometry e.symm
    exact Regularity.IsWkInfty.ofContDiff (B := hf.bound) (hf.contDiff.of_le
      (by exact_mod_cast le_top)) hf.bound_nonneg fun m _ x => hf.norm_iteratedFDeriv_le m x

end FullEllipticOp

end DivForm

end EllipticPdes
