/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Existence.DivFormMaximum
public import EllipticPdes.Existence.Garding
public import EllipticPdes.Embedding.ChainRule
public import EllipticPdes.Extension.GlobalApproximation
public import EllipticPdes.Form.DivFormEuclidean
public import EllipticPdes.Poincare.BoundedDomain

/-!
# Weak maximum principle in coordinates

A weak subsolution of a transport-free divergence-form equation with nonnegative zeroth-order
coefficient is bounded above by its boundary values. The boundary inequality `u ≤ k on ∂Ω`
for a Sobolev class is read, following Gilbarg and Trudinger, as membership of `(u - k)⁺` in
`H₀¹(Ω)`, and the conclusion is `u ≤ k` almost everywhere for every `k ≥ 0` with that
property, which is the inequality `sup_Ω u ≤ sup_∂Ω u⁺` between the essential supremum and
the infimum of such `k`.

The theorem is `EllipticPdes.DivForm.FullEllipticOp.weak_maximum_principle`, over a
finite-dimensional inner product space. The coordinate statement here is its transport along
`EllipticPdes.H1Graph.h1Equiv`: a coordinate operator is read as a divergence-form operator by
`EllipticPdes.DivForm.FullEllipticOp.ofCoord`, and the bilinear pairing of a class `U` of `H¹`
against an element of `H₀¹` is the sum of the pairings of the coordinates
(`EllipticPdes.DivForm.FullEllipticOp.form_eq_sum`).

## Main declarations

* `EllipticPdes.Sobolev.weak_maximum_principle`: the weak maximum principle for a
  transport-free coordinate operator with nonnegative zeroth-order coefficient.
* `EllipticPdes.DivForm.FullEllipticOp.form_eq_sum`: the full form of `ofCoord Op` on classes of
  `H¹` is the coordinate sum.

## References

D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§8.1 Theorem 8.1 (p. 179);
L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.4.1 Theorem 2 (p. 346).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes

namespace DivForm

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The components of the gradient part of `X` are the coordinates of `h1Equiv X`. -/
lemma ae_gradL_h1Equiv (X : H1Graph volume Ω) :
    ∀ᵐ x ∂(volume.restrict Ω), ∀ i : Fin d,
      H1Graph.gradL X x i = (H1Graph.h1Equiv Ω X) i.succ x := by
  refine ae_all_iff.2 fun i => ?_
  have h := H1Graph.h1Equiv_apply_succ Ω X i
  filter_upwards [ContinuousLinearMap.coeFn_compLp
    (EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (H1Graph.gradL X)] with x hx
  rw [h, hx]
  rfl

/-- The principal form of `ofCoord A` on classes of `H¹` is the coordinate sum. -/
theorem EllipticCoeff.form_eq_sum (A : Sobolev.EllipticCoeff d) (X Y : H1Graph volume Ω) :
    (EllipticCoeff.ofCoord A).form Ω X Y = ∑ i, ∑ j,
      ⟪A.actL i j ((H1Graph.h1Equiv Ω X) i.succ), (H1Graph.h1Equiv Ω Y) j.succ⟫ := by
  rw [EllipticCoeff.form_eq_integral]
  have key : ∫ x in Ω, (⟪(EllipticCoeff.ofCoord A).a x (H1Graph.gradL X x),
        H1Graph.gradL Y x⟫) =
      ∫ x in Ω, (∑ i : Fin d, ∑ j : Fin d,
        A.a x i j * ((H1Graph.h1Equiv Ω X) i.succ x : ℝ) *
          ((H1Graph.h1Equiv Ω Y) j.succ x : ℝ)) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_gradL_h1Equiv X, ae_gradL_h1Equiv Y] with x hX hY
    rw [EllipticCoeff.inner_ofCoord_a]
    simp only [hX, hY]
  rw [key, integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => A.integrable_triple i j _ _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => A.integrable_triple i j _ _)]
  exact Finset.sum_congr rfl fun j _ => (A.inner_actL_eq i j _ _).symm

/-- The lower-order form of `ofCoord Op` on classes of `H¹` is the coordinate sum. -/
theorem FullEllipticOp.lowerForm_eq_sum (Op : Sobolev.FullEllipticOp d)
    (X Y : H1Graph volume Ω) :
    (FullEllipticOp.ofCoord Op).lowerForm Ω X Y =
      (∑ i, ⟪Op.bAct i ((H1Graph.h1Equiv Ω X) i.succ), (H1Graph.h1Equiv Ω Y) 0⟫)
        + ⟪Op.cAct ((H1Graph.h1Equiv Ω X) 0), (H1Graph.h1Equiv Ω Y) 0⟫ := by
  have hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), |Op.b x i| ≤ Op.Bsup :=
    fun i => ae_restrict_of_ae (Op.b_bdd i)
  have hc : ∀ᵐ x ∂(volume.restrict Ω), |Op.c x| ≤ Op.Csup := ae_restrict_of_ae Op.c_bdd
  rw [FullEllipticOp.lowerForm_eq_integral]
  simp only [Sobolev.FullEllipticOp.bAct, Sobolev.FullEllipticOp.cAct, Sobolev.inner_mulCoeffL_eq]
  have key : ∫ x in Ω, (⟪(FullEllipticOp.ofCoord Op).b x, H1Graph.gradL X x⟫ *
        H1Graph.fnL Y x + (FullEllipticOp.ofCoord Op).c x * H1Graph.fnL X x *
        H1Graph.fnL Y x) =
      ∫ x in Ω, (∑ i : Fin d, Op.b x i * ((H1Graph.h1Equiv Ω X) i.succ x : ℝ) *
          ((H1Graph.h1Equiv Ω Y) 0 x : ℝ) +
        Op.c x * ((H1Graph.h1Equiv Ω X) 0 x : ℝ) * ((H1Graph.h1Equiv Ω Y) 0 x : ℝ)) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_gradL_h1Equiv X] with x hX
    beta_reduce
    rw [FullEllipticOp.inner_ofCoord_b Op x]
    simp only [hX, Finset.sum_mul]
    rfl
  rw [key, integral_add (integrable_finsetSum _ fun i _ => integrable_mulCoeff (Op.b_meas i)
      (hb i) _ _) (integrable_mulCoeff Op.c_meas hc _ _),
    integral_finsetSum _ fun i _ => integrable_mulCoeff (Op.b_meas i) (hb i) _ _]

/-- **The full form on classes of `H¹` is the coordinate sum.** The pairing of `ofCoord Op` on
`h1Equiv.symm U` against `h1Equiv.symm V` is the sum of the principal, transport and
zeroth-order pairings of the coordinates of `U` and `V`. -/
theorem FullEllipticOp.form_eq_sum (Op : Sobolev.FullEllipticOp d) (U V : Sobolev.H1amb Ω) :
    (FullEllipticOp.ofCoord Op).form Ω ((H1Graph.h1Equiv Ω).symm U)
        ((H1Graph.h1Equiv Ω).symm V) =
      (∑ i, ∑ j, ⟪Op.toEllipticCoeff.actL i j (U i.succ), V j.succ⟫)
        + (∑ i, ⟪Op.bAct i (U i.succ), V 0⟫) + ⟪Op.cAct (U 0), V 0⟫ := by
  rw [FullEllipticOp.form_apply, FullEllipticOp.ofCoord_toEllipticCoeff,
    EllipticCoeff.form_eq_sum, FullEllipticOp.lowerForm_eq_sum]
  simp only [LinearIsometryEquiv.apply_symm_apply, add_assoc]

/-- The function part of `h1Equiv.symm U` is the coordinate `0` of `U`. -/
lemma fnL_h1Equiv_symm (U : Sobolev.H1amb Ω) :
    H1Graph.fnL ((H1Graph.h1Equiv Ω).symm U) = U 0 := by
  rw [← H1Graph.h1Equiv_apply_zero, LinearIsometryEquiv.apply_symm_apply]

/-- A class of `W^{1,2}` in coordinates is a class of `W^{1,2}` of the graph space. -/
lemma h1Equiv_symm_mem_W12 {U : Sobolev.H1amb Ω} (hU : U ∈ Sobolev.W12 Ω) :
    (H1Graph.h1Equiv Ω).symm U ∈ H1Graph.W12 volume Ω := by
  rw [← H1Graph.h1Equiv_mem_W12_iff, LinearIsometryEquiv.apply_symm_apply]
  exact hU

/-- **The coordinate subsolution inequality is the divergence-form one.** -/
theorem FullEllipticOp.form_le_zero_of_coord (Op : Sobolev.FullEllipticOp d)
    {U : Sobolev.H1amb Ω}
    (hsub : ∀ V : Sobolev.H01 Ω, (∀ᵐ x ∂(volume.restrict Ω), 0 ≤ ((V : Sobolev.H1amb Ω) 0 x : ℝ)) →
      (∑ i, ∑ j, ⟪Op.toEllipticCoeff.actL i j (U i.succ), (V : Sobolev.H1amb Ω) j.succ⟫)
        + (∑ i, ⟪Op.bAct i (U i.succ), (V : Sobolev.H1amb Ω) 0⟫)
        + ⟪Op.cAct (U 0), (V : Sobolev.H1amb Ω) 0⟫ ≤ 0)
    (V : H1Graph.H01 volume Ω)
    (hV : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ H1Graph.fnL (V : H1Graph volume Ω) x) :
    (FullEllipticOp.ofCoord Op).form Ω ((H1Graph.h1Equiv Ω).symm U) V ≤ 0 := by
  set W : Sobolev.H01 Ω := (H1Graph.h01Equiv Ω).symm V with hW
  have hWV : H1Graph.h01Equiv Ω W = V := LinearIsometryEquiv.apply_symm_apply _ _
  have e1 : (H1Graph.h1Equiv Ω).symm (W : Sobolev.H1amb Ω) = (V : H1Graph volume Ω) := by
    rw [LinearIsometryEquiv.symm_apply_eq]
    have := H1Graph.h1Equiv_h01Equiv Ω W
    rwa [hWV] at this
  have h := hsub W (by
    filter_upwards [hV, ae_fnL_h01Equiv Ω W] with x h1 h2
    rw [hWV] at h2
    rwa [← h2])
  rwa [← FullEllipticOp.form_eq_sum, e1] at h

/-- **The boundary condition in coordinates is the one of the graph space.** -/
theorem exists_fnL_eq_max_of_coord {U : Sobolev.H1amb Ω} {k : ℝ}
    (hbd : ∃ V : Sobolev.H01 Ω, ((V : Sobolev.H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => max ((U 0 x : ℝ) - k) 0) :
    ∃ V : H1Graph.H01 volume Ω, ⇑(H1Graph.fnL (V : H1Graph volume Ω)) =ᵐ[volume.restrict Ω]
      fun x => max (H1Graph.fnL ((H1Graph.h1Equiv Ω).symm U) x - k) 0 := by
  obtain ⟨V₀, hV₀⟩ := hbd
  refine ⟨H1Graph.h01Equiv Ω V₀, ?_⟩
  filter_upwards [ae_fnL_h01Equiv Ω V₀, hV₀] with x h1 h2
  rw [h1, h2, fnL_h1Equiv_symm]

end DivForm

namespace Sobolev

open EllipticPdes.Embedding EllipticPdes.Extension EllipticPdes.Poincare

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- **Weak maximum principle** (Gilbarg and Trudinger Theorem 8.1, in the transport-free
case). Let `Ω` be a bounded open set, `L` a divergence-form operator with no transport term and
nonnegative zeroth-order coefficient, and `U ∈ H¹(Ω)` a weak subsolution, meaning the bilinear
pairing of `U` against every nonnegative `V ∈ H₀¹(Ω)` is nonpositive. If `k ≥ 0` and
`(u - k)⁺` is the function coordinate of some element of `H₀¹(Ω)`, then `u ≤ k` almost
everywhere on `Ω`. -/
theorem weak_maximum_principle (hd : 0 < d) (hΩopen : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (Op : FullEllipticOp d) (hb : ∀ x i, Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), 0 ≤ Op.c x)
    {U : H1amb Ω} (hU : U ∈ W12 Ω)
    (hsub : ∀ V : H01 Ω, (∀ᵐ x ∂(volume.restrict Ω), 0 ≤ ((V : H1amb Ω) 0 x : ℝ)) →
      (∑ i, ∑ j, ⟪Op.toEllipticCoeff.actL i j (U i.succ), (V : H1amb Ω) j.succ⟫)
        + (∑ i, ⟪Op.bAct i (U i.succ), (V : H1amb Ω) 0⟫)
        + ⟪Op.cAct (U 0), (V : H1amb Ω) 0⟫ ≤ 0)
    {k : ℝ} (hk : 0 ≤ k)
    (hbd : ∃ V : H01 Ω, ((V : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => max ((U 0 x : ℝ) - k) 0) :
    ∀ᵐ x ∂(volume.restrict Ω), (U 0 x : ℝ) ≤ k := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.1 hd
  have := DivForm.FullEllipticOp.weak_maximum_principle (DivForm.FullEllipticOp.ofCoord Op)
    hΩopen hΩb (fun x => by ext i; simp [DivForm.FullEllipticOp.ofCoord, hb]) hc
    (DivForm.h1Equiv_symm_mem_W12 hU) (DivForm.FullEllipticOp.form_le_zero_of_coord Op hsub) hk
    (DivForm.exists_fnL_eq_max_of_coord hbd)
  simpa only [DivForm.fnL_h1Equiv_symm] using this

end Sobolev

end EllipticPdes
