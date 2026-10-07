/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Existence.DivFormMaximumTransport
public import EllipticPdes.Existence.WeakMaximum
public import EllipticPdes.Sobolev.H01Lattice

/-!
# Weak maximum principle with a transport term, in coordinates

Gilbarg and Trudinger's Theorem 8.1 with the transport term present, in dimension at least
two. The theorem is `EllipticPdes.DivForm.FullEllipticOp.weak_maximum_principle_transport`,
over a finite-dimensional inner product space, and the truncations at every level above the
boundary value are `EllipticPdes.H1Graph.exists_truncation_mem_H01`. The coordinate statements
here are their transport along `EllipticPdes.H1Graph.h1Equiv`, with the coordinate operator read
as a divergence-form operator by `EllipticPdes.DivForm.FullEllipticOp.ofCoord`.

## Main declarations

* `EllipticPdes.Sobolev.exists_truncation_mem_H01`: the truncation `(u - k)⁺` is in `H₀¹` for
  every level `k` above the boundary value.
* `EllipticPdes.Sobolev.weak_maximum_principle_transport`: the weak maximum principle with a
  transport term, in dimension at least two.

## References

D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§8.1 Theorem 8.1 (pp. 179–180).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- **Truncations at every level above the boundary value in `H₀¹`.** If `(u - k₀)⁺` is
the function coordinate of an element of `H₀¹(Ω)`, then for every `k ≥ k₀` there is an element
of `H₀¹(Ω)` with function coordinate `(u - k)⁺` and gradient coordinates those of `u` on
`{u > k}` and zero elsewhere. -/
theorem exists_truncation_mem_H01 (hΩopen : IsOpen Ω) (_hΩb : Bornology.IsBounded Ω)
    {U : H1amb Ω} (hU : U ∈ W12 Ω) {k₀ : ℝ} (V₀ : H01 Ω)
    (hV₀ : ((V₀ : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => max ((U 0 x : ℝ) - k₀) 0)
    {k : ℝ} (hk : k₀ ≤ k) :
    ∃ V : H01 Ω,
      (((V : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] fun x => max ((U 0 x : ℝ) - k) 0) ∧
      ∀ i : Fin d, ((V : H1amb Ω) i.succ : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] fun x => if k < (U 0 x : ℝ) then (U i.succ x : ℝ) else 0 := by
  have hU' := DivForm.h1Equiv_symm_mem_W12 hU
  have hfU := DivForm.fnL_h1Equiv_symm U
  have hgU := DivForm.ae_gradL_h1Equiv ((H1Graph.h1Equiv Ω).symm U)
  simp only [LinearIsometryEquiv.apply_symm_apply] at hgU
  obtain ⟨V', hV'0, hV'g⟩ := H1Graph.exists_truncation_mem_H01 hΩopen hU'
    (V₀ := H1Graph.h01Equiv Ω V₀)
    (by
      filter_upwards [DivForm.ae_fnL_h01Equiv Ω V₀, hV₀] with x h1 h2
      rw [h1, h2, hfU]) hk
  set V : H01 Ω := (H1Graph.h01Equiv Ω).symm V' with hV
  have hVV : (H1Graph.h01Equiv Ω V : H1Graph volume Ω) = V' := by
    rw [hV, LinearIsometryEquiv.apply_symm_apply]
  refine ⟨V, ?_, fun i => ?_⟩
  · filter_upwards [hV'0, DivForm.ae_fnL_h01Equiv Ω V] with x h1 h2
    rw [hVV] at h2
    rw [← h2, h1, hfU]
  · filter_upwards [hV'g, DivForm.ae_gradL_h01Equiv Ω V, hgU] with x h1 h2 h3
    rw [hVV] at h2
    rw [← h2 i, h1, hfU]
    split_ifs
    · exact h3 i
    · rfl

/-- **Weak maximum principle with a transport term** (Gilbarg and Trudinger Theorem 8.1, in
dimension at least two). Let `Ω` be a bounded open set in dimension at least two, `L` a
divergence-form operator with bounded transport term and nonnegative zeroth-order coefficient,
and `U ∈ H¹(Ω)` a weak subsolution, meaning the bilinear pairing of `U` against every
nonnegative `V ∈ H₀¹(Ω)` is nonpositive. If `k ≥ 0` and `(u - k)⁺` is the function coordinate
of some element of `H₀¹(Ω)`, then `u ≤ k` almost everywhere on `Ω`. -/
theorem weak_maximum_principle_transport (hd : 2 ≤ d) (hΩopen : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (Op : FullEllipticOp d)
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
  have := DivForm.FullEllipticOp.weak_maximum_principle_transport
    (DivForm.FullEllipticOp.ofCoord Op) (by simpa using hd) hΩopen hΩb hc
    (DivForm.h1Equiv_symm_mem_W12 hU) (DivForm.FullEllipticOp.form_le_zero_of_coord Op hsub) hk
    (DivForm.exists_fnL_eq_max_of_coord hbd)
  simpa only [DivForm.fnL_h1Equiv_symm] using this

end EllipticPdes.Sobolev
