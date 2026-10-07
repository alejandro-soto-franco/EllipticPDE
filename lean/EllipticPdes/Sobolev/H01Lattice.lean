/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.ChainRule
public import EllipticPdes.Embedding.WeakGradient
public import EllipticPdes.Existence.DivFormMaximum
public import EllipticPdes.Existence.WeakMaximum
public import EllipticPdes.Form.DivFormEuclidean
public import EllipticPdes.Sobolev.GraphLattice

/-!
# Truncation in `H₀¹`, in coordinates

`H₀¹(Ω)` is closed under the truncation `u ↦ (u - k)⁺` for `k ≥ 0`. The theorem is
`EllipticPdes.H1Graph.exists_mem_H01_posPart_sub_const`, over a finite-dimensional inner product
space, and the compact-support criterion it rests on is
`EllipticPdes.H1Graph.mem_H01_of_hasCompactSupport`. The statements here are their transport
along `EllipticPdes.H1Graph.h1Equiv`, which identifies the coordinate space `H1amb Ω` with the
graph space.

This is the step the proof of the weak maximum principle takes for granted when it tests
against `(u - k)⁺`. With it, the principle applies to every subsolution in `H₀¹(Ω)`, and the
uniqueness of the generalised Dirichlet problem follows by applying it to the solution and to
its negative.

## Main declarations

* `EllipticPdes.Sobolev.mem_H01_of_hasCompactSupport`: a compactly supported class with `L²`
  weak gradient lies in `H₀¹`.
* `EllipticPdes.Sobolev.exists_mem_H01_posPart_sub_const`: `H₀¹` is closed under
  `u ↦ (u - k)⁺` for `k ≥ 0`.
* `EllipticPdes.Sobolev.weak_maximum_principle_H01`: a subsolution in `H₀¹` is nonpositive.
* `EllipticPdes.Sobolev.eq_zero_of_weakSolution_H01`: uniqueness of the generalised Dirichlet
  problem.

## References

D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§8.1 Theorem 8.1 and Corollary 8.2 (pp. 179–180);
L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.3.1 Theorem 1 (p. 264).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal Convolution RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

open EllipticPdes.Embedding

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### Transport of the graph-space truncation -/

/-- The vector-valued gradient of a coordinate family of `L²` functions is in `L²`. -/
lemma memLp_toLp_of_forall {h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hh : ∀ k, MemLp (h k) 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    MemLp (fun x => (WithLp.toLp 2 fun k => h k x : EuclideanSpace ℝ (Fin d))) 2 volume := by
  refine (Lp.memLp (H1Graph.piLpLpₗ (volume : Measure (EuclideanSpace ℝ (Fin d)))
    (WithLp.toLp 2 fun k => (hh k).toLp (h k)))).ae_eq ?_
  filter_upwards [H1Graph.coeFn_piLpLpₗ (volume : Measure (EuclideanSpace ℝ (Fin d)))
    (WithLp.toLp 2 fun k => (hh k).toLp (h k)),
    ae_all_iff.2 fun k => (hh k).coeFn_toLp] with x hx hx'
  rw [hx]
  exact congrArg (WithLp.toLp 2) (funext hx')

/-- **Compactly supported classes with `L²` weak gradient lie in `H₀¹`.** A class on the whole
space with an `L²` weak gradient whose support is a compact subset of the open set `Ω` is, with
its gradient, the `H¹` limit of its mollifications, which are test functions of `Ω`. -/
theorem mem_H01_of_hasCompactSupport (hΩ : IsOpen Ω) {w : EuclideanSpace ℝ (Fin d) → ℝ}
    {h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hwg : HasWeakGradOn univ w h)
    (hw : MemLp w 2 volume) (hh : ∀ k, MemLp (h k) 2 volume) (hwcs : HasCompactSupport w)
    (hwΩ : tsupport w ⊆ Ω) :
    WithLp.toLp 2 (Fin.cons ((hw.mono_measure Measure.restrict_le_self).toLp w)
      fun k => ((hh k).mono_measure Measure.restrict_le_self).toLp (h k)) ∈ H01 Ω := by
  have hgm := memLp_toLp_of_forall hh
  have hwg' : HasWeakFDerivOn ⊤ w
      (fun x => innerSL ℝ (WithLp.toLp 2 fun k => h k x : EuclideanSpace ℝ (Fin d))) volume := by
    have := (hasWeakGradOn_iff_hasWeakFDerivOn isOpen_univ
      ((hw.locallyIntegrable one_le_two).locallyIntegrableOn _)
      (fun k => ((hh k).locallyIntegrable one_le_two).locallyIntegrableOn _)).1 hwg
    convert this using 1
    funext x
    rw [gradCLM_eq_toDual]
    rfl
  have key := H1Graph.mem_H01_of_hasCompactSupport hΩ hwg' hw hgm hwcs hwΩ
  set X := H1Graph.mk ((hw.mono_measure Measure.restrict_le_self).toLp w)
    ((hgm.mono_measure Measure.restrict_le_self).toLp _) with hX
  have hmem := Submodule.mem_map_of_mem (f := (H1Graph.h1Equiv Ω).toLinearEquiv.toLinearMap) key
  rw [H1Graph.map_h1Equiv_H01] at hmem
  convert hmem using 1
  refine (PiLp.ext fun j => ?_)
  induction j using Fin.cases with
  | zero => simp [hX]
  | succ i =>
    refine Lp.ext ?_
    simp only [Fin.cons_succ]
    have e : (H1Graph.h1Equiv Ω X) i.succ =
        (EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).compLp
          (H1Graph.gradL X) := H1Graph.h1Equiv_apply_succ Ω X i
    refine (((hh i).mono_measure Measure.restrict_le_self).coeFn_toLp).trans ?_
    change _ =ᵐ[volume.restrict Ω] ⇑((H1Graph.h1Equiv Ω X) i.succ)
    rw [e]
    filter_upwards [ContinuousLinearMap.coeFn_compLp
      (EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (H1Graph.gradL X),
      (hgm.mono_measure Measure.restrict_le_self).coeFn_toLp] with x h1 h2
    rw [h1]
    simp only [hX, H1Graph.gradL_mk] at h2 ⊢
    rw [h2]
    rfl

/-- **Truncation in `H₀¹`.** For `V ∈ H₀¹(Ω)` and `k ≥ 0` there is `W ∈ H₀¹(Ω)` whose function
coordinate is `(v - k)⁺` and whose gradient coordinates are those of `V` on `{v > k}` and zero
elsewhere. -/
theorem exists_mem_H01_posPart_sub_const (hΩ : IsOpen Ω) {V : H1amb Ω} (hV : V ∈ H01 Ω)
    {k : ℝ} (hk : 0 ≤ k) :
    ∃ W ∈ H01 Ω,
      ((W 0 : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] (fun x => max ((V 0 x : ℝ) - k) 0) ∧
      ∀ i : Fin d, ((W i.succ : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] fun x => if k < (V 0 x : ℝ) then (V i.succ x : ℝ) else 0 := by
  obtain ⟨W', hW', hf, hg⟩ := H1Graph.exists_mem_H01_posPart_sub_const hΩ
    (H1Graph.h01Equiv Ω ⟨V, hV⟩).2 hk
  set W : H01 Ω := (H1Graph.h01Equiv Ω).symm ⟨W', hW'⟩ with hW
  have hWW : (H1Graph.h01Equiv Ω W : H1Graph volume Ω) = W' := by simp [hW]
  have hf' := DivForm.ae_fnL_h01Equiv Ω ⟨V, hV⟩
  have hgV := DivForm.ae_gradL_h01Equiv Ω ⟨V, hV⟩
  have hgW := DivForm.ae_gradL_h01Equiv Ω W
  rw [hWW] at hgW
  refine ⟨W, W.2, ?_, fun i => ?_⟩
  · filter_upwards [hf, hf', DivForm.ae_fnL_h01Equiv Ω W] with x h1 h2 h3
    rw [hWW] at h3
    rw [← h3, h1, h2]
  · filter_upwards [hg, hf', hgV, hgW] with x h1 h2 h3 h4
    rw [← h4 i, h1, h2, ← h3 i]
    split_ifs <;> rfl

/-! ### The maximum principle in `H₀¹` -/

/-- **Weak maximum principle for a subsolution in `H₀¹`.** With the boundary inequality
`u ≤ 0` supplied by membership of the subsolution in `H₀¹(Ω)`, a subsolution of a
transport-free operator with nonnegative zeroth-order coefficient on a bounded open set is
nonpositive almost everywhere. -/
theorem weak_maximum_principle_H01 (hd : 0 < d) (hΩopen : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (Op : FullEllipticOp d) (hb : ∀ x i, Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), 0 ≤ Op.c x) (U : H01 Ω)
    (hsub : ∀ V : H01 Ω, (∀ᵐ x ∂(volume.restrict Ω), 0 ≤ ((V : H1amb Ω) 0 x : ℝ)) →
      Op.fullBilin Ω U V ≤ 0) :
    ∀ᵐ x ∂(volume.restrict Ω), ((U : H1amb Ω) 0 x : ℝ) ≤ 0 := by
  obtain ⟨W, hW, hW0, -⟩ := exists_mem_H01_posPart_sub_const hΩopen U.2 (le_refl (0 : ℝ))
  refine weak_maximum_principle hd hΩopen hΩb Op hb hc (H01_le_W12 Ω U.2) (fun V hV => ?_)
    (le_refl (0 : ℝ))
    ⟨⟨W, hW⟩, ?_⟩
  · have := hsub V hV
    rwa [FullEllipticOp.fullBilin_apply, EllipticCoeff.bilin_apply, FullEllipticOp.lowerBilin_apply,
      ← add_assoc] at this
  · filter_upwards [hW0] with x hx
    simpa only [sub_zero] using hx

/-- **Uniqueness of the generalised Dirichlet problem** (Gilbarg and Trudinger Corollary 8.2,
transport-free case). A weak solution in `H₀¹(Ω)` of the homogeneous equation for a
transport-free operator with nonnegative zeroth-order coefficient on a bounded open set is
zero. -/
theorem eq_zero_of_weakSolution_H01 (hd : 0 < d) (hΩopen : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (Op : FullEllipticOp d) (hb : ∀ x i, Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), 0 ≤ Op.c x) (U : H01 Ω)
    (hsol : ∀ V : H01 Ω, Op.fullBilin Ω U V = 0) : U = 0 := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.1 hd
  refine (H1Graph.h01Equiv Ω).injective ?_
  rw [map_zero]
  refine DivForm.FullEllipticOp.eq_zero_of_weakSolution_H01 (DivForm.FullEllipticOp.ofCoord Op)
    hΩopen hΩb (fun x => by ext i; simp [DivForm.FullEllipticOp.ofCoord, hb]) hc
    (H1Graph.h01Equiv Ω U) fun V => ?_
  have := DivForm.FullEllipticOp.form_h01Equiv Op Ω U ((H1Graph.h01Equiv Ω).symm V)
  rw [LinearIsometryEquiv.apply_symm_apply] at this
  exact this.trans (hsol _)

end EllipticPdes.Sobolev
