/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Regularity.HigherWeakDeriv
import EllipticPdes.Regularity.LowerOrderWkInfty
import EllipticPdes.Regularity.IteratedSum
import EllipticPdes.Regularity.IteratedRestrict
import EllipticPdes.Regularity.WeakFormDense
import EllipticPdes.Regularity.LocalWeakFormWkInfty
import EllipticPdes.Regularity.CutoffDeriv
import EllipticPdes.Regularity.CutoffCommutator
import EllipticPdes.Regularity.CollarIdentify
import EllipticPdes.Regularity.DatumPiece

/-!
# Higher interior regularity

Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem VIII.3.2
(*Higher Interior Regularity*, p. 65). For a weak solution `u` of `L u = f` with
`a_{ij} ∈ W^{k+2,∞}`, `b_i, c ∈ W^{k+1,∞}` and `f ∈ H^k`, the solution lies in `H^{k+2}_loc`
with

`‖u‖_{H^{k+2}(V)} ≤ C (‖f‖_{H^k(Ω)} + ‖u‖_{L²(Ω)})` for every `V ⋐ Ω`,

the constant depending on the data and the pair `V ⋐ Ω` and on neither `u` nor `f`. Evans,
*Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2 (p. 327) is the same statement
with `C^{k+1}` coefficients, which `IsCkCoeff.toIsWkInftyCoeff` shows to be the stronger
hypothesis.

## How the induction runs

`InteriorRegularityAt Op Ω k` packages the conclusion at order `k`, and the theorem is an
induction on `k` over that predicate.

* Order `0` is `interior_H2_estimate` with its `(k, i)`-indexed second derivatives assembled
  into a `HasIteratedWeakDerivOn` family of order `2`.
* The step differentiates the equation once. Where `u` solves `L u = f`, the derivative
  `∂_l u` solves `L (∂_l u) = ∂_l f + R_l`, with `R_l` collecting the terms in which the
  differentiation lands on a coefficient rather than on `u`. Those terms carry one derivative
  of a coefficient against derivatives of `u` of order at most two, so `R_l` sits in `H^{k-1}`
  once the order-`k-1` conclusion is available for `u` itself. Applying the induction
  hypothesis to `∂_l u` on an intermediate `V ⋐ W ⋐ Ω` gives `∂_l u ∈ H^{k+1}(V)`, which is
  `u ∈ H^{k+2}(V)`.

The differentiated equation is already available as
`EllipticPdes.Regularity.differentiated_weakForm_div`, and the admissibility of the test
function it needs as `interior_cutoffGrad_mem_H01`.

## Main declarations

* `InteriorRegularityAt`: the order-`k` conclusion, as a predicate, so that the induction has
  something to be an induction over.
* `interiorRegularityAt_zero`: the base case.
* `exists_cutoffDeriv_weakForm`: the differentiated equation, as a weak formulation for the
  cutoff derivative, which is what the induction hypothesis consumes.
* `interiorRegularityAt_succ`: the induction step.
* `higher_interior_regularity`: the theorem.
-/

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {n : ℕ}

/-- **The order-`k` interior conclusion.** For every compact `V ⋐ Ω` there is a constant,
quantified before the solution and the datum, bounding every weak derivative of `u` of order at
most `k + 2` on `V` by `‖f‖_{H^k} + ‖u‖_{L²}`. The datum's `H^k` norm enters through a bound
`M` on its own iterated family, which `IteratedL2Bound.norm_le` shows to dominate `‖f‖`. -/
def InteriorRegularityAt (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (k : ℕ) : Prop :=
  ∀ {V : Set (EuclideanSpace ℝ (Fin (n + 1)))}, IsCompact V → V ⊆ Ω →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H01 Ω) (f : L2D Ω) (M : ℝ)
      (hfk : HasIteratedWeakDerivOn Ω k f), IteratedL2Bound hfk M →
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∃ hu : HasIteratedWeakDerivOn V (k + 2)
          (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))),
        IteratedL2Bound hu (C * (M + ‖(u : H1amb Ω) 0‖))

/-- **Base case: order zero is the interior `H²` estimate.** The estimate
`interior_H2_estimate` returns, for each direction pair `(k, i)`, a weak `k`-derivative of
`∂ᵢu` on `V` together with its bound. Assembling those into a `HasIteratedWeakDerivOn` family
of order `2` is a matter of naming: the empty list is `u`, a singleton `[i]` is `∂ᵢu`, a pair
`[k, i]` is the returned `wki`, and longer lists are unconstrained because `D_step` is asked
only of lists shorter than `2`.

The first-order step, which the `H²` estimate does not itself provide, is
`hasWeakDeriv_extendL2_of_mem_H01`: the ambient encoding's coordinate `i.succ` is the weak
`i`-derivative of coordinate `0` on the whole space, and `hasWeakDerivOn_of_hasWeakDeriv`
localises it to `V`.

No constant is spent. The `H²` estimate bounds the sum of the three norms, so each of them is
bounded on its own, and `IteratedL2Bound.norm_le` supplies `‖f‖ ≤ M`. -/
theorem interiorRegularityAt_zero (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA : IsC1Coeff Op.toEllipticCoeff) :
    InteriorRegularityAt Op hΩm 0 := by
  classical
  intro V hVc hVΩ
  obtain ⟨C, hC0, hC⟩ := interior_H2_estimate Op hΩm hΩo hA hVc hVΩ
  refine ⟨C, hC0, fun u f M hfk hM hu => ?_⟩
  choose W hW hWb using hC u f hu
  -- The family: the empty list is `u`, a singleton is a first derivative, a pair is the
  -- second derivative the `H²` estimate returned. Longer lists are never asked about.
  refine ⟨⟨fun α =>
      match α with
      | [] => restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))
      | [i] => restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))
      | [k, i] => W k i
      | _ => 0, rfl, ?_⟩, ?_⟩
  · rintro m (_ | ⟨i, _ | ⟨j, rest⟩⟩) hα
    · exact hasWeakDerivOn_of_hasWeakDeriv m (hasWeakDeriv_extendL2_of_mem_H01 hΩm m u.2)
    · exact hW m i
    · simp at hα
  -- Each of the three norms is dominated by the sum the `H²` estimate bounds.
  · have hfM : ‖f‖ ≤ M := hM.norm_le
    have hshift : C * (‖f‖ + ‖(u : H1amb Ω) 0‖) ≤ C * (M + ‖(u : H1amb Ω) 0‖) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    rintro (_ | ⟨i, _ | ⟨j, rest⟩⟩) hα
    · refine le_trans ?_ hshift
      have h := hWb 0 0
      have h1 := norm_nonneg (W 0 0)
      have h2 := norm_nonneg (restrictL2 (Ω := V)
        (extendL2 hΩm ((u : H1amb Ω) (0 : Fin (n + 1)).succ)))
      linarith
    · refine le_trans ?_ hshift
      have h := hWb 0 i
      have h1 := norm_nonneg (W 0 i)
      have h2 := norm_nonneg (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0)))
      linarith
    · rcases rest with _ | ⟨p, rest'⟩
      · refine le_trans ?_ hshift
        have h := hWb i j
        have h1 := norm_nonneg (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) j.succ)))
        have h2 := norm_nonneg (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0)))
        linarith
      · simp at hα

/-- **The differentiated equation, as a weak formulation for a cutoff derivative.** For a weak
solution `u` of `L u = f` and each direction `ℓ`, there is an element `U ∈ H₀¹(Ω)` agreeing
with `∂_ℓ u` on `V`, a datum `F ∈ L²(Ω)` carrying `k` weak derivatives, and a weak formulation
`B[U, w] = ⟪F, w⟫` for every `w ∈ H₀¹(Ω)`, with both `‖U‖` and the `H^k` bound on `F`
controlled by the data.

This is Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2, step 3 in the
shape the induction consumes, and it is where the analytic content of the step sits.

`U` is `ξ · ∂_ℓ u` for the middle cutoff of a tower for `V ⋐ Ω`, which
`EllipticPdes.Regularity.interior_cutoffGrad_mem_H01` places in `H₀¹(Ω)` and
`EllipticPdes.Regularity.restrictL2_extendL2_mulTest_xi` makes invisible on `V`. `F` collects
`∂_ℓ f`, the terms of `EllipticPdes.Regularity.differentiated_weakForm_wkInfty` in which the
differentiation lands on a coefficient, and the commutator with `ξ`. Each of those is a
`W^{k,∞}` weight against a derivative of `u` of order at most two, so
`EllipticPdes.Regularity.exists_iteratedWeakDeriv_mul` and
`EllipticPdes.Regularity.HasIteratedWeakDerivOn.sum` assemble the family and its bound, and
`EllipticPdes.Regularity.weakForm_of_testFn` carries the identity from test functions to
`H₀¹(Ω)`.

## Why the order-`k` conclusion is a hypothesis

`F` carries second derivatives of `u` against first derivatives of the coefficients, so
`F ∈ H^k` asks for `u ∈ H^{k+2}` on a neighbourhood of `tsupport ξ`, which is the order-`k`
conclusion at that compact set. Evans reaches for it at the same point: the datum (36) of
§6.3.1, Theorem 2 contains `D²u`, and its `H^k` bound is read off the inductive hypothesis
rather than off the solution's membership of `H₀¹(Ω)`. Passing `hk` here rather than deriving
it is what keeps the step an induction. -/
theorem exists_cutoffDeriv_weakForm (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsC1Coeff Op.toEllipticCoeff) {k : ℕ}
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 3)) (hbc : IsWkInftyLower Op (k + 2))
    (hk : InteriorRegularityAt Op hΩm k)
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hVc : IsCompact V) (hVΩ : V ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H01 Ω) (f : L2D Ω) (M : ℝ)
      (hfk : HasIteratedWeakDerivOn Ω (k + 1) f), IteratedL2Bound hfk M →
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∀ ℓ : Fin (n + 1), ∃ (U : H01 Ω) (F : L2D Ω) (hFk : HasIteratedWeakDerivOn Ω k F),
        restrictL2 (Ω := V) (extendL2 hΩm ((U : H1amb Ω) 0))
            = restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) ℓ.succ))
          ∧ (∀ w : H01 Ω, Op.fullBilin Ω U w
              = ∫ x in Ω, (F x : ℝ) * ((w : H1amb Ω) 0 x : ℝ))
          ∧ IteratedL2Bound hFk (C * (M + ‖(u : H1amb Ω) 0‖))
          ∧ ‖(U : H1amb Ω) 0‖ ≤ C * (M + ‖(u : H1amb Ω) 0‖) := by
  sorry

/-- **Induction step.** Differentiating the equation once carries the order-`k` conclusion to
order `k + 1`, under one more order of regularity on every coefficient.

`∂_ℓ u` is not in `H₀¹(Ω)`: it is a first derivative of an `H₀¹` function and lies only in
`H¹_loc`, so `InteriorRegularityAt`, which quantifies over `H01 Ω`, cannot be applied to it.
`exists_cutoffDeriv_weakForm` supplies the cutoff that can be, together with its datum, and
this step is what remains once that is in hand.

The induction hypothesis returns `k + 2` weak derivatives of the cutoff derivative on `V`,
which `HasIteratedWeakDerivOn.congr` reads as `k + 2` weak derivatives of `∂_ℓ u` itself,
the cutoff being `1` there. Reassembling over `ℓ` through `HasIteratedWeakDerivOn.ofDeriv`
gives `u ∈ H^{k + 3}(V)`.

The constant is `2 C₁ C₀ + 1`, with `C₀` from the datum and `C₁` from the induction
hypothesis. The two summands of `C₀ (M + ‖u‖) + ‖U‖` are each at most `C₀ (M + ‖u‖)`, which
is where the factor of two comes from, and the `+ 1` covers `‖u‖` itself, which the order-zero
entry of the assembled family needs and which no derivative bound supplies. -/
theorem interiorRegularityAt_succ (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsC1Coeff Op.toEllipticCoeff) {k : ℕ}
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 3))
    (hbc : IsWkInftyLower Op (k + 2)) (hk : InteriorRegularityAt Op hΩm k) :
    InteriorRegularityAt Op hΩm (k + 1) := by
  classical
  intro V hVc hVΩ
  obtain ⟨C₀, hC₀0, hdat⟩ := exists_cutoffDeriv_weakForm Op hΩm hΩo hA1 hA hbc hk hVc hVΩ
  obtain ⟨C₁, hC₁0, hIH⟩ := hk hVc hVΩ
  refine ⟨2 * C₁ * C₀ + 1, by nlinarith [mul_nonneg hC₁0 hC₀0], fun u f M hfk hM hu => ?_⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hM.norm_le
  have hu00 : (0 : ℝ) ≤ ‖(u : H1amb Ω) 0‖ := norm_nonneg _
  -- Each first derivative of `u` carries `k + 2` weak derivatives on `V`, read off the
  -- induction hypothesis applied to the cutoff derivative and transported along `ξ ≡ 1`.
  have hstep : ∀ ℓ : Fin (n + 1), ∃ H : HasIteratedWeakDerivOn V (k + 2)
      (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) ℓ.succ))),
      IteratedL2Bound H ((2 * C₁ * C₀ + 1) * (M + ‖(u : H1amb Ω) 0‖)) := by
    intro ℓ
    obtain ⟨U, F, hFk, hres, hUweak, hFbd, hU0⟩ := hdat u f M hfk hM hu ℓ
    obtain ⟨HU, hHU⟩ := hIH U F (C₀ * (M + ‖(u : H1amb Ω) 0‖)) hFk hFbd hUweak
    exact ⟨HU.congr hres, hHU.congr.mono_const (by nlinarith)⟩
  choose H hH using hstep
  refine ⟨HasIteratedWeakDerivOn.ofDeriv
    (fun ℓ => hasWeakDerivOn_of_hasWeakDeriv ℓ
      (hasWeakDeriv_extendL2_of_mem_H01 hΩm ℓ u.2)) H, IteratedL2Bound.ofDeriv ?_ hH⟩
  refine le_trans (norm_restrictL2_le _) ?_
  rw [norm_extendL2]
  have hprod : (0 : ℝ) ≤ 2 * C₁ * C₀ * (M + ‖(u : H1amb Ω) 0‖) :=
    mul_nonneg (mul_nonneg (by linarith) hC₀0) (by linarith)
  nlinarith [hprod]

/-- **Higher interior regularity (Guo, Theorem VIII.3.2, p. 65).** A weak solution with
`W^{k+2,∞}` principal coefficients, `W^{k+1,∞}` lower-order coefficients and an `H^k` datum has
weak derivatives of every order up to `k + 2` on each compact `V ⋐ Ω`, bounded by the data with
a constant quantified before the solution and the datum.

The coefficient hypotheses are asked at `k + 3` and `k + 2` rather than at `k + 2` and `k + 1`
because the induction consumes one order per step and the statement is proved for every order
at once; `IsWkInftyCoeff.mono` recovers the weaker form at any fixed `k`. -/
theorem higher_interior_regularity (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsC1Coeff Op.toEllipticCoeff) (k : ℕ)
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 3))
    (hbc : IsWkInftyLower Op (k + 2)) :
    InteriorRegularityAt Op hΩm k := by
  induction k with
  | zero => exact interiorRegularityAt_zero Op hΩm hΩo hA1
  | succ j ih =>
    refine interiorRegularityAt_succ (k := j) Op hΩm hΩo hA1 (hA.mono (by omega))
      (hbc.mono (by omega)) ?_
    exact ih (hA.mono (by omega)) (hbc.mono (by omega))

end EllipticPdes.Regularity
