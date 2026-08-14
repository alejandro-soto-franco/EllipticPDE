/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Regularity.L2Pairing
import EllipticPdes.Regularity.CutoffGradFormula

/-!
# The commutator of the bilinear form with a cutoff

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2 differentiates the equation
without cutting off, because his interior `H²` theorem asks only `u ∈ H¹(U)`. The interior `H²`
estimate here quantifies its solution over `H₀¹(Ω)`, and `∂_ℓu` carries no boundary condition,
so the induction runs on `ξ·∂_ℓu` and pays a commutator.

This file computes it. Each block of `Op.fullBilin` is expanded on the cut-off element, one
entry at a time, and every term either matches the differentiated equation tested against `ξv`
or becomes an `L²` pairing against `v`.

## The principal entry

`∂ᵢ(ξ·∂_ℓu)` is `(∂ᵢξ)(∂_ℓu) + ξ(∂ᵢ∂_ℓu)`, so the entry splits in two.

* The term carrying `ξ` keeps its derivative on the solution. Writing `ξ∂ⱼv = ∂ⱼ(ξv) - (∂ⱼξ)v`
  turns it into the differentiated equation tested against `ξv`, plus a pairing.
* The term carrying `∂ᵢξ` keeps its derivative on the test function, and has to be integrated by
  parts. It is admissible because `∂ᵢξ` is supported in `W`, which is
  `EllipticPdes.Regularity.setIntegral_mul_mulTest_partialD`.

Nothing here is specific to the operator: the coefficient enters as a bounded measurable weight
and the second derivative of the solution enters as a weak derivative on `W`. The entries are
supplied as classes with their defining almost-everywhere descriptions, so the caller names its
own and no product is constructed twice.

## Main declarations

* `mul_eq_self_of_eqOn_one`: a cutoff that is one where a weight lives is invisible.
* `setIntegral_principal_entry`: one entry of the principal block, expanded.
* `setIntegral_lower_entry`: one entry of a block with no derivative on the test function.
-/

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### The open collar the identifications run on -/

/-- **The tower carries an open collar around the middle cutoff.** There is an open `N` with
`tsupport ξ ⊆ N ⊆ tsupport θ` on which `θ` is identically `1`.

Every identification the induction step makes holds only after a cutoff, and `N` is where the
cutoff is invisible. Running the differentiated equation on `N` rather than on the compact
`tsupport θ` is what lets the inductive hypothesis's own family supply every derivative: the
first derivatives it names agree with the ambient element's gradient coordinates almost
everywhere on `N`, which is enough for both to be weak derivatives of one class there. -/
theorem CutoffTower.exists_isOpen_collar {Ω V : Set (EuclideanSpace ℝ (Fin d))}
    (T : CutoffTower Ω V) :
    ∃ N : Set (EuclideanSpace ℝ (Fin d)), IsOpen N ∧ tsupport T.ξ ⊆ N ∧ N ⊆ tsupport T.θ ∧
      Set.EqOn T.θ 1 N := by
  obtain ⟨N, hNo, hξN, hNθ⟩ := mem_nhdsSet_iff_exists.1 T.hθ_one
  refine ⟨N, hNo, hξN, ?_, fun x hx => hNθ hx⟩
  intro x hx
  refine subset_tsupport T.θ ?_
  rw [Function.mem_support, hNθ hx]
  exact one_ne_zero

/-- **A cutoff that is one where a weight lives is invisible against it.** Every identification
the induction step makes holds only after a cutoff, and every weight it pairs against is
supported where that cutoff is identically one, so the cutoff never reaches the conclusion. -/
theorem mul_eq_self_of_eqOn_one {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    {S : Set (EuclideanSpace ℝ (Fin d))} (hχ : Set.EqOn χ 1 S)
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : tsupport ψ ⊆ S) (x : EuclideanSpace ℝ (Fin d)) :
    χ x * ψ x = ψ x := by
  by_cases hx : x ∈ tsupport ψ
  · rw [hχ (hψ hx)]
    simp
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

/-- **One entry of the principal block of the cut-off element.** With `Uamb` an ambient element
whose `i`-th gradient coordinate is `(∂ᵢξ)·p + ξ·(∂ᵢp)`, the entry
`∫_Ω a·(∂ᵢ(ξp))·∂ⱼv` splits into the differentiated equation's principal term tested against
`ξv`, a pairing coming from `ξ∂ⱼv = ∂ⱼ(ξv) - (∂ⱼξ)v`, and the integration by parts of the term
in which the derivative landed on the cutoff.

`Aip` is the class of `a·p`, `dAip` its weak `j`-derivative on `W`, and `Aig` the class of
`a·∂ᵢp`. Only `dAip` needs the coefficient to be differentiable, and it enters as a hypothesis
rather than as a construction, so this statement is free of every coefficient bundle. -/
theorem setIntegral_principal_entry {Ω W : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) (hWm : MeasurableSet W)
    {ξ : EuclideanSpace ℝ (Fin d) → ℝ} (hξW : IsTestFn W ξ)
    (a : EuclideanSpace ℝ (Fin d) → ℝ) {Uamb : H1amb Ω} {p Dgi : L2D W} (i j : Fin d)
    (hgrad : extendL2 hΩm (Uamb i.succ)
      = extendL2 hWm (mulTest (isTestFn_partialD hξW i) p + mulTest hξW Dgi))
    (Aip : L2D W) (hAip : Aip =ᵐ[volume.restrict W] fun x => a x * (p x : ℝ))
    (dAip : L2D W) (hdAip : HasWeakDerivOn W j Aip dAip)
    (Aig : L2D W) (hAig : Aig =ᵐ[volume.restrict W] fun x => a x * (Dgi x : ℝ))
    {v : EuclideanSpace ℝ (Fin d) → ℝ} (hvc : ContDiff ℝ (⊤ : ℕ∞) v) :
    (∫ x in Ω, a x * ((Uamb i.succ) x : ℝ) * partialD j v x)
      = (∫ x in W, (Aig x : ℝ) * partialD j (fun y => ξ y * v y) x)
        - (∫ x in W, (Aig x : ℝ) * (partialD j ξ x * v x))
        - ∫ x in W, (partialD j (partialD i ξ) x * (Aip x : ℝ)
            + partialD i ξ x * (dAip x : ℝ)) * v x := by
  -- The entry, moved down to `W` through the gradient formula.
  have e0 : (∫ x in Ω, a x * ((Uamb i.succ) x : ℝ) * partialD j v x)
      = ∫ x in W, a x
          * ((mulTest (isTestFn_partialD hξW i) p + mulTest hξW Dgi) x : ℝ) * partialD j v x := by
    rw [← integral_extendL2_mul_mul hΩm (Uamb i.succ) a (partialD j v), hgrad,
      integral_extendL2_mul_mul hWm _ a (partialD j v)]
  -- The two summands of the gradient, each with its own cutoff.
  have hQ : (fun x => a x
        * ((mulTest (isTestFn_partialD hξW i) p + mulTest hξW Dgi) x : ℝ) * partialD j v x)
      =ᵐ[volume.restrict W] fun x => (Aip x : ℝ) * (partialD i ξ x * partialD j v x)
        + (Aig x : ℝ) * (ξ x * partialD j v x) := by
    filter_upwards [Lp.coeFn_add (mulTest (isTestFn_partialD hξW i) p) (mulTest hξW Dgi),
      mulTest_coeFn (isTestFn_partialD hξW i) p, mulTest_coeFn hξW Dgi, hAip, hAig]
      with x h1 h2 h3 h4 h5
    rw [h1, Pi.add_apply, h2, h3, h4, h5]
    ring
  have e1 : (∫ x in W, a x
        * ((mulTest (isTestFn_partialD hξW i) p + mulTest hξW Dgi) x : ℝ) * partialD j v x)
      = (∫ x in W, (Aip x : ℝ) * (partialD i ξ x * partialD j v x))
        + ∫ x in W, (Aig x : ℝ) * (ξ x * partialD j v x) := by
    rw [integral_congr_ae hQ]
    exact integral_add
      (integrable_mul_testFn Aip ((contDiff_partialD hξW.1 i).mul (contDiff_partialD hvc j))
        (hξW.hasCompactSupport_partialD i).mul_right)
      (integrable_mul_testFn Aig (hξW.1.mul (contDiff_partialD hvc j)) hξW.2.1.mul_right)
  rw [e0, e1, setIntegral_mul_mulTest_partialD (isTestFn_partialD hξW i) hdAip hvc,
    setIntegral_mul_cutoff_partialD_split Aig hξW.1 hξW.2.1 hvc j]
  ring

/-- **One entry of a block with no derivative on the test function.** The transport and
zeroth-order blocks need no integration by parts: the entry is already an `L²` pairing, and
only the gradient formula and the move down to `W` are used. -/
theorem setIntegral_lower_entry {Ω W : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) (hWm : MeasurableSet W) (F : L2D Ω) (G : L2D W)
    (hFG : extendL2 hΩm F = extendL2 hWm G) (a : EuclideanSpace ℝ (Fin d) → ℝ)
    (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    (∫ x in Ω, a x * (F x : ℝ) * v x) = ∫ x in W, a x * (G x : ℝ) * v x := by
  rw [← integral_extendL2_mul_mul hΩm F a v, hFG, integral_extendL2_mul_mul hWm G a v]

end EllipticPdes.Regularity
