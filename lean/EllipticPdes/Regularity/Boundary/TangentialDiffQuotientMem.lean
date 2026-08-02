/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Regularity.Boundary.TangentialDiffQuotient

/-!
# Admissibility of the cutoff of a tangential difference quotient

The boundary `H²` estimate (Evans, *Partial Differential Equations* (2nd ed.), §6.3.2,
Theorem 4, *Boundary `H²` regularity*) tests the weak formulation on the half-ball with
`v = -Dₖ^{-h}(ζ² Dₖ^h u)` for a tangential direction `k`. Evans discharges the admissibility
`v ∈ H₀¹(U)` in proof step 3 with the sentence "since `u = 0` along `{xₙ = 0}` in the trace
sense and `ζ ≡ 0` near the curved portion of `∂U`, we see `v ∈ H₀¹(U)`". This file proves
that admissibility in the project's `H₀¹` model, which is the closure of the test-function
graphs rather than the kernel of a trace map, so no trace operator appears anywhere.

The argument is that of `cutoffMul_diffQuotG_mem_H01`
(`EllipticPdes.Regularity.RestrictedDiffQuotientMem`): the composite
`cutoffMulOn Ω ζ ∘ tangDiffQuotG` is a **continuous** linear map and `H₀¹(Ω)` is **closed**,
so membership need only be checked on the spanning set `testGraphSet Ω`, where the diagram
collapses to the graph of `ζ · Dₖ^h φ`. Two things differ from the interior case, both
recorded in `Regularity/Boundary/TangentialDiffQuotient.lean`: the cutoff reaches the flat
boundary, and the direction is tangential, which is what keeps `ζ · Dₖ^h φ` supported inside
the half-ball for **every** step `h`.

## Main results

* `cutoffMulOn_tangDiffQuotG_mem_H01`: the cutoff of the tangential difference quotient of an
  `H₀¹(halfBall d r)` element is again in `H₀¹(halfBall d r)`.
-/

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

/-! ### Extension by zero of a test-function class is the test function -/

/-- Extension by zero of the `L²(Ω)` class of a function supported inside `Ω` recovers the
function itself a.e. on the whole space: off `Ω` the function already vanishes (its
`tsupport` is inside `Ω`), and on `Ω` extension agrees with the class. -/
private lemma extendL2_toLp_ae_eq_halfBall {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩm : MeasurableSet Ω) {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hmem : MemLp ψ 2 (volume.restrict Ω)) (hsupp : tsupport ψ ⊆ Ω) :
    (extendL2 hΩm (hmem.toLp ψ) : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] ψ := by
  filter_upwards [coeFn_extendL2 hΩm (hmem.toLp ψ),
      ae_imp_of_ae_restrict hmem.coeFn_toLp] with x hx himp
  rw [hx]
  by_cases hxΩ : x ∈ Ω
  · rw [Set.indicator_of_mem hxΩ, himp hxΩ]
  · rw [Set.indicator_of_notMem hxΩ,
      image_eq_zero_of_notMem_tsupport (fun hc => hxΩ (hsupp hc))]

/-! ### The difference quotient commutes with the partial derivative -/

/-- **The difference quotient along a fixed vector commutes with the partial derivative.**
`∂ᵢ(D^v φ) = D^v(∂ᵢφ)`: the shift map has derivative the identity, so the shift and the
derivative commute, and dividing by `h` scales the derivative. -/
private lemma partialD_shiftDiffQuotFn {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : Differentiable ℝ φ) (i : Fin n) (v : EuclideanSpace ℝ (Fin n)) (h : ℝ) :
    partialD i (fun x => (φ (x + v) - φ x) / h)
      = fun x => (partialD i φ (x + v) - partialD i φ x) / h := by
  funext x
  have hc : HasFDerivAt (fun y => φ (y + v)) (fderiv ℝ φ (x + v)) x := by
    simpa [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      (hφ (x + v)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const v)
  have hsub := hc.sub (hφ x).hasFDerivAt
  have hval : HasFDerivAt (fun x => (φ (x + v) - φ x) / h)
      ((h⁻¹ : ℝ) • (fderiv ℝ φ (x + v) - fderiv ℝ φ x)) x := by
    have heq : (fun x => (φ (x + v) - φ x) / h)
        = fun y => h⁻¹ * (φ (y + v) - φ y) := by funext y; rw [div_eq_inv_mul]
    rw [heq]; exact hsub.const_mul (h⁻¹ : ℝ)
  simp only [partialD]
  rw [hval.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul]
  ring

/-! ### The discrete graph identity -/

section GraphIdentity

variable {d : ℕ} {r : ℝ} {ζ φ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}

/-- **Discrete graph identity, tangential.** On a test-function graph, the cutoff of the
tangential difference quotient is the graph of the product `ζ · Dₖ^h φ`. Coordinatewise the
restricted difference quotient of `φ`'s classes equals the honest difference quotient of `φ`
(its extension by zero being `φ` itself), and the Leibniz rule
`∂ᵢ(ζ · Dₖ^h φ) = ζ · ∂ᵢ(Dₖ^h φ) + (∂ᵢζ) · Dₖ^h φ` together with `partialD_shiftDiffQuotFn`
matches the successor coordinates. This is the boundary counterpart of
`cutoffMul_diffQuotG_testGraph` (`EllipticPdes.Regularity.RestrictedDiffQuotientMem`). -/
private lemma cutoffMulOn_tangDiffQuotG_testGraph (hζ : IsTestFn (Metric.ball 0 r) ζ)
    (hφ : IsTestFn (halfBall d r) φ) (k : Fin d) (h : ℝ) :
    cutoffMulOn (halfBall d r) hζ (tangDiffQuotG d r k h hφ.testGraph)
      = (isTestFn_tangentialCutoff_diffQuotFn hζ hφ k h).testGraph := by
  have hΩm : MeasurableSet (halfBall d r) := measurableSet_halfBall d r
  have hsh_test : ∀ᵐ x ∂volume,
      (⇑(extendL2 hΩm hφ.testCls) : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
          (x + hshift k.succ h) = φ (x + hshift k.succ h) :=
    (measurePreserving_add_right volume
        (hshift k.succ h)).quasiMeasurePreserving.tendsto_ae.eventually
      (extendL2_toLp_ae_eq_halfBall hΩm hφ.mem_lp hφ.2.2)
  apply PiLp.ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · -- coordinate `0`: `ζ · Dₖ^h φ`
    rw [cutoffMulOn_apply_zero]
    simp only [tangDiffQuotG_apply, IsTestFn.testGraph_zero]
    apply Lp.ext
    filter_upwards [mulCutoff_coeFn hζ (tangDiffQuotD d r k h hφ.testCls),
        coeFn_tangDiffQuotD d r k h hφ.testCls, ae_restrict_of_ae hsh_test,
        (show (⇑hφ.testCls : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
          =ᵐ[volume.restrict (halfBall d r)] φ from hφ.mem_lp.coeFn_toLp),
        (show (⇑(isTestFn_tangentialCutoff_diffQuotFn hζ hφ k h).testCls
            : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
          =ᵐ[volume.restrict (halfBall d r)]
            fun x => ζ x * ((φ (x + hshift k.succ h) - φ x) / h) from
          (isTestFn_tangentialCutoff_diffQuotFn hζ hφ k h).mem_lp.coeFn_toLp)]
      with x hmt hdq hsh htc hpsi
    rw [hmt, hdq, hsh, htc, hpsi]
  · -- coordinate `i+1`: Leibniz `∂ᵢ(ζ · Dₖ^h φ)`
    have hsh_part : ∀ᵐ x ∂volume,
        (⇑(extendL2 hΩm (hφ.partialCls i)) : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
            (x + hshift k.succ h) = partialD i φ (x + hshift k.succ h) :=
      (measurePreserving_add_right volume
          (hshift k.succ h)).quasiMeasurePreserving.tendsto_ae.eventually
        (extendL2_toLp_ae_eq_halfBall hΩm (hφ.memLp_partialD i)
          ((tsupport_partialD_subset i φ).trans hφ.2.2))
    have hpsi_eq : partialD i (fun x => ζ x * ((φ (x + hshift k.succ h) - φ x) / h))
        = fun x => ζ x * ((partialD i φ (x + hshift k.succ h) - partialD i φ x) / h)
          + partialD i ζ x * ((φ (x + hshift k.succ h) - φ x) / h) := by
      rw [partialD_mul (hζ.1.differentiable (by simp))
          ((contDiff_shiftDiffQuotFn hφ.1 (hshift k.succ h) h).differentiable (by simp)) i,
        partialD_shiftDiffQuotFn (hφ.1.differentiable (by simp)) i (hshift k.succ h) h]
    rw [cutoffMulOn_apply_succ]
    simp only [tangDiffQuotG_apply, IsTestFn.testGraph_zero, IsTestFn.testGraph_succ]
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (mulCutoff (halfBall d r) hζ (tangDiffQuotD d r k h
            (hφ.partialCls i)))
          (mulCutoffPartial (halfBall d r) hζ i (tangDiffQuotD d r k h hφ.testCls)),
        mulCutoff_coeFn hζ (tangDiffQuotD d r k h (hφ.partialCls i)),
        mulCutoffPartial_coeFn hζ i (tangDiffQuotD d r k h hφ.testCls),
        coeFn_tangDiffQuotD d r k h (hφ.partialCls i),
        coeFn_tangDiffQuotD d r k h hφ.testCls,
        ae_restrict_of_ae hsh_part, ae_restrict_of_ae hsh_test,
        (show (⇑(hφ.partialCls i) : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
          =ᵐ[volume.restrict (halfBall d r)] partialD i φ from
          (hφ.memLp_partialD i).coeFn_toLp),
        (show (⇑hφ.testCls : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
          =ᵐ[volume.restrict (halfBall d r)] φ from hφ.mem_lp.coeFn_toLp),
        (show (⇑((isTestFn_tangentialCutoff_diffQuotFn hζ hφ k h).partialCls i)
            : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
          =ᵐ[volume.restrict (halfBall d r)]
            partialD i (fun x => ζ x * ((φ (x + hshift k.succ h) - φ x) / h)) from
          ((isTestFn_tangentialCutoff_diffQuotFn hζ hφ k h).memLp_partialD i).coeFn_toLp)]
      with x hadd hmt hmtp hdqp hdqt hshp hsht htcp htct hpsi
    rw [hadd, Pi.add_apply, hmt, hmtp, hdqp, hdqt, hshp, hsht, htcp, htct, hpsi,
      congrFun hpsi_eq x]

/-! ### The crux admissibility -/

/-- **Crux admissibility, tangential.** For `U ∈ H₀¹(halfBall d r)`, the cutoff of its
tangential difference quotient is again in `H₀¹(halfBall d r)`. Since
`cutoffMulOn Ω ζ ∘ tangDiffQuotG` is continuous and sends every test-function graph into
`H₀¹` (by `cutoffMulOn_tangDiffQuotG_testGraph`, as `ζ · Dₖ^h φ` is a test function on the
half-ball for every `φ`), it maps the closure `H₀¹` into the closed set `H₀¹`. This is what
makes `v = -Dₖ^{-h}(ζ² Dₖ^h u)` a legal test element in the boundary `H²` estimate, with no
trace operator and no smallness condition on the step `h` (Evans, *Partial Differential
Equations* (2nd ed.), §6.3.2, Theorem 4, proof step 3). -/
theorem cutoffMulOn_tangDiffQuotG_mem_H01 (hζ : IsTestFn (Metric.ball 0 r) ζ) (k : Fin d)
    (h : ℝ) {U : H1amb (halfBall d r)} (hU : U ∈ H01 (halfBall d r)) :
    cutoffMulOn (halfBall d r) hζ (tangDiffQuotG d r k h U) ∈ H01 (halfBall d r) := by
  have hle : (Submodule.span ℝ (testGraphSet (halfBall d r))).topologicalClosure
      ≤ Submodule.comap
          ((cutoffMulOn (halfBall d r) hζ).comp (tangDiffQuotG d r k h)).toLinearMap
          (H01 (halfBall d r)) := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro _ ⟨φ, hφ, rfl⟩
      change cutoffMulOn (halfBall d r) hζ (tangDiffQuotG d r k h hφ.testGraph)
        ∈ H01 (halfBall d r)
      rw [cutoffMulOn_tangDiffQuotG_testGraph hζ hφ k]
      exact (Submodule.le_topologicalClosure _)
        (Submodule.subset_span ⟨_, isTestFn_tangentialCutoff_diffQuotFn hζ hφ k h, rfl⟩)
    · exact IsClosed.preimage
        ((cutoffMulOn (halfBall d r) hζ).comp (tangDiffQuotG d r k h)).continuous
        (Submodule.isClosed_topologicalClosure _)
  exact Submodule.mem_comap.mp (hle hU)

end GraphIdentity

end EllipticPdes.Regularity
