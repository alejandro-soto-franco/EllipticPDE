/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.Metrizable.ContinuousMap
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Arzelà–Ascoli compactness criterion

Evans's Appendix C.8 states the criterion on `ℝⁿ`. A sequence of real functions that is
uniformly bounded and uniformly equicontinuous has a subsequence that converges uniformly on
compact subsets to a continuous function. This file states it as Evans does and proves it from
Mathlib's Arzelà–Ascoli theorem for `C(ℝⁿ, ℝ)` with the compact-open topology.

## Main declarations

* `EllipticPdes.Analysis.arzela_ascoli`: the criterion for a sequence of functions on
  `EuclideanSpace ℝ (Fin d)`.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), Appendix C.8 (Arzelà–Ascoli
compactness criterion, p. 718).
-/

@[expose] public section

open Filter Topology Set

noncomputable section

namespace EllipticPdes.Analysis

variable {d : ℕ}

/-- **Arzelà–Ascoli compactness criterion.** A sequence `f k` of real functions on `ℝⁿ` with
`|f k x| ≤ M` and uniformly equicontinuous (for each `ε > 0` there is one `δ > 0` with
`|x - y| < δ → |f k x - f k y| < ε` for all `k`) has a subsequence converging uniformly on
compact subsets of `ℝⁿ` to a continuous function. Evans Appendix C.8 (p. 718). -/
theorem arzela_ascoli {f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ} {M : ℝ}
    (hM : ∀ k x, |f k x| ≤ M)
    (heq : ∀ ε > 0, ∃ δ > 0, ∀ k x y, dist x y < δ → |f k x - f k y| < ε) :
    ∃ (φ : ℕ → ℕ) (g : EuclideanSpace ℝ (Fin d) → ℝ), StrictMono φ ∧ Continuous g ∧
      ∀ K, IsCompact K → TendstoUniformlyOn (fun j => f (φ j)) g atTop K := by
  classical
  -- a fixed modulus of continuity
  choose! δ hδ hδ' using heq
  let T : Set (EuclideanSpace ℝ (Fin d) → ℝ) :=
    {h | ∀ x, |h x| ≤ M} ∩ {h | ∀ ε > 0, ∀ x y, dist x y < δ ε → |h x - h y| ≤ ε}
  have hTcont : ∀ h ∈ T, Continuous h := by
    intro h hh
    refine (Metric.uniformContinuous_iff.2 fun ε hε =>
      ⟨δ (ε / 2), hδ _ (half_pos hε), ?_⟩).continuous
    intro x y hxy
    rw [Real.dist_eq]
    have := hh.2 (ε / 2) (half_pos hε) x y hxy
    linarith
  have hTclosed : IsClosed T := by
    refine IsClosed.inter ?_ ?_
    · simp only [ofPred_forall]
      exact isClosed_iInter fun x =>
        isClosed_le ((continuous_apply x).abs) continuous_const
    · simp only [ofPred_forall]
      refine isClosed_iInter fun ε => isClosed_iInter fun _ => isClosed_iInter fun x =>
        isClosed_iInter fun y => isClosed_iInter fun _ => ?_
      exact isClosed_le (((continuous_apply x).sub (continuous_apply y)).abs) continuous_const
  have hTcompact : IsCompact T := by
    refine IsCompact.of_isClosed_subset
      (isCompact_univ_pi fun _ : EuclideanSpace ℝ (Fin d) => isCompact_Icc (a := -M) (b := M))
      hTclosed ?_
    intro h hh x _
    exact abs_le.1 (hh.1 x)
  let S : Set C(EuclideanSpace ℝ (Fin d), ℝ) := {g | (g : EuclideanSpace ℝ (Fin d) → ℝ) ∈ T}
  have himage : ContinuousMap.toFun '' S = T := by
    ext h
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hh
      exact ⟨⟨h, hTcont h hh⟩, hh, rfl⟩
  have hScompact : IsCompact S := by
    refine ArzelaAscoli.isCompact_of_equicontinuous S ?_ ?_
    · rw [himage]
      exact hTcompact
    · refine UniformEquicontinuous.equicontinuous ?_
      rw [Metric.uniformEquicontinuous_iff]
      intro ε hε
      refine ⟨δ (ε / 2), hδ _ (half_pos hε), fun x y hxy g => ?_⟩
      rw [Real.dist_eq]
      have := g.2.2 (ε / 2) (half_pos hε) x y hxy
      linarith
  have hfT : ∀ k, f k ∈ T := by
    intro k
    refine ⟨hM k, fun ε hε x y hxy => (hδ' ε hε k x y hxy).le⟩
  let F : ℕ → C(EuclideanSpace ℝ (Fin d), ℝ) := fun k => ⟨f k, hTcont _ (hfT k)⟩
  obtain ⟨g, hgS, φ, hφ, hlim⟩ := hScompact.tendsto_subseq (x := F) fun k => hfT k
  refine ⟨φ, g, hφ, g.continuous, ?_⟩
  intro K hK
  exact (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 hlim) K hK

end EllipticPdes.Analysis
