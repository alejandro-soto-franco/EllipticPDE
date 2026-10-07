/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Compactness.Compact

/-!
# Smooth cutoffs on a finite-dimensional space

A compact set `K` inside an open set `U` of a finite-dimensional real normed space has a smooth
function equal to one on `K`, with compact support inside `U`, and with values in `[0, 1]`.
-/

@[expose] public section

open Set

noncomputable section

namespace EllipticPdes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Cutting between a compact set and an open one.** A smooth function with values in `[0, 1]`,
equal to one on the compact set and compactly supported inside the open one. -/
theorem exists_contDiff_one_on_compact {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ y ∈ K, χ y = 1) ∧ ∀ y, χ y ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨f, hf, hfI, hsupp, h1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    (isOpen_interior (s := L)) hK.isClosed hKL
  have hts : tsupport f ⊆ L := by
    rw [tsupport, hsupp]
    exact closure_minimal interior_subset hLc.isClosed
  exact ⟨f, hf, hLc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hLU,
    fun y hy => (h1 y).1 hy, fun y => hfI ⟨y, rfl⟩⟩

end EllipticPdes
