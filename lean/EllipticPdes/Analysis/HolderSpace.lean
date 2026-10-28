/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.Topology.MetricSpace.Holder
public import EllipticPdes.Analysis.FunctionSpaces

/-!
# Hölder spaces

Evans defines, for `0 < γ ≤ 1`, the supremum norm `‖u‖_{C(Ū)}`, the `γ`-th Hölder seminorm
`[u]_{C^{0,γ}(Ū)}` and norm, and the Hölder space `C^{k,γ}(Ū)` of the functions in `C^k(Ū)` with
finite norm `Σ_{|α|≤k} ‖D^α u‖_{C(Ū)} + Σ_{|α|=k} [D^α u]_{C^{0,γ}(Ū)}`. This file states
these as Evans does, with values in `ℝ≥0∞` so that finiteness is the membership condition. It
proves that a finite Hölder seminorm is Mathlib's `HolderOnWith`, and that `C^{0,γ}(Ū)` is the
bounded functions in `C^0(Ū)` satisfying a Hölder condition.

## Main declarations

* `EllipticPdes.Analysis.supNorm`: Evans's `‖u‖_{C(Ū)}`.
* `EllipticPdes.Analysis.holderSeminorm`: Evans's `[u]_{C^{0,γ}(Ū)}`.
* `EllipticPdes.Analysis.holderNorm`: Evans's `‖u‖_{C^{k,γ}(Ū)}`.
* `EllipticPdes.Analysis.HolderSpace`: Evans's `C^{k,γ}(Ū)`.
* `EllipticPdes.Analysis.holderOnWith_iff_holderSeminorm_le`: `HolderOnWith C γ u U` is
  `[u]_{C^{0,γ}(Ū)} ≤ C`.
* `EllipticPdes.Analysis.holderNorm_zero`: the case `k = 0` of the Hölder norm.
* `EllipticPdes.Analysis.mem_holderSpace_zero_iff`: the case `k = 0` of the Hölder space.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), Section 5.1 (Hölder spaces, p. 254
and p. 255).
-/

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace EllipticPdes.Analysis

variable {d k : ℕ} {γ : ℝ≥0} {U : Set (EuclideanSpace ℝ (Fin d))} {u : EuclideanSpace ℝ (Fin d) → ℝ}

/-- **Supremum norm.** `‖u‖_{C(Ū)} = sup_{x ∈ U} |u x|`, valued in `ℝ≥0∞` so that it is `⊤`
for an unbounded function. Evans §5.1 Def (i) (p. 254). -/
def supNorm (U : Set (EuclideanSpace ℝ (Fin d))) (u : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ U, ‖u x‖ₑ

/-- **Hölder seminorm.** `[u]_{C^{0,γ}(Ū)} = sup_{x,y ∈ U, x ≠ y} |u x - u y| / |x - y|^γ`.
Evans §5.1 Def (ii) (p. 254). -/
def holderSeminorm (γ : ℝ≥0) (U : Set (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ U, ⨆ y ∈ U, ⨆ (_ : x ≠ y), ENNReal.ofReal (|u x - u y| / ‖x - y‖ ^ (γ : ℝ))

/-- **Hölder norm.** `‖u‖_{C^{k,γ}(Ū)} = Σ_{|α|≤k} ‖D^α u‖_{C(Ū)} + Σ_{|α|=k} [D^α u]_{C^{0,γ}(Ū)}`.
Evans §5.1 Def (Hölder space), formula (3) (p. 255). -/
def holderNorm (k : ℕ) (γ : ℝ≥0) (U : Set (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  ∑ α : Sobolev.MultiIdx d k, supNorm U (classicalDeriv α u) +
    ∑ α ∈ Finset.univ.filter (fun α : Sobolev.MultiIdx d k => α.order = k),
      holderSeminorm γ U (classicalDeriv α u)

/-- **Space `C^{k,γ}(Ū)`.** The functions in `C^k(Ū)` with finite Hölder norm.
Evans §5.1 Def (Hölder space) (p. 255). -/
def HolderSpace (k : ℕ) (γ : ℝ≥0) (U : Set (EuclideanSpace ℝ (Fin d))) :
    Set (EuclideanSpace ℝ (Fin d) → ℝ) :=
  {u | CkBar k U u ∧ holderNorm k γ U u < ⊤}

/-- A function satisfies a Hölder condition with constant `C` and exponent `γ` on `U` exactly
when its Hölder seminorm on `U` is at most `C`. Evans §5.1 Def (ii) (p. 254). The converse
of the inequality `|u x - u y| ≤ C |x - y|^γ` is proved as well.
Evans assumes `0 < γ`. The proof does not use it and the statement keeps it. -/
theorem holderOnWith_iff_holderSeminorm_le (_hγ : 0 < γ) (C : ℝ≥0) :
    HolderOnWith C γ u U ↔ holderSeminorm γ U u ≤ C := by
  unfold holderSeminorm
  simp only [iSup_le_iff]
  -- for `x ≠ y` both conditions say `|u x - u y| ≤ C * |x - y|^γ`
  have key : ∀ x y : EuclideanSpace ℝ (Fin d), x ≠ y →
      (edist (u x) (u y) ≤ C * edist x y ^ (γ : ℝ) ↔
        ENNReal.ofReal (|u x - u y| / ‖x - y‖ ^ (γ : ℝ)) ≤ C) := by
    intro x y hxy
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    have hpow : 0 < ‖x - y‖ ^ (γ : ℝ) := Real.rpow_pos_of_pos hpos _
    have h1 : edist (u x) (u y) ≤ C * edist x y ^ (γ : ℝ) ↔
        |u x - u y| ≤ C * ‖x - y‖ ^ (γ : ℝ) := by
      rw [edist_dist, edist_dist, Real.dist_eq, dist_eq_norm, ENNReal.ofReal_rpow_of_pos hpos,
        ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
      exact ENNReal.ofReal_le_ofReal_iff (by positivity)
    have h2 : ENNReal.ofReal (|u x - u y| / ‖x - y‖ ^ (γ : ℝ)) ≤ C ↔
        |u x - u y| / ‖x - y‖ ^ (γ : ℝ) ≤ C := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal_iff C.coe_nonneg
    rw [h1, h2, div_le_iff₀ hpow]
  constructor
  · intro h x hx y hy hxy
    exact (key x y hxy).1 (h x hx y hy)
  · intro h x hx y hy
    by_cases hxy : x = y
    · subst hxy; simp
    · exact (key x y hxy).2 (h x hx y hy hxy)

/-- The Hölder norm of order `0` is the supremum norm plus the Hölder seminorm.
Evans §5.1 Def (Hölder space), formula (3) at `k = 0` (p. 255). -/
theorem holderNorm_zero (γ : ℝ≥0) :
    holderNorm 0 γ U u = supNorm U u + holderSeminorm γ U u := by
  have hsub : ∀ α : Sobolev.MultiIdx d 0, α = Sobolev.MultiIdx.zero := fun α =>
    Subtype.ext (funext fun i => Fin.ext (by
      have := (α.1 i).2
      simp only [Sobolev.MultiIdx.zero]
      omega))
  have : Unique (Sobolev.MultiIdx d 0) := ⟨⟨Sobolev.MultiIdx.zero⟩, hsub⟩
  have hder : classicalDeriv (Sobolev.MultiIdx.zero (d := d) (k := 0)) u = u := by
    simp [classicalDeriv, Sobolev.MultiIdx.dirs_zero, Sobolev.iterPartialD_nil]
  have hord : Finset.univ.filter (fun α : Sobolev.MultiIdx d 0 => α.order = 0) = Finset.univ := by
    refine Finset.filter_true_of_mem fun α _ => ?_
    rw [hsub α]
    simp [Sobolev.MultiIdx.order, Sobolev.MultiIdx.zero]
  unfold holderNorm
  rw [hord, Finset.univ_unique, Finset.sum_singleton, Finset.sum_singleton]
  have : (default : Sobolev.MultiIdx d 0) = Sobolev.MultiIdx.zero := hsub _
  rw [this, hder]

/-- The space `C^{0,γ}(Ū)` is the set of `u ∈ C^0(Ū)` that are bounded on `U` and satisfy a
Hölder condition of exponent `γ` on `U`. Evans §5.1 Def (Hölder space) (p. 255), with his
hypothesis `0 < γ ≤ 1`. The statement keeps `γ ≤ 1` as Evans's hypothesis.
The proof uses `0 < γ` only. -/
theorem mem_holderSpace_zero_iff (hγ : 0 < γ) (_hγ1 : γ ≤ 1) :
    u ∈ HolderSpace 0 γ U ↔ CkBar 0 U u ∧ supNorm U u < ⊤ ∧ ∃ C, HolderOnWith C γ u U := by
  have hfin : ∀ {a b : ℝ≥0∞}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ := ENNReal.add_lt_top
  have hC : holderSeminorm γ U u < ⊤ ↔ ∃ C : ℝ≥0, HolderOnWith C γ u U := by
    constructor
    · intro h
      obtain ⟨C, hC⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 h
      exact ⟨C, (holderOnWith_iff_holderSeminorm_le hγ C).2 hC.1.le⟩
    · rintro ⟨C, hC⟩
      exact lt_of_le_of_lt ((holderOnWith_iff_holderSeminorm_le hγ C).1 hC) ENNReal.coe_lt_top
  unfold HolderSpace
  simp only [Set.mem_ofPred_eq, holderNorm_zero, hfin, hC]

end EllipticPdes.Analysis
