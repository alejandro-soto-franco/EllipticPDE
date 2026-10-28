/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import EllipticPdes.Analysis.WeakCompactness
public import EllipticPdes.Sobolev.GraphEuclidean
public import EllipticPdes.Sobolev.GraphLattice
public import EllipticPdes.Spectrum.RellichDischarge

/-!
# Weak convergence and compact embedding

Evans defines weak convergence `u_k ⇀ u` of a sequence in a Banach space by convergence of
`f(u_k)` for every bounded linear functional `f`, and a compact embedding `X ⊂⊂ Y` by an
injective bounded inclusion that maps bounded sequences to sequences with a convergent
subsequence. This file states each notion as Evans does. The characterising theorems relate
them to Mathlib's `StrongDual` and `IsCompactOperator`, and to the Hilbert-space form of weak
sequential compactness in `EllipticPdes.Analysis.exists_weakLimit`.

## Main declarations

* `EllipticPdes.Analysis.WeakConverges`: convergence of `f (u k)` for every dual element `f`.
* `EllipticPdes.Analysis.weakConverges_of_tendsto`: strong convergence implies weak convergence.
* `EllipticPdes.Analysis.WeakConverges.bddAbove_norm`: a weakly convergent sequence is bounded.
* `EllipticPdes.Analysis.weakConverges_iff_inner`: the Hilbert form, by Riesz representation.
* `EllipticPdes.Analysis.CompactlyEmbedded`: Evans's compact embedding of `X` into `Y`.
* `EllipticPdes.Analysis.compactlyEmbedded_iff`: a bounded inclusion is a compact embedding iff
  it is injective and a compact operator.
* `EllipticPdes.Sobolev.embL2_injective`: `H₀¹(Ω) → L²(Ω)` is injective on an open set.
* `EllipticPdes.Sobolev.compactlyEmbedded_embL2`: the Rellich theorem in this form.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), Appendix D.4 (weak convergence,
p. 723) and §5.7 (the definition of compact embedding, p. 286, and the Rellich-Kondrachov
theorem).
-/

@[expose] public section

open Filter Topology MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace EllipticPdes.Analysis

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- **Weak convergence.** `u k ⇀ x` when `f (u k) → f x` for every bounded linear functional `f`.
Evans Appendix D.4 (Definition of weak convergence, p. 723). -/
def WeakConverges (u : ℕ → X) (x : X) : Prop :=
  ∀ f : StrongDual ℝ X, Tendsto (fun k => f (u k)) atTop (𝓝 (f x))

/-- Strong convergence implies weak convergence. Evans records this after the definition of weak
convergence (Appendix D.4, p. 723). -/
theorem weakConverges_of_tendsto {u : ℕ → X} {x : X} (h : Tendsto u atTop (𝓝 x)) :
    WeakConverges u x := fun f => (f.continuous.tendsto x).comp h

/-- A weakly convergent sequence is bounded. Evans records this after the definition of weak
convergence (Appendix D.4, p. 723). The proof applies the uniform boundedness principle to the
sequence in the double dual. -/
theorem WeakConverges.bddAbove_norm {u : ℕ → X} {x : X} (h : WeakConverges u x) :
    BddAbove (Set.range fun k => ‖u k‖) := by
  have key : ∀ f : StrongDual ℝ X, ∃ C, ∀ k,
      ‖(NormedSpace.inclusionInDoubleDual ℝ X (u k)) f‖ ≤ C := fun f => by
    obtain ⟨C, hC⟩ := (h f).norm.bddAbove_range
    exact ⟨C, fun k => by simpa using hC ⟨k, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus key
  exact ⟨C, by
    rintro _ ⟨k, rfl⟩
    simpa using (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℝ) (E := X)).norm_map (u k) ▸ hC k⟩

/-- **Weak convergence in a Hilbert space.** In a real Hilbert space, `u k ⇀ x` iff every inner
product `⟪u k, v⟫` converges to `⟪x, v⟫`. The statement `exists_weakLimit` uses the right-hand
form. The two directions use the Riesz representation of the dual. -/
theorem weakConverges_iff_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {u : ℕ → H} {x : H} :
    WeakConverges u x ↔ ∀ v : H, Tendsto (fun k => ⟪u k, v⟫_ℝ) atTop (𝓝 ⟪x, v⟫_ℝ) := by
  constructor
  · intro h v
    simpa [real_inner_comm] using h (innerSL ℝ v)
  · intro h f
    have hf := h ((InnerProductSpace.toDual ℝ H).symm f)
    have e : ∀ w, f w = ⟪w, (InnerProductSpace.toDual ℝ H).symm f⟫_ℝ := fun w => by
      rw [real_inner_comm]
      exact (InnerProductSpace.toDual_symm_apply).symm
    simpa only [e] using hf

/-- **Compact embedding.** `ι : X → Y` is a compact embedding when it is injective, bounded, and
maps every bounded sequence to a sequence with a convergent subsequence. Evans §5.7 (Definition
of compact embedding, p. 286) writes `X ⊂ Y`, and the definition here takes that as an injective
linear map. -/
def CompactlyEmbedded (ι : X →ₗ[ℝ] Y) : Prop :=
  Function.Injective ι ∧ (∃ C, ∀ u, ‖ι u‖ ≤ C * ‖u‖) ∧
    ∀ u : ℕ → X, BddAbove (Set.range fun k => ‖u k‖) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y, Tendsto (fun j => ι (u (φ j))) atTop (𝓝 y)

/-- **Compact embeddings are the injective compact operators.** A bounded linear inclusion is a
compact embedding in Evans's sense iff it is injective and a compact operator. Evans §5.7
(p. 286) gives the definition, and the equivalence is proved here in both directions. -/
theorem compactlyEmbedded_iff (ι : X →L[ℝ] Y) :
    CompactlyEmbedded (ι : X →ₗ[ℝ] Y) ↔ Function.Injective ι ∧ IsCompactOperator ι := by
  constructor
  · rintro ⟨hinj, -, hseq⟩
    refine ⟨hinj,
      (isCompactOperator_iff_isCompact_closure_image_closedBall (ι : X →ₗ[ℝ] Y) one_pos).2 ?_⟩
    refine IsSeqCompact.isCompact fun a ha => ?_
    have hnear :
        ∀ k, ∃ v ∈ Metric.closedBall (0 : X) 1, dist (a k) (ι v) < 1 / (k + 1 : ℝ) :=
      fun k => by
        obtain ⟨_, ⟨v, hv, rfl⟩, hd⟩ :=
          Metric.mem_closure_iff.1 (ha k) (1 / (k + 1 : ℝ)) (by positivity)
        exact ⟨v, hv, hd⟩
    choose v hv hd using hnear
    obtain ⟨φ, hφ, y, hy⟩ := hseq v ⟨1, by
      rintro _ ⟨k, rfl⟩
      simpa using hv k⟩
    refine ⟨y, ?_, φ, hφ, ?_⟩
    · exact isClosed_closure.mem_of_tendsto hy (Eventually.of_forall fun j =>
        subset_closure ⟨v (φ j), hv _, rfl⟩)
    · have h1 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hdist : Tendsto (fun j => dist (a (φ j)) (ι (v (φ j)))) atTop (𝓝 0) :=
        squeeze_zero (fun _ => dist_nonneg) (fun j => (hd (φ j)).le) (h1.comp hφ.tendsto_atTop)
      refine tendsto_of_tendsto_of_dist hy ?_
      simp_rw [Function.comp_apply, dist_comm]
      exact hdist
  · rintro ⟨hinj, hc⟩
    refine ⟨hinj, ⟨‖ι‖, fun u => ι.le_opNorm u⟩, fun u ⟨M, hM⟩ => ?_⟩
    have hmem : ∀ k, ι (u k) ∈ closure (ι '' Metric.closedBall (0 : X) (max M 1)) := fun k =>
      subset_closure ⟨u k, by simpa using (hM ⟨k, rfl⟩).trans (le_max_left _ _), rfl⟩
    obtain ⟨y, -, φ, hφ, hy⟩ :=
      (hc.isCompact_closure_image_closedBall (max M 1)).tendsto_subseq hmem
    exact ⟨φ, hφ, y, hy⟩

end EllipticPdes.Analysis

namespace EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- **Injectivity of the inclusion `H₀¹(Ω) → L²(Ω)`.** Evans writes `H_0^1(U) ⊂ L^2(U)` (§5.7,
p. 286) and takes the injectivity for granted. On an open `Ω` an element of `H₀¹` with zero
function part has zero gradient part, because the gradient of a `W^{1,2}` function vanishes
almost everywhere on a level set (Gilbarg and Trudinger Lemma 7.7, p. 152). -/
theorem embL2_injective (hΩ : IsOpen Ω) : Function.Injective (embL2 Ω) := by
  refine (injective_iff_map_eq_zero (embL2 Ω)).2 fun U hU => ?_
  set V : H1Graph.H01 volume Ω := H1Graph.h01Equiv Ω U with hV
  have h0 : H1Graph.fnL (V : H1Graph volume Ω) = 0 := by
    rw [hV, H1Graph.fnL_h01Equiv]
    exact hU
  have hW : (V : H1Graph volume Ω) ∈ H1Graph.W12 volume Ω := H1Graph.H01_le_W12 V.2
  have hf : ∀ᵐ x ∂(volume.restrict Ω), H1Graph.fnL (V : H1Graph volume Ω) x = 0 := by
    rw [h0]
    exact Lp.coeFn_zero ℝ 2 _
  have hg : H1Graph.gradL (V : H1Graph volume Ω) = 0 := by
    refine Lp.ext ?_
    filter_upwards [H1Graph.ae_gradL_eq_zero_of_fnL_eq hΩ hW 0, hf,
      Lp.coeFn_zero (EuclideanSpace ℝ (Fin d)) 2 (volume.restrict Ω)] with x h1 h2 h3
    rw [h3]
    exact h1 h2
  have hV0 : V = 0 := Subtype.ext (H1Graph.ext (by rw [h0]; rfl) (by rw [hg]; rfl))
  exact (map_eq_zero_iff _ (H1Graph.h01Equiv Ω).injective).1 hV0

/-- **Rellich-Kondrachov as a compact embedding.** For bounded open `Ω`, `H₀¹(Ω)` is compactly
embedded in `L²(Ω)` in the sense of Evans §5.7 (p. 286). The compactness is `embL2_isCompact`,
the `H₀¹` case of the Rellich compactness that Evans states in the Remark after the proof of
Theorem 1 in §5.7 (p. 289) on any bounded open set, and the
injectivity is `embL2_injective`. -/
theorem compactlyEmbedded_embL2 (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) :
    Analysis.CompactlyEmbedded (embL2 Ω : H01 Ω →ₗ[ℝ] L2D Ω) :=
  (Analysis.compactlyEmbedded_iff (embL2 Ω)).2
    ⟨embL2_injective hΩ, embL2_isCompact hΩ.measurableSet hΩb⟩

end EllipticPdes.Sobolev
