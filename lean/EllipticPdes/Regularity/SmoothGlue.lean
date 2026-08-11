/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Regularity.HigherWeakDeriv

/-!
# A locally smooth representative is a smooth representative

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 3 (p. 331) is proved on
balls: the Sobolev ladder runs inside a ball compactly contained in the region, and produces a
smooth function agreeing almost everywhere with the solution there. The theorem is stated on
the region. This file is the passage between the two, and it is the only part of that argument
carrying no analysis.

Two observations do the work.

* **The local representatives agree where they overlap.** Both are continuous on the
  intersection of their balls, which is open, and both agree almost everywhere with the same
  class there. A nonempty open set has positive Lebesgue measure, so two continuous functions
  agreeing almost everywhere on one agree on it.
* **So no gluing is needed.** Sending `x` to the value at `x` of the representative attached to
  `x` itself already agrees with every local representative on the whole of that
  representative's ball, by the previous point. Smoothness is then local, and the almost
  everywhere identity follows from a countable subcover.

## Main declarations

* `eqOn_of_ae_eq_of_continuousOn`: continuous functions agreeing almost everywhere on an open
  set agree on it.
* `exists_contDiffOn_of_locally_ae`: local smooth representatives assemble into one.
-/

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

variable {d : ℕ}

/-- **Almost everywhere equality upgrades to equality for continuous functions on an open
set.** Where they differ at a point they differ on an open neighbourhood, which carries
positive Lebesgue measure. -/
theorem eqOn_of_ae_eq_of_continuousOn {W : Set (EuclideanSpace ℝ (Fin d))} (hW : IsOpen W)
    {f g : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContinuousOn f W) (hg : ContinuousOn g W)
    (hae : f =ᵐ[volume.restrict W] g) : Set.EqOn f g W := by
  intro x hx
  by_contra hne
  have hcont : ContinuousAt (fun y => f y - g y) x :=
    (hf.sub hg).continuousAt (hW.mem_nhds hx)
  have hev : ∀ᶠ y in nhds x, ¬ f y = g y := by
    filter_upwards [hcont.eventually_ne (sub_ne_zero.2 hne)] with y hy hc
    exact hy (by rw [hc, sub_self])
  obtain ⟨O, hOsub, hOo, hxO⟩ := mem_nhds_iff.1 (Filter.inter_mem hev (hW.mem_nhds hx))
  have hOW : O ⊆ W := fun y hy => (hOsub hy).2
  have hzero : volume.restrict W O = 0 :=
    nonpos_iff_eq_zero.1
      ((measure_mono (fun y hy => (hOsub hy).1)).trans (ae_iff.1 hae).le)
  rw [Measure.restrict_apply hOo.measurableSet,
    Set.inter_eq_self_of_subset_left hOW] at hzero
  exact absurd hzero (hOo.measure_pos volume ⟨x, hxO⟩).ne'

/-- **Local smooth representatives assemble into one.** If every point of an open `U` has an
open ball inside `U` on which some smooth function agrees almost everywhere with `u`, then a
single smooth function does so on all of `U`.

No gluing construction appears. The value at `x` is taken from the representative attached to
`x`, and `eqOn_of_ae_eq_of_continuousOn` makes that choice agree with every other
representative on the whole of its own ball, which is what turns pointwise selection into a
locally smooth function. -/
theorem exists_contDiffOn_of_locally_ae {U : Set (EuclideanSpace ℝ (Fin d))} (hUo : IsOpen U)
    (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (h : ∀ x ∈ U, ∃ B : Set (EuclideanSpace ℝ (Fin d)), IsOpen B ∧ x ∈ B ∧ B ⊆ U ∧
      ∃ v : EuclideanSpace ℝ (Fin d) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v B ∧
        v =ᵐ[volume.restrict B] u) :
    ∃ u' : EuclideanSpace ℝ (Fin d) → ℝ,
      u' =ᵐ[volume.restrict U] u ∧ ContDiffOn ℝ (⊤ : ℕ∞) u' U := by
  classical
  choose B hBo hxB hBU v hvc hvae using h
  -- The representative attached to `x` agrees with the one attached to `y` on `B y`.
  have key : ∀ (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ U),
      Set.EqOn (fun x => if hx : x ∈ U then v x hx x else 0) (v y hy) (B y hy) := by
    intro y hy x hxB'
    have hxU : x ∈ U := hBU y hy hxB'
    have hInt : IsOpen (B x hxU ∩ B y hy) := (hBo x hxU).inter (hBo y hy)
    have hmono : ∀ (z : EuclideanSpace ℝ (Fin d)) (hz : z ∈ U),
        B x hxU ∩ B y hy ⊆ B z hz → v z hz =ᵐ[volume.restrict (B x hxU ∩ B y hy)] u :=
      fun z hz hsub =>
        (hvae z hz).filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hagree : Set.EqOn (v x hxU) (v y hy) (B x hxU ∩ B y hy) :=
      eqOn_of_ae_eq_of_continuousOn hInt
        ((hvc x hxU).continuousOn.mono Set.inter_subset_left)
        ((hvc y hy).continuousOn.mono Set.inter_subset_right)
        ((hmono x hxU Set.inter_subset_left).trans
          (hmono y hy Set.inter_subset_right).symm)
    simp only [dif_pos hxU]
    exact hagree ⟨hxB x hxU, hxB'⟩
  refine ⟨fun x => if hx : x ∈ U then v x hx x else 0, ?_, ?_⟩
  · -- Almost everywhere on `U`, through a countable subcover.
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun i : {x : EuclideanSpace ℝ (Fin d) // x ∈ U} => B i.1 i.2) (fun i => hBo i.1 i.2)
    have hUeq : U = ⋃ i ∈ T, B i.1 i.2 := by
      rw [hTU]
      refine Set.Subset.antisymm (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxB x hx⟩) ?_
      rintro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      exact hBU i.1 i.2 hi
    set N : Set (EuclideanSpace ℝ (Fin d)) :=
      {x | ¬ (if hx : x ∈ U then v x hx x else 0) = u x} with hN
    have hNi : ∀ i ∈ T, volume (N ∩ B i.1 i.2) = 0 := by
      intro i _
      have hlocal : ∀ᵐ x ∂(volume.restrict (B i.1 i.2)),
          (if hx : x ∈ U then v x hx x else 0) = u x := by
        filter_upwards [hvae i.1 i.2, ae_restrict_mem (hBo i.1 i.2).measurableSet] with x h1 h2
        have hk : (if hx : x ∈ U then v x hx x else 0) = v i.1 i.2 x := key i.1 i.2 h2
        rw [hk, h1]
      have hz := ae_iff.1 hlocal
      rw [hN]
      rwa [Measure.restrict_apply₀' (hBo i.1 i.2).measurableSet.nullMeasurableSet] at hz
    have hsplit : N ∩ U = ⋃ i ∈ T, N ∩ B i.1 i.2 := by
      rw [← Set.inter_iUnion₂, ← hUeq]
    rw [Filter.EventuallyEq, ae_iff,
      Measure.restrict_apply₀' hUo.measurableSet.nullMeasurableSet]
    change volume (N ∩ U) = 0
    rw [hsplit]
    exact (measure_biUnion_null_iff hTc).2 hNi
  · -- Smoothness is local, and on each ball the function is a local representative.
    refine contDiffOn_of_locally_contDiffOn fun x hx => ⟨B x hx, hBo x hx, hxB x hx, ?_⟩
    rw [Set.inter_eq_self_of_subset_right (hBU x hx)]
    exact (hvc x hx).congr fun y hy => key x hx hy

end EllipticPdes.Regularity
