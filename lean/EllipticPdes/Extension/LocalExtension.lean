/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Extension.PartitionOfUnity
import EllipticPdes.Extension.Patch
import EllipticPdes.Extension.Motion
import EllipticPdes.Extension.BoundaryChart

/-!
# Local boundary extension

Guo's Theorem III.2.2 reaches its third step with a local extension for each chart: a class on
the chart's neighbourhood agreeing with the original on the part of the domain that
neighbourhood meets. This file proves that statement, which is the whole content of his step 2
once the chart is in hand.

The proof composes what the chapter has built. A cutoff between two balls makes the class reach
the whole region above the chart's graph, the rigid motion of the chart takes it into the
coordinates the graph is written in, the reflection extends it across the graph, and the motion
takes the result back. Guo's step 2 works with a function smooth up to the boundary and reads
the chain rule off it; here every step is a weak gradient.

Two points where the statement is narrower than the machinery. The chart asks nothing of the
gradient of its graph, as Evans' definition does not, so the proof runs on the bounded graph
`exists_bounded_graph` supplies, whose region agrees with the chart's on exactly the ball in
play. The conclusion is on a ball strictly inside the chart's, which is where the cutoff is one,
and is what a partition of unity subordinate to the cover asks for anyway.

## Main declarations

* `EllipticPdes.Extension.exists_localExtension`: the local boundary extension.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem III.2.2
(p. 20), proof step 2 (p. 21); L. C. Evans, *Partial Differential Equations* (2nd ed.),
§5.4 Theorem 1 (p. 253).
-/

open MeasureTheory Metric Set

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn)
open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- **Guo's local boundary extension** (Theorem III.2.2, proof step 2, p. 21). Near a boundary
point the class extends across the boundary: on any ball strictly inside the chart's, there is a
class with a weak gradient there agreeing with the original on the part of the domain the ball
meets. -/
theorem exists_localExtension (c : C1Chart d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {x : EuclideanSpace ℝ (Fin d)} (hfits : c.Fits Ω x) {r : ℝ} (hrc : r < c.radius)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u Ω volume) (hgi : ∀ k, IntegrableOn (g k) Ω volume)
    (hwg : HasWeakGradOn Ω u g) :
    ∃ (U : EuclideanSpace ℝ (Fin d) → ℝ) (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      HasWeakGradOn (ball x r) U G ∧ Integrable U volume ∧
        (∀ k, Integrable (G k) volume) ∧ ∀ y ∈ Ω ∩ ball x r, U y = u y := by
  classical
  obtain ⟨γ, M, hγC1, hγind, hγb, hγeq⟩ :=
    exists_bounded_graph c.graph_contDiff c.graph_indep (c.motion x) c.radius_pos
  -- the region of the bounded graph, in the original coordinates
  set A : Set (EuclideanSpace ℝ (Fin d)) := aboveGraph c.dir γ with hAdef
  set A' : Set (EuclideanSpace ℝ (Fin d)) :=
    (c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' A with hA'def
  have hAopen : IsOpen A := isOpen_aboveGraph (hγC1.differentiable (by simp)).continuous
  have hA'open : IsOpen A' := hAopen.preimage c.motion.continuous
  -- it agrees with the domain on the chart's ball
  have hAW : A' ∩ ball x c.radius = Ω ∩ ball x c.radius := by
    have h1 : A' ∩ ball x c.radius
        = (c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹'
            (A ∩ ball (c.motion x) c.radius) := by
      rw [Set.preimage_inter, preimage_motion_ball]
    rw [h1, hγeq, ← C1Chart.region, Set.preimage_inter, preimage_motion_ball,
      ← c.fits_ball hfits]
  -- the cutoff between the two balls
  obtain ⟨ξ, hξC1, hξ1, hξs⟩ := exists_cutoff_one_on_ball x hrc
  have hξcs : HasCompactSupport ξ :=
    (isCompact_closedBall x c.radius).of_isClosed_subset (isClosed_tsupport ξ)
      (hξs.trans ball_subset_closedBall)
  have hsub : A' ∩ ball x c.radius ⊆ Ω := by rw [hAW]; exact Set.inter_subset_left
  have hcut := hasWeakGradOn_mul_cutoff_inter hA'open.measurableSet hξC1 hξs
    (hu.mono_set hsub) (fun k => (hgi k).mono_set hsub) (hwg.mono hsub)
  -- the cut-off pieces vanish off the ball
  have hξ0 : ∀ y, y ∉ ball x c.radius → ξ y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun hc => hy (hξs hc)
  have hξd0 : ∀ (k : Fin d) y, y ∉ ball x c.radius → partialD k ξ y = 0 := by
    intro k y hy
    have hxs : y ∉ tsupport ξ := fun hc => hy (hξs hc)
    have hev : ξ =ᶠ[nhds y] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport ξ).isOpen_compl.mem_nhds hxs] with w hw
      exact image_eq_zero_of_notMem_tsupport hw
    rw [partialD, hev.fderiv_eq]
    simp
  obtain ⟨Cξ, hCξ⟩ := hξcs.exists_bound_of_continuous hξC1.continuous
  have hξpc : ∀ k : Fin d, Continuous (partialD k ξ) := fun k =>
    (hξC1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hξpcs : ∀ k : Fin d, HasCompactSupport (partialD k ξ) := fun k =>
    hξcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  -- and are integrable on the region
  have hIu : IntegrableOn (fun y => ξ y * u y) A' volume := by
    refine integrableOn_of_vanishing_off (W := ball x c.radius) hA'open.measurableSet
      measurableSet_ball ?_ ?_
    · exact (EllipticPdes.Embedding.integrableOn_mul_bounded (hu.mono_set hsub)
        hξC1.continuous hCξ).congr (Filter.Eventually.of_forall fun y => mul_comm (u y) (ξ y))
    · intro y hy
      rw [hξ0 y hy, zero_mul]
  have hIg : ∀ k, IntegrableOn (fun y => ξ y * g k y + partialD k ξ y * u y) A' volume := by
    intro k
    obtain ⟨Cd, hCd⟩ := (hξpcs k).exists_bound_of_continuous (hξpc k)
    refine integrableOn_of_vanishing_off (W := ball x c.radius) hA'open.measurableSet
      measurableSet_ball ?_ ?_
    · refine IntegrableOn.add ?_ ?_
      · exact (EllipticPdes.Embedding.integrableOn_mul_bounded ((hgi k).mono_set hsub)
          hξC1.continuous hCξ).congr
          (Filter.Eventually.of_forall fun y => mul_comm (g k y) (ξ y))
      · exact (EllipticPdes.Embedding.integrableOn_mul_bounded (hu.mono_set hsub)
          (hξpc k) hCd).congr
          (Filter.Eventually.of_forall fun y => mul_comm (u y) (partialD k ξ y))
    · intro y hy
      rw [hξ0 y hy, hξd0 k y hy, zero_mul, zero_mul, add_zero]
  -- into the chart's coordinates
  have hAeq : (c.motion.symm : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' A' = A := by
    rw [hA'def, ← Set.preimage_comp]
    ext y
    simp
  have hchart := hasWeakGradOn_comp_linearIsometry hIu hIg hcut c.motion.symm
  rw [hAeq] at hchart
  set V : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun y => ξ (c.motion.symm y) * u (c.motion.symm y) with hVdef
  set H : Fin d → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun k y => ∑ i, c.motion.symm (EuclideanSpace.single k (1 : ℝ)) i *
      (ξ (c.motion.symm y) * g i (c.motion.symm y)
        + partialD i ξ (c.motion.symm y) * u (c.motion.symm y)) with hHdef
  -- integrability there
  have hmpS : MeasurePreserving
      (c.motion.symm : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) volume volume :=
    c.motion.symm.measurePreserving
  have hmeS : MeasurableEmbedding
      (c.motion.symm : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :=
    c.motion.symm.toHomeomorph.measurableEmbedding
  have htrans : ∀ w : EuclideanSpace ℝ (Fin d) → ℝ, IntegrableOn w A' volume →
      IntegrableOn (fun y => w (c.motion.symm y)) A volume := by
    intro w hw
    have h := (hmpS.integrableOn_comp_preimage hmeS (f := w) (s := A')).mpr hw
    rwa [hAeq] at h
  have hVint : IntegrableOn
      (fun y => ξ (c.motion.symm y) * u (c.motion.symm y)) A volume :=
    htrans _ hIu
  have hGint : ∀ k : Fin d, IntegrableOn
      (fun y => ∑ i, c.motion.symm (EuclideanSpace.single k (1 : ℝ)) i *
        (ξ (c.motion.symm y) * g i (c.motion.symm y)
          + partialD i ξ (c.motion.symm y) * u (c.motion.symm y))) A volume := by
    intro k
    refine MeasureTheory.integrable_finsetSum _ fun i _ => ?_
    exact ((htrans _ (hIg i)).const_mul _)
  have hext := hasWeakGradOn_chartExt hγC1 hγind hγb hVint hGint hchart
  -- global integrability of the extension and of its gradient
  have hγd : Differentiable ℝ γ := hγC1.differentiable (by simp)
  have hnegd : Differentiable ℝ fun z => -γ z := hγd.neg
  have hmpT : MeasurePreserving (shear c.dir fun z => -γ z) volume volume :=
    measurePreserving_shear hnegd hγind.neg
  have hmeT : MeasurableEmbedding (shear c.dir fun z => -γ z) :=
    measurableEmbedding_shear hnegd.continuous hγind.neg
  have hback : ∀ w : EuclideanSpace ℝ (Fin d) → ℝ, Integrable w volume →
      Integrable (w ∘ shear c.dir fun z => -γ z) volume := fun w hw =>
    (hmpT.integrable_comp_emb hmeT).mpr hw
  have hVhalf : IntegrableOn
      (fun z => (fun y => ξ (c.motion.symm y) * u (c.motion.symm y)) (shear c.dir γ z))
      (halfSpace c.dir) volume :=
    ((measurePreserving_shear_halfSpace hγd hγind).integrable_comp hVint.1).mpr hVint
  have hIext : Integrable (chartExt c.dir γ
      fun y => ξ (c.motion.symm y) * u (c.motion.symm y)) volume :=
    hback _ (integrable_evenExt hVhalf)
  -- and of the gradient
  have hHint : ∀ k, IntegrableOn (H k) A volume := hGint
  have hSGhalf : ∀ k, IntegrableOn (shearGrad c.dir γ H k) (halfSpace c.dir) volume := by
    intro k
    have hck : Continuous (partialD k γ) :=
      (hγC1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have h1 : ∀ i : Fin d, IntegrableOn (fun z => H i (shear c.dir γ z))
        (halfSpace c.dir) volume := fun i =>
      ((measurePreserving_shear_halfSpace hγd hγind).integrable_comp (hHint i).1).mpr (hHint i)
    exact (h1 k).add (EllipticPdes.Embedding.integrableOn_mul_bounded (h1 c.dir) hck (hγb k))
  have hIextG : ∀ k, Integrable (chartExtGrad c.dir γ H k) volume := by
    intro k
    have hck : Continuous (partialD k γ) :=
      (hγC1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have h1 : Integrable
        (evenExtGrad c.dir (shearGrad c.dir γ H) k ∘ shear c.dir fun z => -γ z) volume :=
      hback _ (integrable_evenExtGrad k (hSGhalf k))
    have h2 : Integrable
        (evenExtGrad c.dir (shearGrad c.dir γ H) c.dir ∘ shear c.dir fun z => -γ z) volume :=
      hback _ (integrable_evenExtGrad c.dir (hSGhalf c.dir))
    exact h1.sub (integrableOn_univ.mp
      (EllipticPdes.Embedding.integrableOn_mul_bounded (integrableOn_univ.mpr h2) hck (hγb k)))
  -- back to the original coordinates, and restricted to the smaller ball
  have hfinal := hasWeakGradOn_comp_linearIsometry hIext.integrableOn
    (fun k => (hIextG k).integrableOn) hext c.motion
  rw [Set.preimage_univ] at hfinal
  have hmpM : MeasurePreserving
      (c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) volume volume :=
    c.motion.measurePreserving
  have hmeM : MeasurableEmbedding
      (c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :=
    c.motion.toHomeomorph.measurableEmbedding
  refine ⟨_, _, hfinal.mono (Set.subset_univ _),
    (hmpM.integrable_comp_emb hmeM).mpr hIext,
    fun k => MeasureTheory.integrable_finsetSum _ fun i _ =>
      ((hmpM.integrable_comp_emb hmeM).mpr (hIextG i)).const_mul _, ?_⟩
  intro y hy
  have hyA' : y ∈ A' := by
    have hmem : y ∈ Ω ∩ ball x c.radius := ⟨hy.1, ball_subset_ball hrc.le hy.2⟩
    rw [← hAW] at hmem
    exact hmem.1
  change chartExt c.dir γ V (c.motion y) = u y
  rw [chartExt_eq_of_mem hγind hyA', hVdef]
  simp only [LinearIsometryEquiv.symm_apply_apply]
  rw [hξ1 y (ball_subset_closedBall hy.2), one_mul]

end EllipticPdes.Extension
