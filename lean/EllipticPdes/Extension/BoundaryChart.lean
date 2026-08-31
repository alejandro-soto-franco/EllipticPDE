/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Extension.ShearWeakGrad
import EllipticPdes.Extension.EvenReflection

/-!
# Extension across a `C¹` boundary chart

Near a boundary point a domain with `C¹` boundary is, after relabelling the coordinates, the
region above the graph of a `C¹` function `γ` of the remaining ones. This file extends a
Sobolev class across that graph, which is the local half of Guo's extension operator.

The route is the composite of the three maps the chapter has built. The shear `S y = y + γ(y)eⱼ`
inverts the flattening, so the flattening `T = S⁻¹` sends the region above the graph onto the
half space; the class travels the other way, through `S`, and picks up the transpose of the
shear's derivative on its gradient. The flattened class is then reflected across the interface,
and the reflection returns through `T`.

## Main declarations

* `EllipticPdes.Extension.aboveGraph`: the region above the graph of a chart.
* `EllipticPdes.Extension.preimage_shear_aboveGraph`: the shear pulls that region back to the
  half space.
* `EllipticPdes.Extension.chartExt` and `EllipticPdes.Extension.chartExtGrad`: the extension
  and its gradient.
* `EllipticPdes.Extension.hasWeakGradOn_chartExt`: the extension has that weak gradient on the
  whole space.
* `EllipticPdes.Extension.chartExt_eq_of_mem`: the extension agrees with the class on the
  region it extends.
* `EllipticPdes.Extension.eLpNorm_chartExt_le`: its bound in every `Lᵖ` seminorm.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem III.2.2
steps 1 and 2 (p. 21); L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4 Theorem 1
and §C.1.
-/

open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn)
open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-! ### The region above a graph -/

/-- **Region above the graph of a chart**, in the `j`-th coordinate. -/
def aboveGraph (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) := {y | γ y < y j}

theorem isOpen_aboveGraph {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hγ : Continuous γ) :
    IsOpen (aboveGraph j γ) :=
  isOpen_lt hγ (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous

/-- The `j`-th coordinate of a sheared point. -/
theorem shear_coord {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (y : EuclideanSpace ℝ (Fin d)) : (shear j γ y) j = y j + γ y := by
  simp [shear]

/-- **Pull-back of the half space through the flattening.** -/
theorem aboveGraph_eq_preimage {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} :
    aboveGraph j γ = shear j (fun z => -γ z) ⁻¹' halfSpace j := by
  ext y
  have hc : (shear j (fun z => -γ z) y) j = y j - γ y := by
    rw [shear_coord]; ring
  simp only [aboveGraph, Set.mem_preimage, halfSpace, Set.mem_setOf_eq, hc]
  constructor <;> intro h <;> linarith

/-- **Pull-back of the region above the graph through the shear.** -/
theorem preimage_shear_aboveGraph {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hind : IndepCoord j γ) : shear j γ ⁻¹' aboveGraph j γ = halfSpace j := by
  ext x
  have hγS : γ (shear j γ x) = γ x := hind x (γ x)
  simp only [Set.mem_preimage, aboveGraph, halfSpace, Set.mem_setOf_eq, shear_coord, hγS]
  constructor <;> intro h <;> linarith

/-! ### The extension -/

/-- **Gradient of a class pulled back through the shear**, the transpose of the shear's
derivative applied to the gradient. -/
def shearGrad (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => g k (shear j γ x) + g j (shear j γ x) * partialD k γ x

/-- **Extension across a `C¹` boundary chart.** The chart is flattened by the shear, the
flattened class is reflected across the interface, and the reflection returns through the
inverse shear. -/
def chartExt (j : Fin d) (γ u : EuclideanSpace ℝ (Fin d) → ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun y => evenExt j (fun x => u (shear j γ x)) (shear j (fun z => -γ z) y)

/-- **Gradient of the extension across a `C¹` boundary chart.** The second term is the shear's
own contribution, with the sign of the inverse chart. -/
def chartExtGrad (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun y => evenExtGrad j (shearGrad j γ g) k (shear j (fun z => -γ z) y)
    - evenExtGrad j (shearGrad j γ g) j (shear j (fun z => -γ z) y) * partialD k γ y

/-- The partial derivative of a negated chart. -/
theorem partialD_neg {γ : EuclideanSpace ℝ (Fin d) → ℝ} (k : Fin d)
    (y : EuclideanSpace ℝ (Fin d)) : partialD k (fun z => -γ z) y = -partialD k γ y := by
  simp only [partialD, fderiv_fun_neg, ContinuousLinearMap.neg_apply]

private theorem integrableOn_mul_bounded {B : Set (EuclideanSpace ℝ (Fin d))}
    {w h : EuclideanSpace ℝ (Fin d) → ℝ} (hw : IntegrableOn w B volume) (hc : Continuous h)
    {C : ℝ} (hC : ∀ x, ‖h x‖ ≤ C) : IntegrableOn (fun x => w x * h x) B volume := by
  have hbd := hw.bdd_mul (f := h) hc.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  exact hbd.congr (Filter.Eventually.of_forall fun x => mul_comm (h x) (w x))

/-- **Weak gradient of the extension across a `C¹` boundary chart**, on the whole space. The
class travels through the shear onto the half space, the reflection extends it across the
interface, and the inverse shear returns it, each of the three steps supplying its own half of
the gradient. -/
theorem hasWeakGradOn_chartExt {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hind : IndepCoord j γ) {M : ℝ}
    (hγb : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)), ‖partialD k γ y‖ ≤ M)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u (aboveGraph j γ) volume)
    (hgi : ∀ k, IntegrableOn (g k) (aboveGraph j γ) volume)
    (hwg : HasWeakGradOn (aboveGraph j γ) u g) :
    HasWeakGradOn Set.univ (chartExt j γ u) (chartExtGrad j γ g) := by
  have hγd : Differentiable ℝ γ := hγ.differentiable (by simp)
  have hnegC1 : ContDiff ℝ 1 fun z => -γ z := hγ.neg
  have hnegd : Differentiable ℝ fun z => -γ z := hγd.neg
  have hckc : ∀ k : Fin d, Continuous (partialD k γ) := fun _ =>
    (hγ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hnegb : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)),
      ‖partialD k (fun z => -γ z) y‖ ≤ M := by
    intro k y
    rw [partialD_neg, norm_neg]
    exact hγb k y
  -- the class and its gradient, moved onto the half space
  have hmpS : MeasurePreserving (shear j γ) volume volume := measurePreserving_shear hγd hind
  have hmeS : MeasurableEmbedding (shear j γ) := measurableEmbedding_shear hγd.continuous hind
  have htrans : ∀ w : EuclideanSpace ℝ (Fin d) → ℝ, IntegrableOn w (aboveGraph j γ) volume →
      IntegrableOn (fun x => w (shear j γ x)) (halfSpace j) volume := by
    intro w hw
    have h := (hmpS.integrableOn_comp_preimage hmeS (f := w) (s := aboveGraph j γ)).mpr hw
    rwa [preimage_shear_aboveGraph hind] at h
  have hgS : ∀ k, IntegrableOn (shearGrad j γ g k) (halfSpace j) volume := by
    intro k
    exact (htrans (g k) (hgi k)).add
      (integrableOn_mul_bounded (htrans (g j) (hgi j)) (hckc k) (hγb k))
  have hS : HasWeakGradOn (halfSpace j) (fun x => u (shear j γ x)) (shearGrad j γ g) := by
    have h := hasWeakGradOn_comp_shear (isOpen_aboveGraph hγd.continuous) hu hgi hwg hγ hind hγb
    rwa [preimage_shear_aboveGraph hind] at h
  -- reflected across the interface
  have hEven : HasWeakGradOn Set.univ (evenExt j fun x => u (shear j γ x))
      (evenExtGrad j (shearGrad j γ g)) :=
    hasWeakGradOn_evenExt (htrans u hu) hgS hS
  -- returned through the inverse shear
  have hFinal := hasWeakGradOn_comp_shear (B := Set.univ) isOpen_univ
    (integrable_evenExt (htrans u hu)).integrableOn
    (fun k => (integrable_evenExtGrad k (hgS k)).integrableOn)
    hEven hnegC1 hind.neg hnegb
  rw [Set.preimage_univ] at hFinal
  have hgrad : chartExtGrad j γ g
      = fun k y => evenExtGrad j (shearGrad j γ g) k (shear j (fun z => -γ z) y)
        + evenExtGrad j (shearGrad j γ g) j (shear j (fun z => -γ z) y)
          * partialD k (fun z => -γ z) y := by
    funext k y
    simp only [chartExtGrad, partialD_neg]
    ring
  rw [hgrad]
  exact hFinal

/-- **Agreement of the extension with the class on the region it extends.** -/
theorem chartExt_eq_of_mem {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hind : IndepCoord j γ) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ aboveGraph j γ) : chartExt j γ u y = u y := by
  have hmem : shear j (fun z => -γ z) y ∈ halfSpace j := by
    rw [aboveGraph_eq_preimage] at hy
    exact hy
  have h0 : (0 : ℝ) ≤ (shear j (fun z => -γ z) y) j := le_of_lt hmem
  simp only [chartExt, evenExt]
  rw [if_pos h0, shear_neg_shear hind y]

/-- **Bound on the extension in every `Lᵖ` seminorm.** Both shears preserve measure and the
reflection doubles, so the extension over the whole space is bounded by twice the seminorm over
the region above the graph. -/
theorem eLpNorm_chartExt_le {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict (aboveGraph j γ))) :
    eLpNorm (chartExt j γ u) p volume
      ≤ 2 * eLpNorm u p (volume.restrict (aboveGraph j γ)) := by
  have hnegd : Differentiable ℝ fun z => -γ z := hγ.neg
  have hmpS : MeasurePreserving (shear j γ) volume volume := measurePreserving_shear hγ hind
  have hmeS : MeasurableEmbedding (shear j γ) := measurableEmbedding_shear hγ.continuous hind
  -- the flattened class, on the half space
  have hres : MeasurePreserving (shear j γ) (volume.restrict (halfSpace j))
      (volume.restrict (aboveGraph j γ)) := by
    have h := hmpS.restrict_preimage_emb hmeS (aboveGraph j γ)
    rwa [preimage_shear_aboveGraph hind] at h
  have hvm : AEStronglyMeasurable (fun x => u (shear j γ x))
      (volume.restrict (halfSpace j)) := hu.comp_measurePreserving hres
  have hveq : eLpNorm (fun x => u (shear j γ x)) p (volume.restrict (halfSpace j))
      = eLpNorm u p (volume.restrict (aboveGraph j γ)) :=
    eLpNorm_comp_measurePreserving hu hres
  -- the reflection, returned through the inverse shear
  have hem : AEStronglyMeasurable (evenExt j fun x => u (shear j γ x)) volume :=
    aestronglyMeasurable_evenExt hvm
  have hback : eLpNorm (chartExt j γ u) p volume
      = eLpNorm (evenExt j fun x => u (shear j γ x)) p volume :=
    eLpNorm_comp_measurePreserving hem (measurePreserving_shear hnegd hind.neg)
  calc eLpNorm (chartExt j γ u) p volume
      = eLpNorm (evenExt j fun x => u (shear j γ x)) p volume := hback
    _ ≤ 2 * eLpNorm (fun x => u (shear j γ x)) p (volume.restrict (halfSpace j)) :=
        eLpNorm_evenExt_le hp hvm
    _ = 2 * eLpNorm u p (volume.restrict (aboveGraph j γ)) := by rw [hveq]

end EllipticPdes.Extension
