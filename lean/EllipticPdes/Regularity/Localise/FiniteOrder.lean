/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.Localise.Datum

/-!
# Localising coefficients of finite order on an open set

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 1 (p. 327) assumes
`a^{ij} ∈ C¹(U)` and `b^i, c ∈ L^∞(U)`, and Theorem 2 (p. 332) assumes
`a^{ij}, b^i, c ∈ C^{m+1}(U)`. Neither asks a bound on `a^{ij}` over `U`, and neither asks anything
of a coefficient off `U`. `Localise/LocalOp.lean` blends a principal part of class `C^m` on `U` into a
`FullEllipticOp` (`PrincipalOn`, `blendOp`); this file supplies the lower-order coefficients at
finite order, including coefficients that are only essentially bounded and almost everywhere
strongly measurable on `U`.

## Blend

For a test function `χ` of `U` valued in `[0, 1]`, the principal part is
`a_χ = λ I + χ (a − λ I)`, as in `localOp`. At order `m` the product `χ (a − λ I)` is `C^m` on the
whole space with compact support, so every derivative up to order `m` is bounded
(`exists_iteratedFDeriv_bound`), which is `IsCkCoeff` at order `m`. The lower-order
coefficients are supplied already cut off. For `L^∞(U)` coefficients the cutoff multiplies a
measurable modification (`AEStronglyMeasurable.mk`), which agrees with the coefficient almost
everywhere on `U`; for `C^m(U)` coefficients it multiplies the coefficient itself.

## Main declarations

* `C1OpOn`, `exists_localOp_C1`: the coefficients of Theorem 1 and their localisation.
* `CkOpOn`, `exists_localOp_Ck`: the coefficients of Theorem 2 and their localisation.
* `LocalWeakSol.congr_ae`: the local weak formulation transported along coefficients equal
  almost everywhere.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Coefficients of Theorem 1 -/

/-- **Coefficients of Evans §6.3.1 Theorem 1 on an open set.** `a^{ij} ∈ C¹(U)`, uniformly
elliptic almost everywhere on `U`, and `b^i, c ∈ L^∞(U)`: almost everywhere strongly measurable
and essentially bounded on `U`. Nothing is asked off `U`. -/
structure C1OpOn (d : ℕ) (U : Set (EuclideanSpace ℝ (Fin d))) extends PrincipalOn d U 1 where
  /-- The transport (first-order) coefficients. -/
  b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ
  /-- The zeroth-order coefficient. -/
  c : EuclideanSpace ℝ (Fin d) → ℝ
  /-- The essential bound on the transport coefficients over `U`. -/
  Bsup : ℝ
  /-- The essential bound on the zeroth-order coefficient over `U`. -/
  Csup : ℝ
  /-- Every transport component is almost everywhere strongly measurable on `U`. -/
  b_aesm : ∀ i, AEStronglyMeasurable (fun x => b x i) (volume.restrict U)
  /-- The zeroth-order coefficient is almost everywhere strongly measurable on `U`. -/
  c_aesm : AEStronglyMeasurable c (volume.restrict U)
  /-- Every transport component is essentially bounded on `U`. -/
  b_bdd : ∀ i, ∀ᵐ x ∂(volume.restrict U), |b x i| ≤ Bsup
  /-- The zeroth-order coefficient is essentially bounded on `U`. -/
  c_bdd : ∀ᵐ x ∂(volume.restrict U), |c x| ≤ Csup

/-- A cutoff of `U` times a measurable modification of a function essentially bounded on `U`
is measurable and essentially bounded on the whole space. -/
theorem cutoff_mk_bound {U : Set (EuclideanSpace ℝ (Fin d))} (hUm : MeasurableSet U)
    {χ g : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn U χ)
    (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1) (hg : AEStronglyMeasurable g (volume.restrict U)) {B : ℝ}
    (hB : ∀ᵐ x ∂(volume.restrict U), |g x| ≤ B) :
    Measurable (fun x => χ x * hg.mk g x) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |χ x * hg.mk g x| ≤ max B 0 := by
  refine ⟨hχ.1.continuous.measurable.mul hg.stronglyMeasurable_mk.measurable, ?_⟩
  have h1 : ∀ᵐ x ∂(volume.restrict U), |hg.mk g x| ≤ B := by
    filter_upwards [hB, hg.ae_eq_mk] with x h1 h2
    rwa [← h2]
  filter_upwards [(ae_restrict_iff' hUm).1 h1] with x hx
  by_cases hxU : x ∈ U
  · rw [abs_mul, abs_of_nonneg (hχ01 x).1]
    calc χ x * |hg.mk g x| ≤ 1 * B :=
          mul_le_mul (hχ01 x).2 (hx hxU) (abs_nonneg _) zero_le_one
      _ ≤ max B 0 := by rw [one_mul]; exact le_max_left _ _
  · have : χ x = 0 := by
      by_contra hne
      exact hxU (hχ.2.2 (subset_tsupport _ hne))
    simp [this]

/-- **Localisation of the coefficients of Theorem 1.** For every compact `K ⊆ U` there are a
global operator with `C¹` principal part of bounded derivative and an open `W` with
`K ⊆ W ⊆ U`, on which the principal part agrees with the given one everywhere and the
lower-order coefficients agree with the given ones almost everywhere. -/
theorem exists_localOp_C1 {U : Set (EuclideanSpace ℝ (Fin d))} (P : C1OpOn d U) (hU : IsOpen U)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (Op : FullEllipticOp d) (W : Set (EuclideanSpace ℝ (Fin d))), IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
      Nonempty (IsC1Coeff Op.toEllipticCoeff) ∧ (∀ x ∈ W, Op.a x = P.a x) ∧
      (∀ i, ∀ᵐ x ∂(volume.restrict W), Op.b x i = P.b x i) ∧
      (∀ᵐ x ∂(volume.restrict W), Op.c x = P.c x) := by
  obtain ⟨χ, hχ, hχ01, W, hWo, hKW, hcl, hW1⟩ := exists_cutoff_interior_one hU hK hKU
  have hWU : W ⊆ U := subset_closure.trans (hcl.trans hχ.2.2)
  have hUm := hU.measurableSet
  have hb := fun i => cutoff_mk_bound hUm hχ hχ01 (P.b_aesm i) (P.b_bdd i)
  have hc := cutoff_mk_bound hUm hχ hχ01 P.c_aesm P.c_bdd
  set Op := blendOp P.toPrincipalOn hU hχ hχ01 (fun x i => χ x * (P.b_aesm i).mk _ x)
    (fun x => χ x * P.c_aesm.mk _ x) (le_max_right P.Bsup 0) (le_max_right P.Csup 0)
    (fun i => (hb i).1) hc.1 (fun i => (hb i).2) hc.2 with hOp
  have hae : ∀ {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : AEStronglyMeasurable g (volume.restrict U)),
      ∀ᵐ x ∂(volume.restrict W), χ x * hg.mk g x = g x := by
    intro g hg
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hWU hg.ae_eq_mk,
      ae_restrict_mem hWo.measurableSet] with x h1 h2
    rw [hW1 x h2, one_mul, h1]
  refine ⟨Op, W, hWo, hKW, hWU, ?_, fun x hx => funext fun i => funext fun j =>
      P.toPrincipalOn.aT_eq_of_eq_one (hW1 x hx) i j, fun i => hae (P.b_aesm i), hae P.c_aesm⟩
  exact ⟨(Classical.choice (P.toPrincipalOn.nonempty_isCkCoeff hU hχ _ rfl
    (k := 1) (by simp))).toIsC1Coeff le_rfl⟩

/-! ### Coefficients of Theorem 2 -/

/-- **Coefficients of Evans §6.3.1 Theorem 2 on an open set at order `m`.** `a^{ij}, b^i, c`
of class `C^m` on `U`, with `a^{ij}` uniformly elliptic almost everywhere on `U`. Evans's
hypothesis at order `m` is this structure at `m + 1`. Nothing is asked off `U`. -/
structure CkOpOn (d : ℕ) (U : Set (EuclideanSpace ℝ (Fin d))) (m : ℕ)
    extends PrincipalOn d U m where
  /-- The transport (first-order) coefficients. -/
  b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ
  /-- The zeroth-order coefficient. -/
  c : EuclideanSpace ℝ (Fin d) → ℝ
  /-- Every transport component is of class `C^m` on `U`. -/
  b_contDiffOn : ∀ i, ContDiffOn ℝ m (fun x => b x i) U
  /-- The zeroth-order coefficient is of class `C^m` on `U`. -/
  c_contDiffOn : ContDiffOn ℝ m c U

/-- **Localisation of the coefficients of Theorem 2.** For every compact `K ⊆ U` there are a
global operator with every coefficient of class `C^m` with bounded derivatives, packaged as
`IsCkCoeff` and `IsWkInftyLower` at order `m`, and an open `W` with `K ⊆ W ⊆ U` on which it agrees
with the given coefficients. -/
theorem exists_localOp_Ck {U : Set (EuclideanSpace ℝ (Fin d))} {m : ℕ} (P : CkOpOn d U m)
    (hU : IsOpen U) {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (Op : FullEllipticOp d) (W : Set (EuclideanSpace ℝ (Fin d))), IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
      Nonempty (IsCkCoeff Op.toEllipticCoeff m) ∧ Nonempty (IsWkInftyLower Op m) ∧
      (∀ x ∈ W, Op.a x = P.a x) ∧
      (∀ i, ∀ᵐ x ∂(volume.restrict W), Op.b x i = P.b x i) ∧
      (∀ᵐ x ∂(volume.restrict W), Op.c x = P.c x) := by
  obtain ⟨χ, hχ, hχ01, W, hWo, hKW, hcl, hW1⟩ := exists_cutoff_interior_one hU hK hKU
  have hbs : ∀ i, ContDiff ℝ ((m : ℕ) : ℕ∞) fun x => χ x * P.b x i := fun i =>
    contDiff_mul_of_contDiffOn hU hχ (n := (m : ℕ∞)) (P.b_contDiffOn i)
  have hcs : ContDiff ℝ ((m : ℕ) : ℕ∞) fun x => χ x * P.c x :=
    contDiff_mul_of_contDiffOn hU hχ (n := (m : ℕ∞)) P.c_contDiffOn
  have hbc : ∀ i, HasCompactSupport fun x => χ x * P.b x i := fun i => hasCompactSupport_mul hχ
  have hcc : HasCompactSupport fun x => χ x * P.c x := hasCompactSupport_mul hχ
  set Op := blendOp P.toPrincipalOn hU hχ hχ01 (fun x i => χ x * P.b x i)
    (fun x => χ x * P.c x) (Bs := ∑ i, ⨆ x, |χ x * P.b x i|) (Cs := ⨆ x, |χ x * P.c x|)
    (Finset.sum_nonneg fun i _ => (hbc i).iSup_abs_nonneg (hbs i).continuous)
    (hcc.iSup_abs_nonneg hcs.continuous) (fun i => (hbs i).continuous.measurable)
    hcs.continuous.measurable
    (fun i => Filter.Eventually.of_forall fun x => abs_le_sum_iSup_abs
      (f := fun i x => χ x * P.b x i) (fun i => (hbs i).continuous) hbc i x)
    (Filter.Eventually.of_forall fun x => hcc.abs_le_iSup_abs hcs.continuous x) with hOp
  have hae : ∀ g : EuclideanSpace ℝ (Fin d) → ℝ,
      ∀ᵐ x ∂(volume.restrict W), χ x * g x = g x := fun g => by
    filter_upwards [ae_restrict_mem hWo.measurableSet] with x hx
    rw [hW1 x hx, one_mul]
  exact ⟨Op, W, hWo, hKW, subset_closure.trans (hcl.trans hχ.2.2),
    P.toPrincipalOn.nonempty_isCkCoeff hU hχ _ rfl le_rfl,
    ⟨.ofBundles (fun i => Classical.choice (nonempty_isWkInfty le_rfl (hbs i) (hbc i)))
      (Classical.choice (nonempty_isWkInfty le_rfl hcs hcc))⟩,
    fun x hx => funext fun i => funext fun j =>
      P.toPrincipalOn.aT_eq_of_eq_one (hW1 x hx) i j,
    fun i => hae (fun x => P.b x i), hae P.c⟩

/-! ### Transport of the weak formulation along almost everywhere equal coefficients -/

/-- Coefficients equal on `W` almost everywhere, with a principal part equal everywhere on `W`,
give the same local weak formulation on `W`. -/
theorem LocalWeakSol.congr_ae {W : Set (EuclideanSpace ℝ (Fin d))}
    {a a' : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ}
    {b b' : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c c' f f' u : EuclideanSpace ℝ (Fin d) → ℝ} {G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (ha : ∀ i j, ∀ᵐ x ∂(volume.restrict W), a x i j = a' x i j)
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict W), b x i = b' x i)
    (hc : ∀ᵐ x ∂(volume.restrict W), c x = c' x) (hf : ∀ᵐ x ∂(volume.restrict W), f x = f' x)
    (h : LocalWeakSol W a b c f u G) : LocalWeakSol W a' b' c' f' u G := by
  intro φ hφ hφc hφW
  have e := h φ hφ hφc hφW
  have e1 : ∀ i j, ∫ x in W, a x i j * G i x * partialD j φ x
      = ∫ x in W, a' x i j * G i x * partialD j φ x := fun i j =>
    integral_congr_ae (by filter_upwards [ha i j] with x hx; rw [hx])
  have e2 : ∀ i, ∫ x in W, b x i * G i x * φ x = ∫ x in W, b' x i * G i x * φ x := fun i =>
    integral_congr_ae (by filter_upwards [hb i] with x hx; rw [hx])
  have e3 : ∫ x in W, c x * u x * φ x = ∫ x in W, c' x * u x * φ x :=
    integral_congr_ae (by filter_upwards [hc] with x hx; rw [hx])
  have e4 : ∫ x in W, f x * φ x = ∫ x in W, f' x * φ x :=
    integral_congr_ae (by filter_upwards [hf] with x hx; rw [hx])
  simp only [e1, e2, e3, e4] at e
  exact e

end EllipticPdes.Regularity
