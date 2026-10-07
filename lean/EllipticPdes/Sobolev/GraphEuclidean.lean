/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.Basic
public import EllipticPdes.Sobolev.Graph

/-!
# The Euclidean bridge for the graph space

For `E = EuclideanSpace ℝ (Fin d)` and the Lebesgue measure, the general graph space
`H1Graph volume Ω = L²(Ω) × L²(Ω; E)` is isometric to the coordinate space
`Sobolev.H1amb Ω = (L²(Ω))^{d+1}`. The isometry `h1Equiv` sends `U` to the function part followed
by the coordinates of the gradient part. It maps the test graphs of `H1Graph` to the coordinate
test graphs, hence `H₀¹` to `H₀¹`, and the constraint vectors to the coordinate constraint
vectors, hence `W^{1,2}` to `W^{1,2}`.

## Main declarations

* `EllipticPdes.H1Graph.lpPiLpEquiv`: `L²(ν; ℝ^d) ≃ₗᵢ (L²(ν))^d`, componentwise.
* `EllipticPdes.H1Graph.h1Equiv`: the isometry `H1Graph volume Ω ≃ₗᵢ Sobolev.H1amb Ω`.
* `EllipticPdes.H1Graph.map_h1Equiv_H01`, `EllipticPdes.H1Graph.map_h1Equiv_W12`: the images of
  the two Sobolev subspaces.
* `EllipticPdes.H1Graph.h01Equiv`, `EllipticPdes.H1Graph.w12Equiv`: the restrictions of
  `h1Equiv` to the subspaces.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

noncomputable section

namespace EllipticPdes

set_option linter.unusedSectionVars false

namespace H1Graph

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {Ω : Set E}

omit [FiniteDimensional ℝ E] in
/-- The constraint vector is additive in the direction. -/
lemma constraintVec_add (φ : testFunctions Ω) (v w : E) :
    constraintVec μ Ω φ (v + w) = constraintVec μ Ω φ v + constraintVec μ Ω φ w := by
  refine ext ?_ ?_
  · simp only [constraintVec, fnL_add, fnL_mk]
    refine Lp.ext ?_
    filter_upwards [coeFn_partialCls (μ := μ) φ (v + w), coeFn_partialCls (μ := μ) φ v,
      coeFn_partialCls (μ := μ) φ w,
      Lp.coeFn_add (partialCls μ Ω φ v) (partialCls μ Ω φ w)] with x h1 h2 h3 h4
    rw [h4, h1, Pi.add_apply, h2, h3, map_add]
  · simp only [constraintVec, gradL_add, gradL_mk]
    refine Lp.ext ?_
    filter_upwards [coeFn_smulCls (μ := μ) φ (v + w), coeFn_smulCls (μ := μ) φ v,
      coeFn_smulCls (μ := μ) φ w,
      Lp.coeFn_add (smulCls μ Ω φ v) (smulCls μ Ω φ w)] with x h1 h2 h3 h4
    rw [h4, h1, Pi.add_apply, h2, h3, smul_add]

omit [FiniteDimensional ℝ E] in
/-- The constraint vector commutes with scalars in the direction. -/
lemma constraintVec_smul (φ : testFunctions Ω) (c : ℝ) (v : E) :
    constraintVec μ Ω φ (c • v) = c • constraintVec μ Ω φ v := by
  refine ext ?_ ?_
  · simp only [constraintVec, fnL_smul, fnL_mk]
    refine Lp.ext ?_
    filter_upwards [coeFn_partialCls (μ := μ) φ (c • v), coeFn_partialCls (μ := μ) φ v,
      Lp.coeFn_smul c (partialCls μ Ω φ v)] with x h1 h2 h4
    rw [h4, h1, Pi.smul_apply, h2, map_smul]
  · simp only [constraintVec, gradL_smul, gradL_mk]
    refine Lp.ext ?_
    filter_upwards [coeFn_smulCls (μ := μ) φ (c • v), coeFn_smulCls (μ := μ) φ v,
      Lp.coeFn_smul c (smulCls μ Ω φ v)] with x h1 h2 h4
    rw [h4, h1, Pi.smul_apply, h2, smul_comm]

variable (μ Ω) in
omit [FiniteDimensional ℝ E] in
/-- The constraint vector is linear in the direction. -/
def constraintVecₗ (φ : testFunctions Ω) : E →ₗ[ℝ] H1Graph μ Ω where
  toFun := constraintVec μ Ω φ
  map_add' := constraintVec_add φ
  map_smul' := constraintVec_smul φ

end General

variable {d : ℕ} {α : Type*} [MeasurableSpace α] (ν : Measure α)

/-- The componentwise map `L²(ν; ℝ^d) → (L²(ν))^d`. -/
def lpPiLpₗ : Lp (EuclideanSpace ℝ (Fin d)) 2 ν →ₗ[ℝ] PiLp 2 (fun _ : Fin d => Lp ℝ 2 ν) where
  toFun g := WithLp.toLp 2 (fun i => (EuclideanSpace.proj (𝕜 := ℝ) i :
    EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).compLpL 2 ν g)
  map_add' f g := by ext i : 1; simp
  map_smul' c f := by ext i : 1; simp

/-- The map `(L²(ν))^d → L²(ν; ℝ^d)` assembling coordinates, `F ↦ ∑ i, Fᵢ eᵢ`. -/
def piLpLpₗ : PiLp 2 (fun _ : Fin d => Lp ℝ 2 ν) →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin d)) 2 ν where
  toFun F := ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single i (1 : ℝ))).compLpL 2 ν (F i)
  map_add' F G := by simp [Finset.sum_add_distrib]
  map_smul' c F := by simp [Finset.smul_sum]

/-- A representative of `piLpLpₗ F` has the representatives of the `Fⱼ` as coordinates. -/
lemma coeFn_piLpLpₗ (F : PiLp 2 (fun _ : Fin d => Lp ℝ 2 ν)) :
    ⇑(piLpLpₗ ν F) =ᵐ[ν] fun a => WithLp.toLp 2 (fun j => F j a) := by
  have h2 := ae_all_iff.2 fun i : Fin d => (ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single i (1 : ℝ))).coeFn_compLpL (p := 2) (μ := ν) (F i)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => (ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single i (1 : ℝ))).compLpL 2 ν (F i)), h2] with a h1 h2
  change (∑ i, _ : Lp _ 2 ν) a = _
  rw [h1]
  ext j
  simp [h2, Pi.single_apply]


/-- The componentwise map preserves the `L²` inner product. -/
lemma inner_lpPiLpₗ (f g : Lp (EuclideanSpace ℝ (Fin d)) 2 ν) :
    ⟪lpPiLpₗ ν f, lpPiLpₗ ν g⟫ = ⟪f, g⟫ := by
  have hc : ∀ (g : Lp (EuclideanSpace ℝ (Fin d)) 2 ν) (i : Fin d),
      ⇑((lpPiLpₗ ν g) i) =ᵐ[ν] fun a => (g a) i := fun g i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).coeFn_compLp (p := 2) g
  have hi : ∀ i : Fin d, ⟪(lpPiLpₗ ν f) i, (lpPiLpₗ ν g) i⟫
      = ∫ a, (f a) i * (g a) i ∂ν := by
    intro i
    rw [L2.real_inner_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hc f i, hc g i] with a ha hb
    rw [ha, hb]
  have hint : ∀ i : Fin d, Integrable (fun a => (f a) i * (g a) i) ν := fun i =>
    (L2.integrable_mul ((lpPiLpₗ ν f) i) ((lpPiLpₗ ν g) i)).congr
      (by filter_upwards [hc f i, hc g i] with a ha hb; rw [ha, hb])
  rw [PiLp.inner_apply, L2.inner_def]
  simp_rw [hi]
  rw [← integral_finsetSum _ (fun i _ => hint i)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp [PiLp.inner_apply, mul_comm]

/-- Assembling the coordinates of `g` returns `g`. -/
lemma piLpLpₗ_lpPiLpₗ (g : Lp (EuclideanSpace ℝ (Fin d)) 2 ν) : piLpLpₗ ν (lpPiLpₗ ν g) = g := by
  refine Lp.ext ?_
  have hc : ∀ i : Fin d, ⇑((lpPiLpₗ ν g) i) =ᵐ[ν] fun a => (g a) i := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).coeFn_compLp (p := 2) g
  filter_upwards [coeFn_piLpLpₗ ν (lpPiLpₗ ν g), ae_all_iff.2 hc] with a h1 h2
  rw [h1]
  ext j
  simp [h2]

/-- The coordinates of the assembled field are the original classes. -/
lemma lpPiLpₗ_piLpLpₗ (F : PiLp 2 (fun _ : Fin d => Lp ℝ 2 ν)) : lpPiLpₗ ν (piLpLpₗ ν F) = F := by
  ext i : 1
  refine Lp.ext ?_
  have hc : ⇑((lpPiLpₗ ν (piLpLpₗ ν F)) i) =ᵐ[ν] fun a => (piLpLpₗ ν F a) i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).coeFn_compLp (p := 2) _
  filter_upwards [hc, coeFn_piLpLpₗ ν F] with a h1 h2
  rw [show (lpPiLpₗ ν (piLpLpₗ ν F)).ofLp i = _ from rfl] at h1
  rw [h1, h2]

/-- `L²(ν; ℝ^d) ≃ₗᵢ (L²(ν))^d`, componentwise. -/
def lpPiLpEquiv : Lp (EuclideanSpace ℝ (Fin d)) 2 ν ≃ₗᵢ[ℝ] PiLp 2 (fun _ : Fin d => Lp ℝ 2 ν) :=
  LinearEquiv.isometryOfInner
    { lpPiLpₗ ν with
      invFun := piLpLpₗ ν
      left_inv := piLpLpₗ_lpPiLpₗ ν
      right_inv := lpPiLpₗ_piLpLpₗ ν } (inner_lpPiLpₗ ν)


variable (Ω : Set (EuclideanSpace ℝ (Fin d)))

/-- **The Euclidean bridge.** The general graph space over `ℝ^d` with Lebesgue measure is
isometric to the coordinate space `Sobolev.H1amb Ω`. -/
def h1Equivₗ : H1Graph volume Ω ≃ₗ[ℝ] Sobolev.H1amb Ω where
  toFun U := WithLp.toLp 2 (Fin.cons (α := fun _ : Fin (d + 1) => Sobolev.L2D Ω) (fnL U)
    (fun i => lpPiLpEquiv (volume.restrict Ω) (gradL U) i))
  map_add' U V := by
    ext j : 1
    refine Fin.cases ?_ (fun i => ?_) j <;> simp
  map_smul' c U := by
    ext j : 1
    refine Fin.cases ?_ (fun i => ?_) j <;> simp
  invFun V := mk (V 0) ((lpPiLpEquiv (volume.restrict Ω)).symm (WithLp.toLp 2 fun i => V i.succ))
  left_inv U := by
    refine ext ?_ ?_
    · simp
    · simp
  right_inv V := by
    ext j : 1
    refine Fin.cases ?_ (fun i => ?_) j <;> simp


/-- The isometry between the general and the coordinate graph spaces. -/
def h1Equiv : H1Graph volume Ω ≃ₗᵢ[ℝ] Sobolev.H1amb Ω :=
  (h1Equivₗ Ω).isometryOfInner fun U V => by
    rw [Sobolev.H1amb.inner_eq, inner_eq]
    congr 1
    have : ∀ (W : H1Graph volume Ω) (i : Fin d),
        (h1Equivₗ Ω W).grad i = lpPiLpEquiv (volume.restrict Ω) (gradL W) i := fun W i => rfl
    simp only [this]
    rw [← PiLp.inner_apply, LinearIsometryEquiv.inner_map_map]

variable {Ω}

/-- The function coordinate of `h1Equiv U` is the function part of `U`. -/
@[simp] lemma h1Equiv_apply_zero (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : H1Graph volume Ω) :
    (h1Equiv Ω U) 0 = fnL U := rfl

/-- The coordinate `i.succ` of `h1Equiv U` is the `i`-th coordinate of the gradient part. -/
@[simp] lemma h1Equiv_apply_succ (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : H1Graph volume Ω)
    (i : Fin d) :
    (h1Equiv Ω U) i.succ =
      (EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).compLp (gradL U) := rfl

/-- The inverse of `h1Equiv` rebuilds the gradient from the coordinates. -/
lemma h1Equiv_symm_apply (V : Sobolev.H1amb Ω) :
    (h1Equiv Ω).symm V = mk (V 0) ((lpPiLpEquiv (volume.restrict Ω)).symm
      (WithLp.toLp 2 fun i => V i.succ)) := rfl


/-- A coordinate test function is a member of `testFunctions`. -/
lemma isTestFn_iff_mem_testFunctions {φ : EuclideanSpace ℝ (Fin d) → ℝ} :
    Sobolev.IsTestFn Ω φ ↔ φ ∈ testFunctions Ω := Iff.rfl

/-- `h1Equiv` sends the test graph of `φ` to the coordinate test graph. -/
lemma h1Equiv_testGraphₗ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : Sobolev.IsTestFn Ω φ) :
    h1Equiv Ω (testGraphₗ volume Ω ⟨φ, h⟩) = h.testGraph := by
  ext j : 1
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [Sobolev.IsTestFn.testCls, fnCls]
  · simp only [h1Equiv_apply_succ, Sobolev.IsTestFn.testGraph_succ]
    refine Lp.ext ?_
    have hc := (EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).coeFn_compLp
      (p := 2) (gradL (testGraphₗ volume Ω ⟨φ, h⟩))
    filter_upwards [hc, coeFn_gradL_testGraphₗ (μ := volume) (⟨φ, h⟩ : testFunctions Ω),
      h.coeFn_partialCls i] with x h1 h2 h3
    rw [h1, h3]
    simp only [h2, Sobolev.partialD_apply]
    rw [← inner_gradient_right, EuclideanSpace.inner_single_left]
    simp

/-- `h1Equiv` sends the constraint vector of direction `eᵢ` to the coordinate constraint
vector. -/
lemma h1Equiv_constraintVec {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : Sobolev.IsTestFn Ω φ)
    (i : Fin d) :
    h1Equiv Ω (constraintVec volume Ω ⟨φ, h⟩ (EuclideanSpace.single i 1)) =
      h.constraintVec i := by
  ext j : 1
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [h1Equiv_apply_zero]
    simp [Sobolev.IsTestFn.constraintVec, (Fin.succ_ne_zero i).symm]
    rfl
  · rw [h1Equiv_apply_succ]
    simp only [Sobolev.IsTestFn.constraintVec, PiLp.add_apply, PiLp.single_apply,
      Fin.succ_ne_zero, ite_false, zero_add, Fin.succ_inj]
    refine Lp.ext ?_
    have hc := (EuclideanSpace.proj (𝕜 := ℝ) k : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).coeFn_compLp
      (p := 2) (gradL (constraintVec volume Ω ⟨φ, h⟩ (EuclideanSpace.single i 1)))
    simp only [constraintVec, gradL_mk] at hc ⊢
    filter_upwards [hc, coeFn_smulCls (μ := volume) (⟨φ, h⟩ : testFunctions Ω)
      (EuclideanSpace.single i 1), h.coeFn_testCls, Lp.coeFn_zero ℝ 2 (volume.restrict Ω)]
      with x h1 h2 h3 h4
    rw [h1, h2]
    by_cases hk : k = i
    · subst hk
      simp [h3]
    · simp only [hk, ↓reduceIte]
      simpa [hk] using h4.symm

/-- `h1Equiv` maps `H₀¹` of the general graph space onto the coordinate `H₀¹`. -/
theorem map_h1Equiv_H01 :
    (H1Graph.H01 volume Ω).map (h1Equiv Ω).toLinearEquiv.toLinearMap = Sobolev.H01 Ω := by
  refine SetLike.coe_injective ?_
  rw [Submodule.map_coe, H01, Submodule.topologicalClosure_coe, Sobolev.coe_H01]
  change (h1Equiv Ω).toHomeomorph '' _ = _
  rw [Homeomorph.image_closure]
  congr 1
  ext V
  constructor
  · rintro ⟨_, ⟨φ, rfl⟩, rfl⟩
    exact ⟨φ, φ.2, h1Equiv_testGraphₗ φ.2⟩
  · rintro ⟨φ, h, rfl⟩
    exact ⟨_, ⟨⟨φ, h⟩, rfl⟩, h1Equiv_testGraphₗ h⟩

/-- Membership of `W^{1,2}` is preserved and reflected by `h1Equiv`. -/
lemma h1Equiv_mem_W12_iff (U : H1Graph volume Ω) :
    h1Equiv Ω U ∈ Sobolev.W12 Ω ↔ U ∈ H1Graph.W12 volume Ω := by
  rw [Sobolev.mem_W12_iff, mem_W12_iff]
  constructor
  · intro hU φ v
    have key : ∀ i : Fin d, ⟪constraintVec volume Ω φ (EuclideanSpace.single i 1), U⟫ = 0 := by
      intro i
      have h : Sobolev.IsTestFn Ω φ := φ.2
      have := hU φ h i
      rwa [← h.inner_constraintVec, ← h1Equiv_constraintVec h,
        LinearIsometryEquiv.inner_map_map] at this
    have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
      ext j
      simp [Pi.single_apply]
    rw [hv]
    change ⟪constraintVecₗ volume Ω φ _, U⟫ = 0
    rw [map_sum, sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, inner_smul_left]
    simp [constraintVecₗ, key]
  · intro hU φ h i
    rw [← h.inner_constraintVec, ← h1Equiv_constraintVec h, LinearIsometryEquiv.inner_map_map]
    exact hU ⟨φ, h⟩ _

/-- `h1Equiv` maps `W^{1,2}` of the general graph space onto the coordinate `W^{1,2}`. -/
theorem map_h1Equiv_W12 :
    (H1Graph.W12 volume Ω).map (h1Equiv Ω).toLinearEquiv.toLinearMap = Sobolev.W12 Ω := by
  ext V
  rw [Submodule.mem_map_equiv, ← h1Equiv_mem_W12_iff]
  simp

/-- The coordinate `H₀¹` is the general `H₀¹` transported by `h1Equiv`. -/
def h01Equiv (Ω : Set (EuclideanSpace ℝ (Fin d))) : Sobolev.H01 Ω ≃ₗᵢ[ℝ] H1Graph.H01 volume Ω :=
  (LinearIsometryEquiv.ofEq _ _ (map_h1Equiv_H01 (Ω := Ω))).symm.trans
    (LinearIsometryEquiv.submoduleMap (H1Graph.H01 volume Ω) (h1Equiv Ω)).symm

/-- The coordinate `W^{1,2}` is the general `W^{1,2}` transported by `h1Equiv`. -/
def w12Equiv (Ω : Set (EuclideanSpace ℝ (Fin d))) : Sobolev.W12 Ω ≃ₗᵢ[ℝ] H1Graph.W12 volume Ω :=
  (LinearIsometryEquiv.ofEq _ _ (map_h1Equiv_W12 (Ω := Ω))).symm.trans
    (LinearIsometryEquiv.submoduleMap (H1Graph.W12 volume Ω) (h1Equiv Ω)).symm

/-- `h01Equiv` is a lift of `h1Equiv⁻¹`. -/
lemma h1Equiv_h01Equiv (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : Sobolev.H01 Ω) :
    h1Equiv Ω (h01Equiv Ω U : H1Graph volume Ω) = U := by
  have := congrArg Subtype.val ((LinearIsometryEquiv.submoduleMap (H1Graph.H01 volume Ω)
    (h1Equiv Ω)).apply_symm_apply (LinearIsometryEquiv.ofEq _ _ (map_h1Equiv_H01 (Ω := Ω)).symm U))
  exact this

/-- `w12Equiv` is a lift of `h1Equiv⁻¹`. -/
lemma h1Equiv_w12Equiv (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : Sobolev.W12 Ω) :
    h1Equiv Ω (w12Equiv Ω U : H1Graph volume Ω) = U := by
  have := congrArg Subtype.val ((LinearIsometryEquiv.submoduleMap (H1Graph.W12 volume Ω)
    (h1Equiv Ω)).apply_symm_apply (LinearIsometryEquiv.ofEq _ _ (map_h1Equiv_W12 (Ω := Ω)).symm U))
  exact this

/-- The function part of `h01Equiv U` is the coordinate `0` of `U`. -/
@[simp] lemma fnL_h01Equiv (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : Sobolev.H01 Ω) :
    fnL (h01Equiv Ω U : H1Graph volume Ω) = (U : Sobolev.H1amb Ω) 0 := by
  rw [← h1Equiv_apply_zero, h1Equiv_h01Equiv]

/-- The function part of `w12Equiv U` is the coordinate `0` of `U`. -/
@[simp] lemma fnL_w12Equiv (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : Sobolev.W12 Ω) :
    fnL (w12Equiv Ω U : H1Graph volume Ω) = (U : Sobolev.H1amb Ω) 0 := by
  rw [← h1Equiv_apply_zero, h1Equiv_w12Equiv]

/-- The inclusion of the general `H₀¹` into `L²` is the function coordinate. -/
lemma embL2_h01Equiv (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : Sobolev.H01 Ω) :
    H1Graph.embL2 volume Ω (h01Equiv Ω U) = (U : Sobolev.H1amb Ω) 0 :=
  fnL_h01Equiv Ω U

/-- The squared norm of the gradient part is the sum of the squared norms of the coordinate
partial derivatives. -/
lemma norm_gradL_sq (U : H1Graph volume Ω) :
    ‖gradL U‖ ^ 2 = ∑ i : Fin d, ‖(h1Equiv Ω U) i.succ‖ ^ 2 := by
  rw [← (lpPiLpEquiv (volume.restrict Ω)).norm_map, PiLp.norm_sq_eq_of_L2]
  rfl

/-- The squared gradient norm of `h01Equiv U` is the sum of the squared coordinate norms. -/
lemma norm_gradL_h01Equiv_sq (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : Sobolev.H01 Ω) :
    ‖gradL (h01Equiv Ω U : H1Graph volume Ω)‖ ^ 2 =
      ∑ i : Fin d, ‖(U : Sobolev.H1amb Ω) i.succ‖ ^ 2 := by
  rw [norm_gradL_sq, h1Equiv_h01Equiv]

/-- The squared gradient norm of `w12Equiv U` is the sum of the squared coordinate norms. -/
lemma norm_gradL_w12Equiv_sq (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : Sobolev.W12 Ω) :
    ‖gradL (w12Equiv Ω U : H1Graph volume Ω)‖ ^ 2 =
      ∑ i : Fin d, ‖(U : Sobolev.H1amb Ω) i.succ‖ ^ 2 := by
  rw [norm_gradL_sq, h1Equiv_w12Equiv]

end H1Graph
end EllipticPdes
