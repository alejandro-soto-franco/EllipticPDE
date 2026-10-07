/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.Graph
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Divergence-form operators and their forms over a general inner product space

For a measure `μ` on a finite-dimensional real inner product space `E`, a bounded measurable
uniformly elliptic coefficient field `a : E → E →L[ℝ] E` gives the principal form
`⟪a ∇u, ∇v⟫` on the graph space `H1Graph μ Ω`, and a drift `b` and a potential `c` add the
lower-order terms `⟪b, ∇u⟫ v + c u v`. Coefficients enter as `L^∞` classes and act on `L²` by
Hölder multiplication, so each form is a continuous bilinear map on `H1Graph μ Ω` by
construction.

## Main declarations

* `EllipticPdes.DivForm.EllipticCoeff`, `EllipticPdes.DivForm.FullEllipticOp`: the coefficients.
* `EllipticPdes.DivForm.EllipticCoeff.form`: the principal form `⟪a ∇u, ∇v⟫`.
* `EllipticPdes.DivForm.FullEllipticOp.lowerForm`, `.form`, `.formOn`: the lower-order form, the
  full form and its restriction to a subspace such as `H1Graph.H01 μ Ω`.
* `EllipticPdes.DivForm.EllipticCoeff.form_self_ge`: `λ ‖∇u‖² ≤ ⟪a ∇u, ∇u⟫`.
* `EllipticPdes.DivForm.FullEllipticOp.form_self_ge`: the pointwise form of the Gårding bound
  before the shift is chosen.
-/

@[expose] public section

open MeasureTheory Filter
open scoped RealInnerProductSpace ENNReal

noncomputable section

namespace EllipticPdes

namespace DivForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-- A bounded measurable uniformly elliptic coefficient field `a`, with ellipticity constant
`lam` and bound `Λ`. -/
structure EllipticCoeff (μ : Measure E) where
  /-- The coefficient field. -/
  a : E → E →L[ℝ] E
  /-- The ellipticity constant. -/
  lam : ℝ
  /-- The bound on the operator norm. -/
  Λ : ℝ
  /-- The ellipticity constant is positive. -/
  lam_pos : 0 < lam
  /-- The norm bound is nonnegative. -/
  Λ_nonneg : 0 ≤ Λ
  /-- The coefficient field is almost everywhere strongly measurable. -/
  aestronglyMeasurable : AEStronglyMeasurable a μ
  /-- The operator norm of the coefficient is at most `Λ` almost everywhere. -/
  norm_le : ∀ᵐ x ∂μ, ‖a x‖ ≤ Λ
  /-- Uniform ellipticity: `⟪a x ξ, ξ⟫ ≥ lam ‖ξ‖²` almost everywhere. -/
  coercive : ∀ᵐ x ∂μ, ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪a x ξ, ξ⟫

/-- A divergence-form operator `-div (a ∇u) + ⟪b, ∇u⟫ + c u` with bounded measurable
coefficients. -/
structure FullEllipticOp (μ : Measure E) extends EllipticCoeff μ where
  /-- The drift. -/
  b : E → E
  /-- The zeroth-order coefficient. -/
  c : E → ℝ
  /-- The bound on the drift. -/
  Bsup : ℝ
  /-- The bound on the zeroth-order coefficient. -/
  Csup : ℝ
  /-- The drift bound is nonnegative. -/
  Bsup_nonneg : 0 ≤ Bsup
  /-- The bound on the zeroth-order coefficient is nonnegative. -/
  Csup_nonneg : 0 ≤ Csup
  /-- The drift is almost everywhere strongly measurable. -/
  b_aestronglyMeasurable : AEStronglyMeasurable b μ
  /-- The zeroth-order coefficient is almost everywhere strongly measurable. -/
  c_aestronglyMeasurable : AEStronglyMeasurable c μ
  /-- The drift has norm at most `Bsup` almost everywhere. -/
  norm_b_le : ∀ᵐ x ∂μ, ‖b x‖ ≤ Bsup
  /-- The zeroth-order coefficient is at most `Csup` in absolute value almost everywhere. -/
  abs_c_le : ∀ᵐ x ∂μ, |c x| ≤ Csup

variable {μ : Measure E}

open H1Graph

/-- The `L^∞` norm of the class of a function bounded almost everywhere by `C`. -/
lemma norm_toLp_top_le {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] {f : α → F}
    {ν : Measure α} {C : ℝ}
    (hf : MemLp f ∞ ν) (hC : 0 ≤ C) (h : ∀ᵐ x ∂ν, ‖f x‖ ≤ C) : ‖hf.toLp f‖ ≤ C := by
  rw [Lp.norm_toLp, eLpNorm_exponent_top hf.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hC (eLpNormEssSup_le_of_ae_bound h |>.trans (by simp))

namespace EllipticCoeff

variable (A : EllipticCoeff μ) (Ω : Set E)

/-- The coefficient field as an `L^∞` class on `Ω`. -/
def toLinfty : Lp (E →L[ℝ] E) ∞ (μ.restrict Ω) :=
  (memLp_top_of_bound A.aestronglyMeasurable.restrict A.Λ (ae_restrict_of_ae A.norm_le)).toLp A.a

/-- A representative of `toLinfty` is the coefficient field. -/
lemma coeFn_toLinfty : ⇑(A.toLinfty Ω) =ᵐ[μ.restrict Ω] A.a := MemLp.coeFn_toLp _

/-- The `L^∞` class of the coefficient field has norm at most `Λ`. -/
lemma norm_toLinfty_le : ‖A.toLinfty Ω‖ ≤ A.Λ :=
  norm_toLp_top_le _ A.Λ_nonneg (ae_restrict_of_ae A.norm_le)

/-- The pointwise action `g ↦ a g` on `L²(Ω; E)`, a Hölder product. -/
def act : Lp E 2 (μ.restrict Ω) →L[ℝ] Lp E 2 (μ.restrict Ω) :=
  (ContinuousLinearMap.id ℝ (E →L[ℝ] E)).holderL (μ.restrict Ω) ∞ 2 2 (A.toLinfty Ω)

/-- A representative of `A.act Ω g` is `x ↦ a x (g x)`. -/
lemma coeFn_act (g : Lp E 2 (μ.restrict Ω)) :
    ⇑(A.act Ω g) =ᵐ[μ.restrict Ω] fun x => A.a x (g x) := by
  have h := (ContinuousLinearMap.id ℝ (E →L[ℝ] E)).coeFn_holder (r := 2) (A.toLinfty Ω) g
  filter_upwards [h, A.coeFn_toLinfty Ω] with x hx hx'
  simpa [act, hx'] using hx

/-- The action of the coefficients on `L²(Ω; E)` has norm at most `Λ`. -/
lemma norm_act_le (g : Lp E 2 (μ.restrict Ω)) : ‖A.act Ω g‖ ≤ A.Λ * ‖g‖ := by
  have h := ContinuousLinearMap.norm_holder_apply_apply_le
    (ContinuousLinearMap.id ℝ (E →L[ℝ] E)) (r := 2) (A.toLinfty Ω) g
  have h1 : ‖ContinuousLinearMap.id ℝ (E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  calc ‖A.act Ω g‖ ≤ _ := h
    _ ≤ 1 * A.Λ * ‖g‖ := by
      have h2 := A.norm_toLinfty_le Ω
      have h3 := norm_nonneg (A.toLinfty Ω)
      have h4 := norm_nonneg g
      have h5 := norm_nonneg (ContinuousLinearMap.id ℝ (E →L[ℝ] E))
      calc _ ≤ 1 * A.Λ * ‖g‖ := by gcongr
        _ = _ := rfl
    _ = A.Λ * ‖g‖ := by ring

/-- The principal form `⟪a ∇u, ∇v⟫` on the graph space. -/
def form : H1Graph μ Ω →L[ℝ] H1Graph μ Ω →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp ((A.act Ω).comp gradL) gradL

/-- The principal form is the `L²` pairing of `a ∇u` with `∇v`. -/
lemma form_apply (U V : H1Graph μ Ω) : A.form Ω U V = ⟪A.act Ω (gradL U), gradL V⟫ := by
  simp [form]

/-- The principal form as an integral. -/
lemma form_eq_integral (U V : H1Graph μ Ω) :
    A.form Ω U V = ∫ x in Ω, ⟪A.a x (gradL U x), gradL V x⟫ ∂μ := by
  rw [form_apply, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [A.coeFn_act Ω (gradL U)] with x hx
  rw [hx]

/-- The principal form is bounded by `Λ ‖∇u‖ ‖∇v‖`. -/
lemma abs_form_le (U V : H1Graph μ Ω) :
    |A.form Ω U V| ≤ A.Λ * ‖gradL U‖ * ‖gradL V‖ := by
  rw [form_apply]
  refine (abs_real_inner_le_norm _ _).trans ?_
  gcongr
  exact A.norm_act_le Ω _

/-- Ellipticity of the coefficients bounds the principal form below by `λ ‖∇u‖²`. -/
lemma form_self_ge (U : H1Graph μ Ω) : A.lam * ‖gradL U‖ ^ 2 ≤ A.form Ω U U := by
  rw [form_eq_integral, ← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_const_mul]
  refine integral_mono_ae ((L2.integrable_inner _ _).const_mul _) ?_ ?_
  · refine ((L2.integrable_inner (A.act Ω (gradL U)) (gradL U)).congr ?_)
    filter_upwards [A.coeFn_act Ω (gradL U)] with x hx
    rw [hx]
  · filter_upwards [ae_restrict_of_ae A.coercive] with x hx
    simpa [real_inner_self_eq_norm_sq] using hx (gradL U x)

/-- The principal form is symmetric when the coefficient matrix is almost everywhere
self-adjoint. -/
lemma form_symm [FiniteDimensional ℝ E] (h : ∀ᵐ x ∂μ, (A.a x).adjoint = A.a x)
    (U V : H1Graph μ Ω) : A.form Ω U V = A.form Ω V U := by
  rw [form_eq_integral, form_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae h] with x hx
  rw [real_inner_comm, ← ContinuousLinearMap.adjoint_inner_left, hx]

end EllipticCoeff

namespace FullEllipticOp

variable (Op : FullEllipticOp μ) (Ω : Set E)

/-- The drift as an `L^∞` class of vectors. -/
def bLinfty : Lp E ∞ (μ.restrict Ω) :=
  (memLp_top_of_bound Op.b_aestronglyMeasurable.restrict Op.Bsup
    (ae_restrict_of_ae Op.norm_b_le)).toLp Op.b

/-- The zeroth-order coefficient as an `L^∞` class. -/
def cLinfty : Lp ℝ ∞ (μ.restrict Ω) :=
  (memLp_top_of_bound Op.c_aestronglyMeasurable.restrict Op.Csup
    (ae_restrict_of_ae (Op.abs_c_le.mono fun _ h => by rwa [Real.norm_eq_abs]))).toLp Op.c

/-- A representative of `bLinfty` is the drift. -/
lemma coeFn_bLinfty : ⇑(Op.bLinfty Ω) =ᵐ[μ.restrict Ω] Op.b := MemLp.coeFn_toLp _

/-- A representative of `cLinfty` is the zeroth-order coefficient. -/
lemma coeFn_cLinfty : ⇑(Op.cLinfty Ω) =ᵐ[μ.restrict Ω] Op.c := MemLp.coeFn_toLp _

/-- The `L^∞` class of the drift has norm at most `Bsup`. -/
lemma norm_bLinfty_le : ‖Op.bLinfty Ω‖ ≤ Op.Bsup :=
  norm_toLp_top_le _ Op.Bsup_nonneg (ae_restrict_of_ae Op.norm_b_le)

/-- The `L^∞` class of the zeroth-order coefficient has norm at most `Csup`. -/
lemma norm_cLinfty_le : ‖Op.cLinfty Ω‖ ≤ Op.Csup :=
  norm_toLp_top_le _ Op.Csup_nonneg
    (ae_restrict_of_ae (Op.abs_c_le.mono fun _ h => by rwa [Real.norm_eq_abs]))

/-- The map `g ↦ ⟪b, g⟫` from `L²(Ω; E)` to `L²(Ω)`. -/
def bAct : Lp E 2 (μ.restrict Ω) →L[ℝ] Lp ℝ 2 (μ.restrict Ω) :=
  (innerSL ℝ).holderL (μ.restrict Ω) ∞ 2 2 (Op.bLinfty Ω)

/-- The map `f ↦ c f` on `L²(Ω)`. -/
def cAct : Lp ℝ 2 (μ.restrict Ω) →L[ℝ] Lp ℝ 2 (μ.restrict Ω) :=
  (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).holderL (μ.restrict Ω) ∞ 2 2 (Op.cLinfty Ω)

/-- A representative of `Op.bAct Ω g` is `x ↦ ⟪b x, g x⟫`. -/
lemma coeFn_bAct (g : Lp E 2 (μ.restrict Ω)) :
    ⇑(Op.bAct Ω g) =ᵐ[μ.restrict Ω] fun x => ⟪Op.b x, g x⟫ := by
  have h := (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).coeFn_holder (r := 2) (Op.bLinfty Ω) g
  filter_upwards [h, Op.coeFn_bLinfty Ω] with x hx hx'
  exact hx.trans (by rw [hx']; rfl)

/-- A representative of `Op.cAct Ω f` is `x ↦ c x * f x`. -/
lemma coeFn_cAct (f : Lp ℝ 2 (μ.restrict Ω)) :
    ⇑(Op.cAct Ω f) =ᵐ[μ.restrict Ω] fun x => Op.c x * f x := by
  have h := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).coeFn_holder (r := 2) (Op.cLinfty Ω) f
  filter_upwards [h, Op.coeFn_cLinfty Ω] with x hx hx'
  simpa [cAct, hx'] using hx

/-- The drift acts on `L²(Ω; E)` with norm at most `Bsup`. -/
lemma norm_bAct_le (g : Lp E 2 (μ.restrict Ω)) : ‖Op.bAct Ω g‖ ≤ Op.Bsup * ‖g‖ := by
  have h := ContinuousLinearMap.norm_holder_apply_apply_le
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) (r := 2) (Op.bLinfty Ω) g
  have h1 : ‖(innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [innerSL_apply_norm, one_mul]
  have h2 := Op.norm_bLinfty_le Ω
  have h3 := norm_nonneg (Op.bLinfty Ω)
  have h4 := norm_nonneg g
  have h5 := norm_nonneg (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)
  calc ‖Op.bAct Ω g‖ ≤ _ := h
    _ ≤ 1 * Op.Bsup * ‖g‖ := by gcongr
    _ = Op.Bsup * ‖g‖ := by ring

/-- The zeroth-order coefficient acts on `L²(Ω)` with norm at most `Csup`. -/
lemma norm_cAct_le (f : Lp ℝ 2 (μ.restrict Ω)) : ‖Op.cAct Ω f‖ ≤ Op.Csup * ‖f‖ := by
  have h := ContinuousLinearMap.norm_holder_apply_apply_le
    (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)) (r := 2) (Op.cLinfty Ω) f
  have h1 : ‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)‖ ≤ 1 := ContinuousLinearMap.opNorm_lsmul_le
  have h2 := Op.norm_cLinfty_le Ω
  have h3 := norm_nonneg (Op.cLinfty Ω)
  have h4 := norm_nonneg f
  have h5 := norm_nonneg (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ))
  calc ‖Op.cAct Ω f‖ ≤ _ := h
    _ ≤ 1 * Op.Csup * ‖f‖ := by gcongr
    _ = Op.Csup * ‖f‖ := by ring

/-- The lower-order form `⟪b · ∇u, v⟫ + ⟪c u, v⟫`. -/
def lowerForm : H1Graph μ Ω →L[ℝ] H1Graph μ Ω →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp ((Op.bAct Ω).comp gradL) fnL
    + (innerSL ℝ).bilinearComp ((Op.cAct Ω).comp fnL) fnL

/-- The full form on the graph space. -/
def form : H1Graph μ Ω →L[ℝ] H1Graph μ Ω →L[ℝ] ℝ :=
  Op.toEllipticCoeff.form Ω + Op.lowerForm Ω

/-- The full form restricted to a subspace of the graph space, such as `H1Graph.H01 μ Ω`. -/
def formOn (S : Submodule ℝ (H1Graph μ Ω)) : S →L[ℝ] S →L[ℝ] ℝ :=
  (Op.form Ω).bilinearComp S.subtypeL S.subtypeL

/-- The Gårding shift. It has no dimension factor, since `‖b x‖ ≤ Bsup` bounds the vector. -/
def gardingγ : ℝ := Op.lam / 2 + Op.Csup + Op.Bsup ^ 2 / (2 * Op.lam)

/-- The Gårding shift is positive. -/
lemma gardingγ_pos : 0 < Op.gardingγ := by
  have := Op.lam_pos
  have := Op.Csup_nonneg
  unfold gardingγ
  positivity

variable {Ω}

/-- The lower-order form is the sum of the drift and zeroth-order pairings. -/
lemma lowerForm_apply (U V : H1Graph μ Ω) :
    Op.lowerForm Ω U V = ⟪Op.bAct Ω (gradL U), fnL V⟫ + ⟪Op.cAct Ω (fnL U), fnL V⟫ := by
  simp [lowerForm]

/-- The lower-order form as an integral. -/
lemma lowerForm_eq_integral (U V : H1Graph μ Ω) :
    Op.lowerForm Ω U V =
      ∫ x in Ω, (⟪Op.b x, gradL U x⟫ * fnL V x + Op.c x * fnL U x * fnL V x) ∂μ := by
  rw [lowerForm_apply, L2.inner_def, L2.inner_def,
    ← integral_add (L2.integrable_inner _ _) (L2.integrable_inner _ _)]
  refine integral_congr_ae ?_
  filter_upwards [Op.coeFn_bAct Ω (gradL U), Op.coeFn_cAct Ω (fnL U)] with x h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- The lower-order form is bounded by `Bsup ‖∇u‖ ‖v‖ + Csup ‖u‖ ‖v‖`. -/
lemma abs_lowerForm_le (U V : H1Graph μ Ω) :
    |Op.lowerForm Ω U V| ≤ Op.Bsup * ‖gradL U‖ * ‖fnL V‖ + Op.Csup * ‖fnL U‖ * ‖fnL V‖ := by
  rw [lowerForm_apply]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (abs_real_inner_le_norm _ _).trans ?_
    calc _ ≤ Op.Bsup * ‖gradL U‖ * ‖fnL V‖ := by
          gcongr
          exact Op.norm_bAct_le Ω _
      _ = _ := rfl
  · refine (abs_real_inner_le_norm _ _).trans ?_
    gcongr
    exact Op.norm_cAct_le Ω _

/-- The full form is the sum of the principal and lower-order forms. -/
lemma form_apply (U V : H1Graph μ Ω) :
    Op.form Ω U V = Op.toEllipticCoeff.form Ω U V + Op.lowerForm Ω U V := rfl

/-- The restricted form is the full form on the underlying vectors. -/
@[simp] lemma formOn_apply (S : Submodule ℝ (H1Graph μ Ω)) (u v : S) :
    Op.formOn Ω S u v = Op.form Ω u v := rfl

/-- The full form is bounded by `(Λ + Bsup + Csup) ‖U‖ ‖V‖`. -/
lemma abs_form_le (U V : H1Graph μ Ω) :
    |Op.form Ω U V| ≤ (Op.Λ + Op.Bsup + Op.Csup) * ‖U‖ * ‖V‖ := by
  rw [form_apply]
  refine (abs_add_le _ _).trans ?_
  nlinarith [Op.toEllipticCoeff.abs_form_le Ω U V, Op.abs_lowerForm_le U V, norm_gradL_le U,
    norm_gradL_le V, norm_fnL_le U, norm_fnL_le V, Op.Λ_nonneg, Op.Bsup_nonneg, Op.Csup_nonneg,
    norm_nonneg U, norm_nonneg V, norm_nonneg (gradL U), norm_nonneg (fnL U),
    norm_nonneg (fnL V), norm_nonneg (gradL V),
    mul_le_mul (norm_gradL_le U) (norm_gradL_le V) (norm_nonneg _) (norm_nonneg _),
    mul_le_mul (norm_gradL_le U) (norm_fnL_le V) (norm_nonneg _) (norm_nonneg _),
    mul_le_mul (norm_fnL_le U) (norm_fnL_le V) (norm_nonneg _) (norm_nonneg _)]

/-- The diagonal of the full form is bounded below by
`λ ‖∇u‖² - Bsup ‖∇u‖ ‖u‖ - Csup ‖u‖²`. This is the pointwise form of the Gårding bound before
the shift is chosen. -/
lemma form_self_ge (U : H1Graph μ Ω) :
    Op.lam * ‖gradL U‖ ^ 2 - Op.Bsup * ‖gradL U‖ * ‖fnL U‖ - Op.Csup * ‖fnL U‖ ^ 2
      ≤ Op.form Ω U U := by
  rw [form_apply]
  have h1 := Op.toEllipticCoeff.form_self_ge Ω U
  have h2 := Op.abs_lowerForm_le U U
  have h3 := neg_abs_le (Op.lowerForm Ω U U)
  nlinarith

/-- Without drift the lower-order form is the integral of `c u v`. -/
lemma lowerForm_eq_integral_of_b_eq_zero (hb : ∀ᵐ x ∂μ, Op.b x = 0) (U V : H1Graph μ Ω) :
    Op.lowerForm Ω U V = ∫ x in Ω, Op.c x * fnL U x * fnL V x ∂μ := by
  rw [lowerForm_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hb] with x hx
  simp [hx]

/-- Without drift and with a self-adjoint coefficient matrix, the full form is symmetric. -/
lemma form_symm [FiniteDimensional ℝ E] (ha : ∀ᵐ x ∂μ, (Op.a x).adjoint = Op.a x)
    (hb : ∀ᵐ x ∂μ, Op.b x = 0) (U V : H1Graph μ Ω) : Op.form Ω U V = Op.form Ω V U := by
  rw [form_apply, form_apply, Op.toEllipticCoeff.form_symm Ω ha U V,
    lowerForm_eq_integral_of_b_eq_zero Op hb, lowerForm_eq_integral_of_b_eq_zero Op hb]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  ring

/-- With no drift and a nonnegative zeroth-order coefficient, the full form dominates
`λ ‖∇u‖²`. -/
lemma form_self_ge_of_nonneg (hb : ∀ᵐ x ∂μ, Op.b x = 0) (hc : ∀ᵐ x ∂μ, 0 ≤ Op.c x)
    (U : H1Graph μ Ω) : Op.lam * ‖gradL U‖ ^ 2 ≤ Op.form Ω U U := by
  rw [form_apply]
  have h1 := Op.toEllipticCoeff.form_self_ge Ω U
  have h2 : 0 ≤ Op.lowerForm Ω U U := by
    rw [lowerForm_eq_integral_of_b_eq_zero Op hb]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_of_ae hc] with x hx
    have : 0 ≤ Op.c x * fnL U x * fnL U x := by
      rw [mul_assoc]; exact mul_nonneg hx (mul_self_nonneg _)
    exact this
  linarith

end FullEllipticOp

end DivForm

end EllipticPdes
