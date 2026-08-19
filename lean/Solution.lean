/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import EllipticPdes

/-!
# Discharging the solvability theory from `EllipticPdes`

`Challenge.lean` states six results of §6.2 of Evans in Mathlib vocabulary alone and
leaves each one open. This module carries the same six statements, under the same names,
and proves them from `EllipticPdes`.

Comparator looks a theorem up by name in both modules and compares the two statements, so
this module restates the definitions rather than importing `Challenge`. Everything above
`toFullEllipticOp` is character-for-character the text of `Challenge.lean`, which
`verify/palomar_sync.py` checks.

Three identifications carry the statements across.

* `Palomar.H01` unfolds to `EllipticPdes.Sobolev.H01`, so the two quantify over the same
  space.
* `Palomar.EllipticOperator` carries the fields of
  `EllipticPdes.Sobolev.FullEllipticOp` flattened, and `toFullEllipticOp` rebundles them.
* `weakForm_eq`, `zerothPairing_eq` and `datumPairing_eq` identify the sums of integrals
  with `FullEllipticOp.fullBilin`, `FullEllipticOp.zerothForm` and the `L²` pairing, whose
  principal and lower-order parts are inner products of coefficient actions on `L²`.
-/

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

noncomputable section

namespace Palomar

variable {d : ℕ}

/-! ### The graph encoding of `H_0^1(Ω)` -/

/-- The real `L²` space on a domain `Ω ⊆ ℝ^d` (restricted Lebesgue measure). -/
abbrev L2D (Ω : Set (EuclideanSpace ℝ (Fin d))) : Type :=
  Lp ℝ 2 (volume.restrict Ω)

/-- Ambient Hilbert space for the graph encoding: a function value together with `d`
gradient components, carrying the ℓ² (`H¹`) inner product. Coordinate `0` is the
function; coordinate `i.succ` is the `i`-th weak partial derivative. -/
abbrev H1amb (Ω : Set (EuclideanSpace ℝ (Fin d))) : Type :=
  PiLp 2 (fun _ : Fin (d + 1) => L2D Ω)

/-- The `i`-th classical partial derivative of `φ` (a directional `fderiv`). -/
def partialD (i : Fin d) (φ : EuclideanSpace ℝ (Fin d) → ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)

/-- A smooth, compactly supported test function whose support sits inside `Ω`. -/
def IsTestFn (Ω : Set (EuclideanSpace ℝ (Fin d))) (φ : EuclideanSpace ℝ (Fin d) → ℝ) :
    Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

namespace IsTestFn

variable {Ω : Set (EuclideanSpace ℝ (Fin d))} {φ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- A test function is continuous. -/
lemma continuous (h : IsTestFn Ω φ) : Continuous φ := h.1.continuous

/-- Each partial derivative of a test function is continuous. -/
lemma continuous_partialD (h : IsTestFn Ω φ) (i : Fin d) : Continuous (partialD i φ) :=
  ((h.1.continuous_fderiv (by simp)).clm_apply continuous_const)

/-- Each partial derivative of a test function has compact support. -/
lemma hasCompactSupport_partialD (h : IsTestFn Ω φ) (i : Fin d) :
    HasCompactSupport (partialD i φ) :=
  h.2.1.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)

/-- A test function lies in `L²(Ω)`. -/
lemma mem_lp (h : IsTestFn Ω φ) : MemLp φ 2 (volume.restrict Ω) :=
  h.continuous.memLp_of_hasCompactSupport h.2.1

/-- Each partial derivative of a test function lies in `L²(Ω)`. -/
lemma memLp_partialD (h : IsTestFn Ω φ) (i : Fin d) :
    MemLp (partialD i φ) 2 (volume.restrict Ω) :=
  (h.continuous_partialD i).memLp_of_hasCompactSupport (h.hasCompactSupport_partialD i)

/-- The `L²(Ω)` class of a test function. -/
def testCls (h : IsTestFn Ω φ) : L2D Ω := h.mem_lp.toLp φ

/-- The `L²(Ω)` class of the `i`-th partial derivative of a test function. -/
def partialCls (h : IsTestFn Ω φ) (i : Fin d) : L2D Ω :=
  (h.memLp_partialD i).toLp (partialD i φ)

/-- A test function embedded as its graph `(φ, ∇φ)` in the ambient space: coordinate `0`
is the function, coordinate `i.succ` its `i`-th classical (equivalently weak) partial. -/
def testGraph (h : IsTestFn Ω φ) : H1amb Ω :=
  WithLp.toLp 2 (Fin.cons h.testCls (fun i => h.partialCls i))

end IsTestFn

/-- The set of test-function graphs over `Ω`. -/
def testGraphSet (Ω : Set (EuclideanSpace ℝ (Fin d))) : Set (H1amb Ω) :=
  { U | ∃ (φ : EuclideanSpace ℝ (Fin d) → ℝ) (h : IsTestFn Ω φ), U = h.testGraph }

/-- `H_0^1(Ω)`: the closure of the smooth compactly supported functions inside the
ambient `H¹` space. As a topological closure it is a closed, complete, real Hilbert
space. -/
def H01 (Ω : Set (EuclideanSpace ℝ (Fin d))) : Submodule ℝ (H1amb Ω) :=
  (Submodule.span ℝ (testGraphSet Ω)).topologicalClosure

/-! ### The operator and its bilinear form -/

/-- A second-order divergence-form operator
`L u = -∂_j (a_{ij} ∂_i u) + b_i ∂_i u + c u` with measurable coefficients, bounded by
`Λ`, `Bsup` and `Csup` respectively, whose principal part is uniformly elliptic with
constant `lam`. No sign condition is imposed on `c` and no smallness condition on `b`. -/
structure EllipticOperator (d : ℕ) where
  /-- The principal coefficient matrix. -/
  a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ
  /-- The transport (first-order) coefficients. -/
  b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ
  /-- The zeroth-order coefficient. -/
  c : EuclideanSpace ℝ (Fin d) → ℝ
  /-- The ellipticity constant. -/
  lam : ℝ
  /-- A uniform sup bound on the entries of `a`. -/
  Λ : ℝ
  /-- A uniform sup bound on the transport field. -/
  Bsup : ℝ
  /-- A uniform sup bound on the zeroth-order coefficient. -/
  Csup : ℝ
  /-- The ellipticity constant is strictly positive. -/
  lam_pos : 0 < lam
  /-- The sup bound on `a` is nonnegative. -/
  Λ_nonneg : 0 ≤ Λ
  /-- The sup bound on `b` is nonnegative. -/
  Bsup_nonneg : 0 ≤ Bsup
  /-- The sup bound on `c` is nonnegative. -/
  Csup_nonneg : 0 ≤ Csup
  /-- Every entry of `a` is measurable. -/
  a_meas : ∀ i j, Measurable (fun x => a x i j)
  /-- Every component of `b` is measurable. -/
  b_meas : ∀ i, Measurable (fun x => b x i)
  /-- The zeroth-order coefficient is measurable. -/
  c_meas : Measurable c
  /-- Every entry of `a` is bounded by `Λ` almost everywhere. -/
  a_bdd : ∀ i j, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |a x i j| ≤ Λ
  /-- Every component of `b` is bounded by `Bsup` almost everywhere. -/
  b_bdd : ∀ i, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |b x i| ≤ Bsup
  /-- The zeroth-order coefficient is bounded by `Csup` almost everywhere. -/
  c_bdd : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |c x| ≤ Csup
  /-- Uniform ellipticity: `∑_{ij} a_{ij}(x) ξ_i ξ_j ≥ lam |ξ|²` for almost every `x`. -/
  elliptic : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
    ∀ ξ : Fin d → ℝ, lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j

/-- The bilinear form of the operator,
`B[u, v] = ∑_{ij} ∫_Ω a_{ij} ∂_i u ∂_j v + ∑_i ∫_Ω b_i ∂_i u v + ∫_Ω c u v`,
read off the graph coordinates: `(U : H1amb Ω) 0` is `u` and `(U : H1amb Ω) i.succ` is
`∂_i u`. -/
def weakForm (Op : EllipticOperator d) (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (U V : H01 Ω) : ℝ :=
  (∑ i : Fin d, ∑ j : Fin d,
      ∫ x in Ω, Op.a x i j * ((U : H1amb Ω) i.succ x : ℝ) * ((V : H1amb Ω) j.succ x : ℝ))
    + (∑ i : Fin d,
        ∫ x in Ω, Op.b x i * ((U : H1amb Ω) i.succ x : ℝ) * ((V : H1amb Ω) 0 x : ℝ))
    + ∫ x in Ω, Op.c x * ((U : H1amb Ω) 0 x : ℝ) * ((V : H1amb Ω) 0 x : ℝ)

/-- The `L²` pairing of the function coordinates, `⟨u, v⟩ = ∫_Ω u v`. A spectral shift
`L u + μ u` enters the weak formulation through it. -/
def zerothPairing (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : H01 Ω) : ℝ :=
  ∫ x in Ω, ((U : H1amb Ω) 0 x : ℝ) * ((V : H1amb Ω) 0 x : ℝ)

/-- The pairing of an `L²(Ω)` datum against the function coordinate, `⟨f, v⟩ = ∫_Ω f v`.
An `L²` right-hand side enters the weak problem through it. -/
def datumPairing {Ω : Set (EuclideanSpace ℝ (Fin d))} (f : L2D Ω) (V : H01 Ω) : ℝ :=
  ∫ x in Ω, (f x : ℝ) * ((V : H1amb Ω) 0 x : ℝ)

/-! ### Discharging the statements from the library -/

open EllipticPdes.Sobolev in
/-- The flattened operator data of the challenge, rebundled as the library's
`FullEllipticOp`. -/
def toFullEllipticOp (Op : EllipticOperator d) : FullEllipticOp d where
  a := Op.a
  lam := Op.lam
  Λ := Op.Λ
  lam_pos := Op.lam_pos
  Λ_nonneg := Op.Λ_nonneg
  measurable := Op.a_meas
  bdd := Op.a_bdd
  elliptic := Op.elliptic
  b := Op.b
  c := Op.c
  Bsup := Op.Bsup
  Csup := Op.Csup
  Bsup_nonneg := Op.Bsup_nonneg
  Csup_nonneg := Op.Csup_nonneg
  b_meas := Op.b_meas
  c_meas := Op.c_meas
  b_bdd := Op.b_bdd
  c_bdd := Op.c_bdd

/-- The challenge's graph space is the library's. -/
lemma H01_eq (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    H01 Ω = EllipticPdes.Sobolev.H01 Ω := rfl

/-- The sum of integrals is the library's bilinear form. The principal part is
`∑ᵢⱼ ⟪aᵢⱼ ∂ᵢu, ∂ⱼv⟫`, the transport part `∑ᵢ ⟪bᵢ ∂ᵢu, v⟫` and the zeroth-order part
`⟪c u, v⟫`, and each inner product of a coefficient action against an `L²` class is the
integral of the triple product. -/
lemma weakForm_eq (Op : EllipticOperator d) (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (U V : H01 Ω) :
    weakForm Op Ω U V = (toFullEllipticOp Op).fullBilin Ω U V := by
  rw [EllipticPdes.Sobolev.FullEllipticOp.fullBilin_apply,
    EllipticPdes.Sobolev.EllipticCoeff.bilin_apply,
    EllipticPdes.Sobolev.FullEllipticOp.lowerBilin_apply, weakForm, ← add_assoc]
  simp only [EllipticPdes.Sobolev.EllipticCoeff.actL,
    EllipticPdes.Sobolev.FullEllipticOp.bAct, EllipticPdes.Sobolev.FullEllipticOp.cAct,
    EllipticPdes.Sobolev.inner_mulCoeffL_eq]
  rfl

/-- The `L²` pairing of the function coordinates is the library's zeroth-order form. -/
lemma zerothPairing_eq (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : H01 Ω) :
    zerothPairing Ω U V = EllipticPdes.Sobolev.FullEllipticOp.zerothForm Ω U V := by
  rw [EllipticPdes.Sobolev.FullEllipticOp.zerothForm_apply, zerothPairing, L2.inner_def]
  simp only [Real.inner_apply]

/-- The pairing of an `L²` datum against the function coordinate is the library's. -/
lemma datumPairing_eq {Ω : Set (EuclideanSpace ℝ (Fin d))} (f : L2D Ω) (V : H01 Ω) :
    datumPairing f V = ∫ x in Ω, (f x : ℝ) * ((V : H1amb Ω) 0 x : ℝ) := rfl

/-! ### The Gårding inequality -/

/-- **The Gårding inequality** (Evans, *Partial Differential Equations* (2nd ed.),
§6.2.2, Theorem 2, p. 318). -/
theorem garding (Op : EllipticOperator d) (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (U : H01 Ω) :
    Op.lam / 2 * ‖U‖ ^ 2
      ≤ weakForm Op Ω U U
        + (Op.lam / 2 + Op.Csup + (d : ℝ) * Op.Bsup ^ 2 / (2 * Op.lam))
            * ‖(U : H1amb Ω) 0‖ ^ 2 := by
  rw [weakForm_eq]
  exact (toFullEllipticOp Op).garding Ω U

/-! ### Existence and uniqueness for a nonnegative zeroth-order coefficient -/

/-- **First Existence Theorem for weak solutions** (Evans, §6.2.2, Theorem 3, p. 319). -/
theorem weak_solution_of_nonneg_zeroth {n : ℕ} (Op : EllipticOperator (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩb : Bornology.IsBounded Ω)
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ f : L2D Ω,
      (∃! u : H01 Ω, ∀ v : H01 Ω, weakForm Op Ω u v = datumPairing f v)
        ∧ ∀ u : H01 Ω, (∀ v : H01 Ω, weakForm Op Ω u v = datumPairing f v) →
            ‖u‖ ≤ (CP + 1) / Op.lam * ‖f‖ := by
  obtain ⟨CP, hCP, hmain⟩ :=
    EllipticPdes.Sobolev.FullEllipticOp.weak_solution_L2_of_nonneg_zeroth_of_bounded
      (toFullEllipticOp Op) hΩb hb hc
  refine ⟨CP, hCP, fun f => ⟨?_, ?_⟩⟩
  · simp only [weakForm_eq, datumPairing_eq]
    exact (hmain f).1
  · intro u hu
    simp only [weakForm_eq, datumPairing_eq] at hu
    exact (hmain f).2 u hu

/-! ### The Fredholm alternative -/

/-- **Second Existence Theorem for weak solutions** (Evans, §6.2.3, Theorem 4(i),
p. 321). -/
theorem fredholm_alternative (Op : EllipticOperator d)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) :
    (∃ u : H01 Ω, u ≠ 0 ∧ ∀ v : H01 Ω, weakForm Op Ω u v = 0)
      ∨ (∀ f : H01 Ω →L[ℝ] ℝ, ∃! u : H01 Ω,
          ∀ v : H01 Ω, weakForm Op Ω u v = f v) := by
  simp only [weakForm_eq]
  exact EllipticPdes.Sobolev.FullEllipticOp.fredholm_alternative_of_bounded
    (toFullEllipticOp Op) Ω hΩm hΩb

/-- **Solvability against the transpose problem** (Evans, §6.2.3, Theorem 4(iii),
p. 321). -/
theorem solvable_iff_orthogonal_transpose (Op : EllipticOperator d)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) (f : H01 Ω →L[ℝ] ℝ) :
    (∃ u : H01 Ω, ∀ v : H01 Ω, weakForm Op Ω u v = f v)
      ↔ ∀ w : H01 Ω, (∀ v : H01 Ω, weakForm Op Ω v w = 0) → f w = 0 := by
  have hK := (toFullEllipticOp Op).opK_isCompact Ω
    (EllipticPdes.Sobolev.embL2_isCompact hΩm hΩb)
  have hmem : ∀ w : EllipticPdes.Sobolev.H01 Ω,
      w ∈ (toFullEllipticOp Op).solSpaceStar Ω
        ↔ ∀ v : EllipticPdes.Sobolev.H01 Ω, (toFullEllipticOp Op).fullBilin Ω v w = 0 := by
    intro w
    rw [EllipticPdes.Sobolev.FullEllipticOp.solSpaceStar, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe]
    constructor
    · intro hw v
      rw [← (toFullEllipticOp Op).inner_opA Ω v w, ← ContinuousLinearMap.adjoint_inner_right,
        hw, inner_zero_right]
    · intro hw
      refine ext_inner_right (𝕜 := ℝ) (fun v => ?_)
      rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left, real_inner_comm,
        (toFullEllipticOp Op).inner_opA Ω v w, hw v]
  have hiff := (toFullEllipticOp Op).solvable_iff_orthogonal_solSpaceStar Ω hK f
  simp only [weakForm_eq]
  constructor
  · intro h w hw
    exact hiff.mp h w ((hmem w).mpr hw)
  · intro h
    exact hiff.mpr (fun w hw => h w ((hmem w).mp hw))

/-! ### The discrete set of exceptional shifts -/

/-- **Third Existence Theorem for weak solutions** (Evans, §6.2.3, Theorem 5, p. 323).
`L u = μ u + f`, so the weak form reads `B[u, v] = μ ⟨u, v⟩ + ⟨f, v⟩`. -/
theorem existence_three (Op : EllipticOperator d)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) :
    ∃ S : Set ℝ, S.Countable ∧ (∀ C : ℝ, (S ∩ Set.Iic C).Finite) ∧
      ∀ lam : ℝ, lam ∉ S ↔ ∀ f : L2D Ω, ∃! u : H01 Ω, ∀ v : H01 Ω,
        weakForm Op Ω u v = lam * zerothPairing Ω u v + datumPairing f v := by
  obtain ⟨S, hcount, hfin, hiff⟩ :=
    (toFullEllipticOp Op).existence_three_of_bounded Ω hΩm hΩb
  refine ⟨S, hcount, hfin, fun lam => ?_⟩
  simp only [weakForm_eq, zerothPairing_eq, datumPairing_eq]
  exact hiff lam

/-! ### Boundedness of the inverse -/

/-- **Boundedness of the inverse** (Evans, §6.2.3, Theorem 6, p. 324). -/
theorem resolvent_bound (Op : EllipticOperator d)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) {lam : ℝ}
    (hlam : ∀ f : H01 Ω →L[ℝ] ℝ, ∃! u : H01 Ω, ∀ v : H01 Ω,
      weakForm Op Ω u v = lam * zerothPairing Ω u v + f v) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : L2D Ω, ∀ u : H01 Ω,
      (∀ v : H01 Ω,
        weakForm Op Ω u v = lam * zerothPairing Ω u v + datumPairing f v) →
      ‖(u : H1amb Ω) 0‖ ≤ C * ‖f‖ := by
  simp only [weakForm_eq, zerothPairing_eq] at hlam
  have hnot : lam ∉ (toFullEllipticOp Op).sigmaSet Ω :=
    ((toFullEllipticOp Op).notMem_sigmaSet_iff_solvable_of_bounded Ω hΩm hΩb lam).mpr hlam
  obtain ⟨C, hC, hbound⟩ :=
    (toFullEllipticOp Op).resolvent_bound_of_bounded Ω hΩm hΩb hnot
  refine ⟨C, hC, fun f u hu => hbound f u ?_⟩
  simp only [weakForm_eq, zerothPairing_eq, datumPairing_eq,
    EllipticPdes.Sobolev.FullEllipticOp.zerothForm_apply] at hu
  exact hu

-- The proofs rest on the three axioms of classical Lean and on nothing else.
/-- info: 'Palomar.garding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Palomar.garding

/-- info: 'Palomar.weak_solution_of_nonneg_zeroth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Palomar.weak_solution_of_nonneg_zeroth

/-- info: 'Palomar.fredholm_alternative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Palomar.fredholm_alternative

/-- info: 'Palomar.solvable_iff_orthogonal_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Palomar.solvable_iff_orthogonal_transpose

/-- info: 'Palomar.existence_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Palomar.existence_three

/-- info: 'Palomar.resolvent_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Palomar.resolvent_bound

end Palomar
