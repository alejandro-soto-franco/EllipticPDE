/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.Basic
public import EllipticPdes.Sobolev.WeakDeriv
public import EllipticPdes.Embedding.WeakGradient
public import EllipticPdes.Regularity.HigherWeakDeriv

/-!
# Multi-index weak derivatives

A multi-index `α` is read as the list of directions in which it differentiates (direction `i`
repeated `α i` times). A function `v` is the `α`-th weak derivative of `u` on `U` when both are
locally integrable on `U` and `∫ u D^α φ = (-1)^{|α|} ∫ v φ` for every smooth `φ` with compact
support in `U`. The identity is stated first for a list of directions (`HasWeakDerivList`).
The convention `iterPartialD (m :: l) φ = iterPartialD l (partialD m φ)` makes induction on the
list need no commutation of partial derivatives. `HasWeakDeriv` specialises the list form to
`MultiIdx.dirs α`.

## Main declarations

* `EllipticPdes.Sobolev.MultiIdx`: multi-indices of order at most `k` in dimension `d`.
* `EllipticPdes.Sobolev.iterPartialD`: iterated classical partial derivative along a list.
* `EllipticPdes.Sobolev.HasWeakDerivList` and `EllipticPdes.Sobolev.HasWeakDeriv`: the weak
  derivative (Evans §5.2.1 Definition, p. 256).
* `EllipticPdes.Sobolev.HasWeakDeriv.ae_eq`: uniqueness almost everywhere (Evans §5.2.1
  Lemma, p. 257).
* `EllipticPdes.Sobolev.HasWeakDeriv.add` with `.smul` and `.sub`: linearity (Evans §5.2.3
  Theorem 1(ii), p. 261).
* `EllipticPdes.Sobolev.hasWeakDeriv_of_contDiff`: a smooth function has its classical
  derivative as weak derivative.
* `EllipticPdes.Sobolev.hasWeakDeriv_single_iff`: bridge to the line derivative.
* `EllipticPdes.Sobolev.hasWeakGradOn_iff_forall_hasWeakDeriv`: bridge to the weak gradient.
* `EllipticPdes.Regularity.HasIteratedWeakDerivOn.hasWeakDerivList`: bridge to the iterated
  `L²` family.

## References

* [evans-2010] L. C. Evans: *Partial Differential Equations* (2nd ed.) §5.2.1 and §5.2.3.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace EllipticPdes.Sobolev

variable {d k : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))} {l : List (Fin d)}
  {u v w u' v' φ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ### Multi-indices and iterated partial derivatives -/

/-- Multi-indices of dimension `d` and order at most `k`: exponents `α i ≤ k` with
`∑ α i ≤ k`. -/
abbrev MultiIdx (d k : ℕ) : Type := {α : Fin d → Fin (k + 1) // ∑ i, (α i : ℕ) ≤ k}

namespace MultiIdx

/-- The exponents of a multi-index as natural numbers. -/
def toFun (α : MultiIdx d k) : Fin d → ℕ := fun i => (α.1 i : ℕ)

/-- The zero multi-index. -/
def zero : MultiIdx d k := ⟨fun _ => 0, by simp⟩

/-- The directions in which a multi-index differentiates: direction `i` repeated `α i` times,
in increasing order of `i`. -/
def dirs (α : Fin d → ℕ) : List (Fin d) :=
  (List.finRange d).flatMap fun i => List.replicate (α i) i

/-- The list `dirs α` has length `|α|`. -/
theorem dirs_length (α : Fin d → ℕ) : (dirs α).length = ∑ i, α i := by
  simp [dirs, List.length_flatMap, Fin.sum_univ_def]

/-- The multi-index `Pi.single i 1` differentiates once in direction `i`. -/
theorem dirs_single (i : Fin d) : dirs (Pi.single i 1) = [i] := by
  have h : ∀ j : Fin d,
      List.replicate ((Pi.single i 1 : Fin d → ℕ) j) j = if j = i then [i] else [] := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  simp only [dirs, h]
  have key : ∀ L : List (Fin d), L.Nodup → i ∈ L →
      L.flatMap (fun j => if j = i then [i] else []) = [i] := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
      intro hnd hi
      rw [List.flatMap_cons]
      by_cases ha : a = i
      · subst ha
        have : a ∉ L := (List.nodup_cons.1 hnd).1
        have h0 : L.flatMap (fun j => if j = a then [a] else []) = [] := by
          rw [List.flatMap_eq_nil_iff]
          intro j hj
          have : j ≠ a := fun e => this (e ▸ hj)
          simp [this]
        simp [h0]
      · have hiL : i ∈ L := by simpa [Ne.symm ha] using hi
        simp [ha, ih (List.nodup_cons.1 hnd).2 hiL]
  exact key _ (List.nodup_finRange d) (List.mem_finRange i)

end MultiIdx

/-- The iterated classical partial derivative of `φ` along a list of directions. The head of
the list is applied first. -/
def iterPartialD : List (Fin d) → (EuclideanSpace ℝ (Fin d) → ℝ) →
    (EuclideanSpace ℝ (Fin d) → ℝ)
  | [], φ => φ
  | m :: l, φ => iterPartialD l (partialD m φ)

/-- Iterating along the empty list is the identity. -/
@[simp]
theorem iterPartialD_nil (φ : EuclideanSpace ℝ (Fin d) → ℝ) : iterPartialD [] φ = φ := rfl

/-- Iterating along `m :: l` applies `partialD m` first. -/
@[simp]
theorem iterPartialD_cons (m : Fin d) (l : List (Fin d)) (φ : EuclideanSpace ℝ (Fin d) → ℝ) :
    iterPartialD (m :: l) φ = iterPartialD l (partialD m φ) := rfl

/-- Iterating along a concatenation applies the first list, then the second. -/
theorem iterPartialD_append (l₁ l₂ : List (Fin d)) (φ : EuclideanSpace ℝ (Fin d) → ℝ) :
    iterPartialD (l₁ ++ l₂) φ = iterPartialD l₂ (iterPartialD l₁ φ) := by
  induction l₁ generalizing φ with
  | nil => rfl
  | cons m l ih => exact ih _

/-- A partial derivative of a test function is a test function. -/
theorem IsTestFn.partialD (h : IsTestFn U φ) (i : Fin d) :
    IsTestFn U (Sobolev.partialD i φ) :=
  ⟨(h.1.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const,
    h.hasCompactSupport_partialD i, (tsupport_partialD_subset i φ).trans h.2.2⟩

/-- An iterated partial derivative of a test function is a test function. -/
theorem IsTestFn.iterPartialD (h : IsTestFn U φ) (l : List (Fin d)) :
    IsTestFn U (Sobolev.iterPartialD l φ) := by
  induction l generalizing φ with
  | nil => exact h
  | cons m l ih => exact ih (h.partialD m)

/-- A partial derivative of a smooth function is smooth. -/
theorem contDiff_partialD (h : ContDiff ℝ (⊤ : ℕ∞) w) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (partialD i w) :=
  (h.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

/-- An iterated partial derivative of a smooth function is smooth. -/
theorem contDiff_iterPartialD (h : ContDiff ℝ (⊤ : ℕ∞) w) (l : List (Fin d)) :
    ContDiff ℝ (⊤ : ℕ∞) (iterPartialD l w) := by
  induction l generalizing w with
  | nil => exact h
  | cons m l ih => exact ih (contDiff_partialD h m)

/-! ### Integrals against test functions -/

/-- An integral over `U` of a function vanishing wherever the test function `ψ` does is the
integral over the whole space. -/
theorem setIntegral_eq_integral_of_tsupport {ψ F : EuclideanSpace ℝ (Fin d) → ℝ}
    (hs : tsupport ψ ⊆ U) (hF : ∀ x, ψ x = 0 → F x = 0) :
    ∫ x in U, F x = ∫ x, F x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
    hF x (image_eq_zero_of_notMem_tsupport fun h => hx (hs h))

/-- A function locally integrable on `U` times a continuous function with compact support in
`U` is integrable. -/
theorem integrable_mul_of_tsupport {f ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : LocallyIntegrableOn f U) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ U) : Integrable (fun x => f x * ψ x) := by
  have hK : IntegrableOn (fun x => f x * ψ x) (tsupport ψ) :=
    (hf.integrableOn_compact_subset hs hc).mul_continuousOn hψ.continuousOn hc
  exact hK.integrable_of_forall_notMem_eq_zero fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

/-- **Classical integration by parts on `U`.** For `w` smooth and `φ` a test function of `U`,
`∫_U w ∂ᵢφ = -∫_U ∂ᵢw φ`. -/
theorem setIntegral_mul_partialD (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hφ : IsTestFn U φ) (i : Fin d) :
    ∫ x in U, w x * partialD i φ x = -∫ x in U, partialD i w x * φ x := by
  have hwd : Differentiable ℝ w := hw.differentiable (by simp)
  have hpw : Continuous (partialD i w) := (contDiff_partialD hw i).continuous
  rw [setIntegral_eq_integral_of_tsupport (ψ := partialD i φ)
        ((tsupport_partialD_subset i φ).trans hφ.2.2) (fun x hx => by rw [hx, mul_zero]),
    setIntegral_eq_integral_of_tsupport (ψ := φ) hφ.2.2 (fun x hx => by rw [hx, mul_zero])]
  simp only [partialD]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hpw.mul hφ.continuous).integrable_of_hasCompactSupport hφ.hasCompactSupport.mul_left)
    ((hw.continuous.mul (hφ.continuous_partialD i)).integrable_of_hasCompactSupport
      (hφ.hasCompactSupport_partialD i).mul_left)
    ((hw.continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      hφ.hasCompactSupport.mul_left)
    (fun x _ => hwd x) (fun x _ => hφ.differentiable x)

/-! ### Weak derivative -/

/-- `v` is the weak derivative of `u` along the list `l` of directions on `U`: both are locally
integrable on `U` and `∫_U u ∂_l φ = (-1)^{|l|} ∫_U v φ` for every test function `φ` of `U`. -/
def HasWeakDerivList (U : Set (EuclideanSpace ℝ (Fin d))) (l : List (Fin d))
    (u v : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  LocallyIntegrableOn u U ∧ LocallyIntegrableOn v U ∧ ∀ φ, IsTestFn U φ →
    ∫ x in U, u x * iterPartialD l φ x = (-1) ^ l.length * ∫ x in U, v x * φ x

/-- **Weak derivative.** `v` is the `α`-th weak partial derivative of `u` on `U` when both
are locally integrable on `U` and `∫_U u D^α φ = (-1)^{|α|} ∫_U v φ` for every smooth `φ` with
compact support in `U`. Evans §5.2.1 Definition (p. 256). -/
def HasWeakDeriv (U : Set (EuclideanSpace ℝ (Fin d))) (α : Fin d → ℕ)
    (u v : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  HasWeakDerivList U (MultiIdx.dirs α) u v

namespace HasWeakDerivList

/-- A weak derivative along a list is a weak derivative along a multi-index when the list is
`dirs α`. -/
theorem hasWeakDeriv {α : Fin d → ℕ} (h : HasWeakDerivList U (MultiIdx.dirs α) u v) :
    HasWeakDeriv U α u v := h

/-- Weak derivatives along a list are unique almost everywhere on an open set. -/
theorem ae_eq (hU : IsOpen U) (h₁ : HasWeakDerivList U l u v) (h₂ : HasWeakDerivList U l u w) :
    v =ᵐ[volume.restrict U] w := by
  refine ae_eq_of_forall_integral_smul_eq (Ω := ⟨U, hU⟩) h₁.2.1 h₂.2.1 fun φ hφ hc hs => ?_
  have h := (h₁.2.2 φ ⟨hφ, hc, hs⟩).symm.trans (h₂.2.2 φ ⟨hφ, hc, hs⟩)
  have h' := mul_left_cancel₀ (pow_ne_zero l.length (neg_ne_zero.2 one_ne_zero)) h
  simp only [smul_eq_mul]
  rw [← setIntegral_eq_integral_of_tsupport (U := U) (ψ := φ) hs (fun x hx => by rw [hx, zero_mul]),
    ← setIntegral_eq_integral_of_tsupport (U := U) (ψ := φ) hs (fun x hx => by rw [hx, zero_mul])]
  simpa only [mul_comm (φ _)] using h'

/-- Weak derivatives along a list add. -/
theorem add (h₁ : HasWeakDerivList U l u v) (h₂ : HasWeakDerivList U l u' v') :
    HasWeakDerivList U l (u + u') (v + v') := by
  refine ⟨h₁.1.add h₂.1, h₁.2.1.add h₂.2.1, fun φ hφ => ?_⟩
  have hl := hφ.iterPartialD l
  have i₁ := integrable_mul_of_tsupport h₁.1 hl.continuous hl.hasCompactSupport hl.2.2
  have i₂ := integrable_mul_of_tsupport h₂.1 hl.continuous hl.hasCompactSupport hl.2.2
  have j₁ := integrable_mul_of_tsupport h₁.2.1 hφ.continuous hφ.hasCompactSupport hφ.2.2
  have j₂ := integrable_mul_of_tsupport h₂.2.1 hφ.continuous hφ.hasCompactSupport hφ.2.2
  have e₁ := h₁.2.2 φ hφ
  have e₂ := h₂.2.2 φ hφ
  simp only [Pi.add_apply, add_mul]
  rw [integral_add i₁.integrableOn i₂.integrableOn, integral_add j₁.integrableOn j₂.integrableOn,
    e₁, e₂, mul_add]

/-- Weak derivatives along a list scale. -/
theorem smul (c : ℝ) (h : HasWeakDerivList U l u v) :
    HasWeakDerivList U l (c • u) (c • v) := by
  refine ⟨h.1.smul c, h.2.1.smul c, fun φ hφ => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [integral_const_mul, integral_const_mul, h.2.2 φ hφ]
  ring

/-- Weak derivatives along a list subtract. -/
theorem sub (h₁ : HasWeakDerivList U l u v) (h₂ : HasWeakDerivList U l u' v') :
    HasWeakDerivList U l (u - u') (v - v') := by
  have := h₁.add (h₂.smul (-1))
  simpa [sub_eq_add_neg] using this

end HasWeakDerivList

namespace HasWeakDeriv

variable {α : Fin d → ℕ}

/-- **Uniqueness of weak derivatives.** Two weak `α`-th derivatives of one function agree
almost everywhere on the open set `U`. Evans §5.2.1 Lemma (p. 257). -/
theorem ae_eq (hU : IsOpen U) (h₁ : HasWeakDeriv U α u v) (h₂ : HasWeakDeriv U α u w) :
    v =ᵐ[volume.restrict U] w :=
  HasWeakDerivList.ae_eq hU h₁ h₂

/-- **Sum of weak derivatives.** The weak `α`-th derivative of a sum is the sum of the weak
derivatives. Evans §5.2.3 Theorem 1(ii) (p. 261). -/
theorem add (h₁ : HasWeakDeriv U α u v) (h₂ : HasWeakDeriv U α u' v') :
    HasWeakDeriv U α (u + u') (v + v') :=
  HasWeakDerivList.add h₁ h₂

/-- **Scalar multiple of a weak derivative.** Evans §5.2.3 Theorem 1(ii) (p. 261). -/
theorem smul (c : ℝ) (h : HasWeakDeriv U α u v) : HasWeakDeriv U α (c • u) (c • v) :=
  HasWeakDerivList.smul c h

/-- **Difference of weak derivatives.** Evans §5.2.3 Theorem 1(ii) (p. 261). -/
theorem sub (h₁ : HasWeakDeriv U α u v) (h₂ : HasWeakDeriv U α u' v') :
    HasWeakDeriv U α (u - u') (v - v') :=
  HasWeakDerivList.sub h₁ h₂

end HasWeakDeriv

/-! ### Non-vacuity -/

/-- A smooth function has the classical iterated derivative as weak derivative along any list.
The list of the classical derivative is reversed, since `iterPartialD` applies the head of the
list to the test function first. -/
theorem hasWeakDerivList_of_contDiff (hu : ContDiff ℝ (⊤ : ℕ∞) u) (l : List (Fin d)) :
    HasWeakDerivList U l u (iterPartialD l.reverse u) := by
  refine ⟨hu.continuous.locallyIntegrable.locallyIntegrableOn _,
    (contDiff_iterPartialD hu _).continuous.locallyIntegrable.locallyIntegrableOn _, ?_⟩
  intro φ hφ
  induction l generalizing φ with
  | nil => simp
  | cons m l ih =>
    have hw := contDiff_iterPartialD hu l.reverse
    rw [iterPartialD_cons, ih _ (hφ.partialD m), setIntegral_mul_partialD hw hφ m,
      List.reverse_cons, iterPartialD_append]
    simp only [List.length_cons, pow_succ]
    simp only [iterPartialD_cons, iterPartialD_nil]
    ring

/-- **Non-vacuity of the weak derivative.** A smooth function `u` has the classical derivative
`D^α u` as weak `α`-th derivative: this is the integration by parts identity that motivates
Evans §5.2.1 Definition (p. 256), applied once per direction. -/
theorem hasWeakDeriv_of_contDiff (hu : ContDiff ℝ (⊤ : ℕ∞) u) (α : Fin d → ℕ) :
    HasWeakDeriv U α u (iterPartialD (MultiIdx.dirs α).reverse u) :=
  hasWeakDerivList_of_contDiff hu _

/-! ### Bridges -/

/-- The weak derivative in one coordinate direction is the integration by parts identity
against the classical partial derivative of the test function. -/
theorem hasWeakDeriv_single_iff_integral {i : Fin d} :
    HasWeakDeriv U (Pi.single i 1) u v ↔ LocallyIntegrableOn u U ∧ LocallyIntegrableOn v U ∧
      ∀ φ, IsTestFn U φ →
        ∫ x in U, u x * partialD i φ x = -∫ x in U, v x * φ x := by
  unfold HasWeakDeriv HasWeakDerivList
  rw [MultiIdx.dirs_single]
  simp

/-- **Coordinate weak derivative as line derivative.** For the
multi-index `Pi.single i 1` the weak derivative of `U` is the distributional line derivative of
`EllipticPdes.HasWeakLineDerivOn` along the `i`-th basis vector. -/
theorem hasWeakDeriv_single_iff (hU : IsOpen U) {i : Fin d} :
    HasWeakDeriv U (Pi.single i 1) u v ↔
      HasWeakLineDerivOn ⟨U, hU⟩ (EuclideanSpace.single i 1) u v := by
  rw [hasWeakDeriv_single_iff_integral, hasWeakLineDerivOn_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  have e₁ : ∀ φ, tsupport φ ⊆ U → ∫ x in U, u x * partialD i φ x =
      ∫ x, fderiv ℝ φ x (EuclideanSpace.single i 1) • u x := fun φ hs => by
    rw [setIntegral_eq_integral_of_tsupport (ψ := partialD i φ)
      ((tsupport_partialD_subset i φ).trans hs) (fun x hx => by rw [hx, mul_zero])]
    simp [partialD, mul_comm]
  have e₂ : ∀ φ, tsupport φ ⊆ U → ∫ x in U, v x * φ x = ∫ x, φ x • v x := fun φ hs => by
    rw [setIntegral_eq_integral_of_tsupport (ψ := φ) hs (fun x hx => by rw [hx, mul_zero])]
    simp [mul_comm]
  constructor
  · intro h φ hφ hc hs
    rw [← e₁ φ hs, ← e₂ φ hs]
    exact h φ ⟨hφ, hc, hs⟩
  · intro h φ hφ
    rw [e₁ φ hφ.2.2, e₂ φ hφ.2.2]
    exact h φ hφ.1 hφ.2.1 hφ.2.2

/-- **Weak gradient as coordinate weak derivatives.** For `u` and the
components of `g` locally integrable on `U`, `g` is the weak gradient of `u` in the sense of
`EllipticPdes.Embedding.HasWeakGradOn` exactly when `g i` is the weak derivative of `u` in
direction `i` for each `i`. -/
theorem hasWeakGradOn_iff_forall_hasWeakDeriv {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : LocallyIntegrableOn u U) (hg : ∀ i, LocallyIntegrableOn (g i) U) :
    Embedding.HasWeakGradOn U u g ↔ ∀ i, HasWeakDeriv U (Pi.single i 1) u (g i) := by
  simp only [hasWeakDeriv_single_iff_integral]
  constructor
  · intro h i
    exact ⟨hu, hg i, fun φ hφ => h φ hφ.1 hφ.2.1 hφ.2.2 i⟩
  · intro h φ hφ hc hs i
    exact (h i).2.2 φ ⟨hφ, hc, hs⟩

end EllipticPdes.Sobolev

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev MeasureTheory

variable {d : ℕ} {V : Set (EuclideanSpace ℝ (Fin d))}

/-- An `L²` class on `V` is locally integrable on `V` for Lebesgue measure. -/
theorem locallyIntegrableOn_L2D (f : L2D V) : LocallyIntegrableOn f V := by
  intro x _
  have hmem : Metric.ball x 1 ∩ V ∈ nhdsWithin x V := by
    rw [inter_comm]
    exact inter_mem_nhdsWithin V (Metric.ball_mem_nhds x one_pos)
  refine ⟨Metric.ball x 1 ∩ V, hmem, ?_⟩
  have hf : MemLp f 2 (volume.restrict V) := Lp.memLp f
  have hf' : MemLp f 2 ((volume.restrict V).restrict (Metric.ball x 1)) := hf.restrict _
  rw [Measure.restrict_restrict Metric.isOpen_ball.measurableSet] at hf'
  have : IsFiniteMeasure (volume.restrict (Metric.ball x 1 ∩ V)) :=
    ⟨by simpa using lt_of_le_of_lt (measure_mono inter_subset_left) measure_ball_lt_top⟩
  exact hf'.integrable (by norm_num)

namespace HasIteratedWeakDerivOn

/-- **Iterated weak derivatives are weak derivatives along a list.** An order-`k` family of
iterated weak derivatives of `u` on `V` gives, for every list of directions of length at most
`k`, the weak derivative `h.D l` of `u` along that list. -/
theorem hasWeakDerivList {k : ℕ} {l : List (Fin d)} {u : L2D V}
    (h : HasIteratedWeakDerivOn V k u) (hl : l.length ≤ k) :
    HasWeakDerivList V l (u : EuclideanSpace ℝ (Fin d) → ℝ) (h.D l) := by
  refine ⟨locallyIntegrableOn_L2D u, locallyIntegrableOn_L2D (h.D l), ?_⟩
  have key : ∀ (l : List (Fin d)), l.length ≤ k → ∀ φ, IsTestFn V φ →
      ∫ x in V, (h.D [] x : ℝ) * iterPartialD l φ x =
        (-1) ^ l.length * ∫ x in V, (h.D l x : ℝ) * φ x := by
    intro l
    induction l with
    | nil => intro _ φ _; simp
    | cons m α ih =>
      intro hlen φ hφ
      rw [iterPartialD_cons, ih (Nat.le_of_succ_le hlen) _ (hφ.partialD m),
        h.D_step m α hlen φ hφ.1 hφ.2.1 hφ.2.2]
      simp only [List.length_cons, pow_succ]
      ring
  intro φ hφ
  have := key l hl φ hφ
  rwa [h.D_nil] at this

end HasIteratedWeakDerivOn

end EllipticPdes.Regularity
