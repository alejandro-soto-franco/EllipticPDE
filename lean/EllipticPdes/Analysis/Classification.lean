/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Analysis.FunctionSpaces
public import EllipticPdes.Sobolev.WkpBridge

/-!
# Classification of partial differential equations

Evans writes a `k`-th order partial differential equation as
`F(D^k u, D^{k-1} u, …, Du, u, x) = 0` and sorts it into four classes by the way `F` depends
on the derivatives. This file states the four classes
as properties of the function `F`. The derivatives of `u` at `x` form a jet, a real function
on the multi-indices of order at most `k`. By the symmetry of second derivatives this jet
determines Evans's arrays `D^j u` for `u` of class `C^k`.

## Main declarations

* `EllipticPdes.Analysis.Jet`: the values `D^α u(x)` for the multi-indices `|α| ≤ k`.
* `EllipticPdes.Analysis.IsSolution`: `u` solves `F(D^k u, …, u, x) = 0` on `U`.
* `EllipticPdes.Analysis.IsLinear`, `IsSemilinear`, `IsQuasilinear`, `IsFullyNonlinear`:
  the four classes of equation.
* `EllipticPdes.Analysis.isSolution_iff_of_isLinear`: a linear equation reads
  `∑ a_α D^α u = f` on `U`.
* `EllipticPdes.Analysis.IsLinear.isSemilinear`, `IsSemilinear.isQuasilinear`: the classes
  are nested.
* `EllipticPdes.Analysis.isFullyNonlinear_sq`: `(∂ᵢu)² = 0` is fully nonlinear.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §1.1 (definition of a partial
differential equation, p. 1, and of the four classes of equation, p. 2).
-/

@[expose] public section

noncomputable section

namespace EllipticPdes.Analysis

variable {d k : ℕ}

/-- The jet of order `k`: the values `D^α u(x)` for the multi-indices of order at most `k`. -/
abbrev Jet (d k : ℕ) : Type := Sobolev.MultiIdx d k → ℝ

/-- The jet of `u` at `x`, with entries `D^α u(x)`. -/
def jet (k : ℕ) (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : Jet d k :=
  fun α => classicalDeriv α u x

/-- The restriction of a jet to the multi-indices of order below `k`. -/
def Jet.lower (j : Jet d k) : {α : Sobolev.MultiIdx d k // α.order < k} → ℝ :=
  fun α => j α.1

/-- **Solution of a partial differential equation.** `u` solves
`F(D^k u(x), …, Du(x), u(x), x) = 0` for every `x ∈ U`.
Evans §1.1 Def (partial differential equation) (p. 1). -/
def IsSolution (F : Jet d k → EuclideanSpace ℝ (Fin d) → ℝ) (U : Set (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ x ∈ U, F (jet k u x) x = 0

/-- **Linear equation.** `F = ∑ a_α(x) D^α u - f(x)`.
Evans §1.1 Def (linear, semilinear, quasilinear, fully nonlinear) (p. 2). -/
def IsLinear (F : Jet d k → EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∃ (a : Sobolev.MultiIdx d k → EuclideanSpace ℝ (Fin d) → ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ),
    ∀ j x, F j x = ∑ α, a α x * j α - f x

/-- **Semilinear equation.** `F = ∑_{|α|=k} a_α(x) D^α u + a₀(D^{k-1}u, …, u, x)`.
Evans §1.1 Def (linear, semilinear, quasilinear, fully nonlinear) (p. 2). -/
def IsSemilinear (F : Jet d k → EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∃ (a : Sobolev.MultiIdx d k → EuclideanSpace ℝ (Fin d) → ℝ)
    (a₀ : ({α : Sobolev.MultiIdx d k // α.order < k} → ℝ) → EuclideanSpace ℝ (Fin d) → ℝ),
    ∀ j x, F j x = ∑ α with α.order = k, a α x * j α + a₀ j.lower x

/-- **Quasilinear equation.** `F = ∑_{|α|=k} a_α(D^{k-1}u, …, u, x) D^α u
+ a₀(D^{k-1}u, …, u, x)`.
Evans §1.1 Def (linear, semilinear, quasilinear, fully nonlinear) (p. 2). -/
def IsQuasilinear (F : Jet d k → EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∃ (a : Sobolev.MultiIdx d k → ({α : Sobolev.MultiIdx d k // α.order < k} → ℝ) →
      EuclideanSpace ℝ (Fin d) → ℝ)
    (a₀ : ({α : Sobolev.MultiIdx d k // α.order < k} → ℝ) → EuclideanSpace ℝ (Fin d) → ℝ),
    ∀ j x, F j x = ∑ α with α.order = k, a α j.lower x * j α + a₀ j.lower x

/-- **Fully nonlinear equation.** `F` depends nonlinearly on the derivatives of highest order,
which is the negation of being quasilinear.
Evans §1.1 Def (linear, semilinear, quasilinear, fully nonlinear) (p. 2). -/
def IsFullyNonlinear (F : Jet d k → EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ¬ IsQuasilinear F

/-- A solution of a linear equation satisfies `∑ a_α D^α u = f` on `U`, and conversely.
Evans §1.1 Def (partial differential equation) (p. 1). -/
theorem isSolution_iff_of_isLinear {F : Jet d k → EuclideanSpace ℝ (Fin d) → ℝ}
    {a : Sobolev.MultiIdx d k → EuclideanSpace ℝ (Fin d) → ℝ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hF : ∀ j x, F j x = ∑ α, a α x * j α - f x)
    {U : Set (EuclideanSpace ℝ (Fin d))} {u : EuclideanSpace ℝ (Fin d) → ℝ} :
    IsSolution F U u ↔ ∀ x ∈ U, ∑ α, a α x * classicalDeriv α u x = f x := by
  unfold IsSolution
  refine forall₂_congr fun x _ => ?_
  rw [hF, sub_eq_zero]
  rfl

/-- Every linear equation is semilinear.
Evans §1.1 Def (linear, semilinear, quasilinear, fully nonlinear) (p. 2). -/
theorem IsLinear.isSemilinear {F : Jet d k → EuclideanSpace ℝ (Fin d) → ℝ} (h : IsLinear F) :
    IsSemilinear F := by
  obtain ⟨a, f, hF⟩ := h
  refine ⟨a, fun l x => (∑ α : {α : Sobolev.MultiIdx d k // α.order < k},
    a α.1 x * l α) - f x, fun j x => ?_⟩
  rw [hF]
  have hsplit : ∑ α, a α x * j α = ∑ α with α.order = k, a α x * j α +
      ∑ α with ¬ α.order = k, a α x * j α := (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hlow : ∑ α with ¬ α.order = k, a α x * j α =
      ∑ α : {α : Sobolev.MultiIdx d k // α.order < k}, a α.1 x * j.lower α := by
    have hmem : ∀ α : Sobolev.MultiIdx d k, α ∈ ({α | ¬ α.order = k} : Finset _) ↔
        α.order < k := by
      intro α
      have hle : α.order ≤ k := by
        have := α.2
        simpa [Sobolev.MultiIdx.order] using this
      simp [lt_iff_le_and_ne, hle]
    exact Finset.sum_subtype _ hmem (fun α => a α x * j α)
  rw [hsplit, hlow]
  ring

/-- Every semilinear equation is quasilinear.
Evans §1.1 Def (linear, semilinear, quasilinear, fully nonlinear) (p. 2). -/
theorem IsSemilinear.isQuasilinear {F : Jet d k → EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsSemilinear F) : IsQuasilinear F := by
  obtain ⟨a, a₀, hF⟩ := h
  exact ⟨fun α _ x => a α x, a₀, hF⟩

/-- The equation `(∂ᵢu)² = 0` of first order is fully nonlinear.
Evans §1.1 Def (linear, semilinear, quasilinear, fully nonlinear) (p. 2). -/
theorem isFullyNonlinear_sq (i : Fin d) :
    IsFullyNonlinear (k := 1) (fun j _ => j (Sobolev.MultiIdx.single i) ^ 2) := by
  rintro ⟨a, a₀, hF⟩
  have hord : (Sobolev.MultiIdx.single i).order = 1 := by
    unfold Sobolev.MultiIdx.order Sobolev.MultiIdx.single
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  -- The jet with value `t` in slot `i` and zero elsewhere.
  let J : ℝ → Jet d 1 := fun t α => if α = Sobolev.MultiIdx.single i then t else 0
  have hlow : ∀ t, (J t).lower = (J 0).lower := by
    intro t
    funext α
    have hne : α.1 ≠ Sobolev.MultiIdx.single i := by
      intro h
      have := α.2
      rw [h, hord] at this
      omega
    simp [Jet.lower, J, hne]
  have hval : ∀ t, ∀ x, (t ^ 2 : ℝ) =
      a (Sobolev.MultiIdx.single i) (J 0).lower x * t + a₀ (J 0).lower x := by
    intro t x
    have h := hF (J t) x
    have hsum : ∑ α : Sobolev.MultiIdx d 1 with α.order = 1,
        a α (J t).lower x * J t α = a (Sobolev.MultiIdx.single i) (J t).lower x * t := by
      rw [Finset.sum_eq_single (Sobolev.MultiIdx.single i)]
      · simp [J]
      · intro α _ hα
        simp [J, hα]
      · intro hn
        exact absurd (by simp [hord]) hn
    rw [hsum, hlow] at h
    simpa [J] using h
  have h1 := hval 1 0
  have h0 := hval 0 0
  have h2 := hval (-1) 0
  nlinarith

end EllipticPdes.Analysis
