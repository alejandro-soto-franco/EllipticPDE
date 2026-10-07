/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Fredholm.CompactOperator
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# Fredholm alternative for an abstract Gårding form

Evans §6.2.3, Theorem 4.

A `GardingForm V L` is a bounded bilinear form `B` on a real Hilbert space `V` with a bounded
map `emb : V →L[ℝ] L` into a Hilbert space `L` such that `B` is coercive modulo `emb`:
`β ‖u‖² ≤ B[u, u] + γ ‖emb u‖²`. The shifted form `B + γ ⟪emb ·, emb ·⟫` is coercive, so
Lax-Milgram makes it an equivalence `opE`, and the Riesz operator `opA` of `B` factors as
`opA = opE ∘ (1 - opK)` with `opK = γ · opE⁻¹ · opT` and `opT = emb† emb`. When `emb` is compact
so is `opK`, and Riesz theory (`CompactOperator.lean`) gives:

* `solSpace`, the weak solutions of `B[u, ·] = 0`, is the eigenspace of `opK` at `1`, hence finite
  dimensional (`finiteDimensional_solSpace`);
* `opA` has closed range, and `B[u, ·] = f` is solvable exactly when `f` annihilates `solSpaceStar`,
  the weak solutions of the transpose problem (`solvable_iff_orthogonal_solSpaceStar`);
* `dim solSpaceStar = dim solSpace` (`finrank_solSpaceStar_eq_finrank_solSpace`);
* the Fredholm alternative (`fredholm_alternative`).

The elliptic Dirichlet problem is an instance with `V = H₀¹(Ω)`, `L = L²(Ω)`.
-/

@[expose] public section

open InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes

/-- A bounded bilinear form `form` on a real Hilbert space `V`, coercive modulo a bounded map
`emb` into a real Hilbert space `L` (the Gårding inequality with constants `β` and `γ`). -/
structure GardingForm (V L : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [NormedAddCommGroup L] [InnerProductSpace ℝ L] [CompleteSpace L] where
  /-- The bounded bilinear form. -/
  form : V →L[ℝ] V →L[ℝ] ℝ
  /-- The bounded map into the space in which the form is lower order. -/
  emb : V →L[ℝ] L
  /-- The coercivity constant. -/
  β : ℝ
  /-- The shift constant. -/
  γ : ℝ
  /-- The coercivity constant is positive. -/
  β_pos : 0 < β
  /-- The shift constant is positive. -/
  γ_pos : 0 < γ
  /-- The Gårding inequality `β ‖u‖² ≤ B[u, u] + γ ‖emb u‖²`. -/
  garding : ∀ u, β * ‖u‖ ^ 2 ≤ form u u + γ * ‖emb u‖ ^ 2

namespace GardingForm

variable {V L : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup L] [InnerProductSpace ℝ L] [CompleteSpace L] (G : GardingForm V L)

/-! ### The shifted form and the Riesz operators -/

/-- The shifted form `B[u, v] + γ ⟪emb u, emb v⟫`. -/
def shifted : V →L[ℝ] V →L[ℝ] ℝ :=
  G.form + G.γ • ((innerSL ℝ).bilinearComp G.emb G.emb : V →L[ℝ] V →L[ℝ] ℝ)

/-- `shifted u v = B[u, v] + γ ⟪emb u, emb v⟫`. -/
lemma shifted_apply (u v : V) :
    G.shifted u v = G.form u v + G.γ * ⟪G.emb u, G.emb v⟫ := by
  simp [shifted]

/-- The shifted form is coercive with constant `β`. -/
theorem shifted_coercive : IsCoercive G.shifted := by
  refine ⟨G.β, G.β_pos, fun u => ?_⟩
  rw [shifted_apply, real_inner_self_eq_norm_sq]
  calc G.β * ‖u‖ * ‖u‖ = G.β * ‖u‖ ^ 2 := by ring
    _ ≤ G.form u u + G.γ * ‖G.emb u‖ ^ 2 := G.garding u

/-- The Riesz representative of `⟪emb u, emb v⟫` as an operator on `V`. -/
def opT : V →L[ℝ] V :=
  continuousLinearMapOfBilin ((innerSL ℝ).bilinearComp G.emb G.emb : V →L[ℝ] V →L[ℝ] ℝ)

/-- Riesz identity: `⟪opT u, v⟫ = ⟪emb u, emb v⟫`. -/
lemma inner_opT (u v : V) : ⟪G.opT u, v⟫ = ⟪G.emb u, G.emb v⟫ :=
  continuousLinearMapOfBilin_apply _ u v

/-- The operator `opT` factors through the embedding: `opT = emb† ∘ emb`. -/
lemma opT_eq_adjoint_comp : G.opT = G.emb.adjoint.comp G.emb := by
  refine ContinuousLinearMap.ext (fun u => ext_inner_right (𝕜 := ℝ) (fun v => ?_))
  rw [G.inner_opT, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]

/-- The Riesz representative of the form `B` as an operator on `V`: `⟪opA u, v⟫ = B[u, v]`. -/
def opA : V →L[ℝ] V := continuousLinearMapOfBilin G.form

/-- Riesz identity: `⟪opA u, v⟫ = B[u, v]`. -/
lemma inner_opA (u v : V) : ⟪G.opA u, v⟫ = G.form u v :=
  continuousLinearMapOfBilin_apply G.form u v

/-- The coercive Lax-Milgram equivalence of the shifted form. -/
def opE : V ≃L[ℝ] V := G.shifted_coercive.continuousLinearEquivOfBilin

/-- Riesz identity: `⟪opE u, v⟫ = B[u, v] + γ ⟪emb u, emb v⟫`. -/
lemma inner_opE (u v : V) : ⟪G.opE u, v⟫ = G.shifted u v :=
  G.shifted_coercive.continuousLinearEquivOfBilin_apply u v

/-! ### Reduction to `1 - opK` -/

/-- `opA = opE - γ · opT`: subtracting the shift recovers the unshifted form. -/
lemma opA_eq : G.opA = (G.opE : V →L[ℝ] V) - G.γ • G.opT := by
  refine ContinuousLinearMap.ext (fun u => ext_inner_right (𝕜 := ℝ) (fun v => ?_))
  rw [_root_.sub_apply, _root_.smul_apply, inner_sub_left,
    real_inner_smul_left, ContinuousLinearEquiv.coe_coe, G.inner_opA, G.inner_opE,
    G.inner_opT, G.shifted_apply]
  ring

/-- The compact part of the reduction: `opK = γ · opE⁻¹ · opT`. -/
def opK : V →L[ℝ] V := G.γ • ((G.opE.symm : V →L[ℝ] V).comp G.opT)

/-- `opA = opE ∘ (1 - opK)`. -/
lemma opA_factor : G.opA = (G.opE : V →L[ℝ] V).comp (1 - G.opK) := by
  have hcomp : (G.opE : V →L[ℝ] V).comp (1 - G.opK) = (G.opE : V →L[ℝ] V) - G.γ • G.opT := by
    refine ContinuousLinearMap.ext (fun u => ?_)
    simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply,
      one_apply_eq_self, _root_.smul_apply, opK,
      ContinuousLinearEquiv.coe_coe, map_sub, map_smul, ContinuousLinearEquiv.apply_symm_apply]
  rw [G.opA_eq, hcomp]

/-- The weak problem `B[u, ·] = f` is the equation `opA u = g` for the Riesz representative `g`
of `f`. -/
lemma opA_eq_toDual_symm_iff (f : V →L[ℝ] ℝ) (u : V) :
    G.opA u = (InnerProductSpace.toDual ℝ V).symm f ↔ ∀ v : V, G.form u v = f v := by
  have hg : ∀ v, ⟪(InnerProductSpace.toDual ℝ V).symm f, v⟫ = f v := fun v =>
    InnerProductSpace.toDual_symm_apply
  constructor
  · intro hu v
    rw [← G.inner_opA u v, hu, hg]
  · intro hu
    refine ext_inner_right (𝕜 := ℝ) (fun v => ?_)
    rw [G.inner_opA u v, hu v, hg]

/-! ### Compactness -/

/-- If the embedding is compact, so is `opT`. -/
lemma opT_isCompact (hK : IsCompactOperator G.emb) : IsCompactOperator G.opT := by
  rw [G.opT_eq_adjoint_comp]
  exact hK.clm_comp G.emb.adjoint

/-- If the embedding is compact, so is `opK = γ · opE⁻¹ · opT`. -/
lemma opK_isCompact (hK : IsCompactOperator G.emb) : IsCompactOperator G.opK :=
  ((G.opT_isCompact hK).clm_comp (G.opE.symm : V →L[ℝ] V)).smul G.γ

/-! ### The homogeneous problem and the transpose problem -/

/-- The space of weak solutions of the homogeneous problem: the kernel of `opA`. -/
def solSpace : Submodule ℝ V := LinearMap.ker G.opA.toLinearMap

/-- Membership in `solSpace` means `B[u, v] = 0` for every `v`. -/
lemma mem_solSpace_iff (u : V) : u ∈ G.solSpace ↔ ∀ v : V, G.form u v = 0 := by
  rw [solSpace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro hu v
    rw [← G.inner_opA u v, hu, inner_zero_left]
  · intro hu
    refine ext_inner_right (𝕜 := ℝ) (fun v => ?_)
    rw [G.inner_opA u v, hu v, inner_zero_left]

/-- The homogeneous solution space is the eigenspace of `opK` at the eigenvalue `1`. -/
lemma solSpace_eq_eigenspace : G.solSpace = Module.End.eigenspace G.opK.toLinearMap 1 := by
  ext u
  rw [solSpace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    Module.End.mem_eigenspace_iff, one_smul]
  have hfac : G.opA u = G.opE ((1 - G.opK) u) := by
    rw [G.opA_factor]; rfl
  constructor
  · intro hu
    have h0 : (1 - G.opK) u = 0 := by
      apply G.opE.injective
      rw [← hfac, hu, map_zero]
    rw [_root_.sub_apply, one_apply_eq_self, sub_eq_zero] at h0
    exact h0.symm
  · intro hu
    have h0 : (1 - G.opK) u = 0 := by
      rw [_root_.sub_apply, one_apply_eq_self,
        show G.opK u = u from hu, sub_self]
    rw [hfac, h0, map_zero]

/-- The homogeneous solution space is finite dimensional when the embedding is compact. -/
theorem finiteDimensional_solSpace (hK : IsCompactOperator G.opK) :
    FiniteDimensional ℝ G.solSpace := by
  rw [solSpace_eq_eigenspace]
  exact ContinuousLinearMap.finite_dimensional_eigenspace hK 1 one_ne_zero

/-- The range of `opA` is closed when `opK` is compact: `opA = opE ∘ (1 - opK)` with `opE` a
homeomorphism and `1 - opK` of closed range. -/
theorem isClosed_range_opA (hK : IsCompactOperator G.opK) : IsClosed (Set.range G.opA) := by
  have h1 : IsClosed (Set.range (1 - G.opK : V →L[ℝ] V)) := hK.isClosed_range_one_sub
  have h2 : Set.range G.opA = G.opE '' Set.range (1 - G.opK : V →L[ℝ] V) := by
    rw [G.opA_factor, ContinuousLinearMap.coe_comp, Set.range_comp]
    rfl
  rw [h2]
  exact G.opE.toHomeomorph.isClosedMap _ h1

/-- The space of weak solutions of the transpose problem: the kernel of the Hilbert adjoint of
`opA`. -/
def solSpaceStar : Submodule ℝ V := LinearMap.ker (ContinuousLinearMap.adjoint G.opA).toLinearMap

/-- Membership in `solSpaceStar` means `B[v, u] = 0` for every `v`. -/
lemma mem_solSpaceStar_iff (u : V) : u ∈ G.solSpaceStar ↔ ∀ v : V, G.form v u = 0 := by
  rw [solSpaceStar, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro hu v
    rw [← G.inner_opA v u, ← ContinuousLinearMap.adjoint_inner_right, hu, inner_zero_right]
  · intro hu
    refine ext_inner_right (𝕜 := ℝ) (fun v => ?_)
    rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left, real_inner_comm,
      G.inner_opA v u]
    exact hu v

/-- **Solvability criterion** (Evans §6.2.3, Theorem 4(iii)): `B[u, ·] = f` has a solution
exactly when `f` annihilates every weak solution of the transpose problem. -/
theorem solvable_iff_orthogonal_solSpaceStar (hK : IsCompactOperator G.opK) (f : V →L[ℝ] ℝ) :
    (∃ u : V, ∀ v : V, G.form u v = f v) ↔ ∀ w ∈ G.solSpaceStar, f w = 0 := by
  set g : V := (InnerProductSpace.toDual ℝ V).symm f with hg
  have hgrep : ∀ v : V, ⟪g, v⟫ = f v := fun v => InnerProductSpace.toDual_symm_apply
  have hiff : (∃ u : V, ∀ v : V, G.form u v = f v) ↔ g ∈ LinearMap.range G.opA.toLinearMap := by
    rw [LinearMap.mem_range]
    exact exists_congr fun u => (G.opA_eq_toDual_symm_iff f u).symm
  rw [hiff, ContinuousLinearMap.range_eq_orthogonal_ker_adjoint _ (G.isClosed_range_opA hK),
    Submodule.mem_orthogonal]
  constructor
  · intro h w hw
    rw [← hgrep w, real_inner_comm]
    exact h w hw
  · intro h w hw
    rw [real_inner_comm, hgrep w]
    exact h w hw

/-- **`dim N* = dim N`** (Evans §6.2.3, Theorem 4(ii)): the homogeneous problem and the
transpose problem have solution spaces of the same dimension. -/
theorem finrank_solSpaceStar_eq_finrank_solSpace (hK : IsCompactOperator G.opK) :
    Module.finrank ℝ G.solSpaceStar = Module.finrank ℝ G.solSpace := by
  rw [solSpaceStar, ContinuousLinearMap.finrank_ker_adjoint_of_eq_comp_equiv G.opE
    G.opA_factor, hK.finrank_ker_one_sub_adjoint_eq,
    ContinuousLinearMap.ker_one_sub_eq_eigenspace, ← G.solSpace_eq_eigenspace]

/-! ### The Fredholm alternative -/

/-- **Fredholm alternative** (Evans §6.2.3, Theorem 4): if `opK` is compact, either the
homogeneous problem has a nontrivial weak solution, or `B[u, ·] = f` has a unique solution for
every continuous functional `f`. -/
theorem fredholm_alternative (hK : IsCompactOperator G.opK) :
    (∃ u : V, u ≠ 0 ∧ ∀ v : V, G.form u v = 0)
      ∨ (∀ f : V →L[ℝ] ℝ, ∃! u : V, ∀ v : V, G.form u v = f v) := by
  rcases hK.fredholm_dichotomy with h | ⟨u, hu0, hu⟩
  · right
    intro f
    refine (existsUnique_congr fun u => ?_).mp
      (h (G.opE.symm ((InnerProductSpace.toDual ℝ V).symm f)))
    rw [← G.opA_eq_toDual_symm_iff f u, G.opE.eq_symm_apply, G.opA_factor]
    exact Iff.rfl
  · left
    refine ⟨u, hu0, (G.mem_solSpace_iff u).1 ?_⟩
    rw [solSpace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, G.opA_factor,
      ContinuousLinearMap.comp_apply, hu, map_zero]

/-- If the homogeneous problem has only the trivial weak solution and `opK` is compact, then
`B[u, ·] = f` has a unique solution for every `f`. -/
theorem fredholm_unique_imp_exists (hK : IsCompactOperator G.opK)
    (huniq : ∀ u : V, (∀ v : V, G.form u v = 0) → u = 0) (f : V →L[ℝ] ℝ) :
    ∃! u : V, ∀ v : V, G.form u v = f v := by
  rcases G.fredholm_alternative hK with ⟨u, hu_ne, hu_hom⟩ | hexists
  · exact absurd (huniq u hu_hom) hu_ne
  · exact hexists f

end GardingForm

end EllipticPdes
