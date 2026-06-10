import EllipticDirichlet.Fredholm
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Towards the complete Fredholm theory (Guo Theorem VII.4.4)

`Fredholm.lean` reduces the weak problem `Lu = f` to the compact-operator equation
`(1 - opK)u = h` through the factorisation `opA = opE ∘ (1 - opK)` and derives the
dichotomy. This module begins the *quantitative* part of Guo Theorem VII.4.4: the space

  `N = {u ∈ H₀¹(Ω) : B[u, v] = 0 for all v}`

of weak solutions of the homogeneous problem is **finite-dimensional**. Since `opE` is a
continuous linear equivalence, `N = ker(opA) = ker(1 - opK)` is the eigenspace of the
compact operator `opK` at the eigenvalue `1`, and eigenspaces of compact operators at
nonzero eigenvalues are finite-dimensional
(`ContinuousLinearMap.finite_dimensional_eigenspace`, the Riesz theory input).

Remaining for the full VII.4.4/VII.4.7 statement (planned here): closed range of
`1 - opK`, the adjoint problem via the transpose form `B(·, v)`, the solvability
criterion `Lu = f` solvable ⟺ `f ⊥ N*`, and `dim N = dim N*`.
-/

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticDirichlet.Sobolev

/-! ### Generic Riesz theory: `1 - K` for a compact operator on a real Hilbert space -/

section RieszTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {K : E →L[ℝ] E}

omit [CompleteSpace E] in
/-- The kernel of `1 - K` is the eigenspace of `K` at the eigenvalue `1`. -/
lemma ker_one_sub_eq_eigenspace (K : E →L[ℝ] E) :
    LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap
      = Module.End.eigenspace K.toLinearMap 1 := by
  ext u
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Module.End.mem_eigenspace_iff, one_smul,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, sub_eq_zero]
  exact eq_comm

/-- **Finite-dimensionality of `ker(1 - K)`** for a compact operator `K` (Riesz
theory): the kernel is the eigenspace of `K` at the nonzero eigenvalue `1`. -/
theorem finiteDimensional_ker_one_sub (hK : IsCompactOperator K) :
    FiniteDimensional ℝ (LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap) := by
  rw [ker_one_sub_eq_eigenspace]
  exact ContinuousLinearMap.finite_dimensional_eigenspace hK 1 one_ne_zero

omit [CompleteSpace E] in
/-- `1 - K` is **bounded below on the orthogonal complement of its kernel**: the heart
of the Riesz closed-range theorem, by the standard compactness contradiction. If not,
normalised `xₙ ∈ (ker(1-K))ᗮ` have `(1-K)xₙ → 0`; compactness of `K` extracts
`Kx_{φ(n)} → z`, so `x_{φ(n)} → z` with `‖z‖ = 1`, `z ∈ ker(1-K)`, and
`z ∈ (ker(1-K))ᗮ` -- forcing `z = 0`, a contradiction. -/
theorem exists_pos_bound_on_orthogonal_ker (hK : IsCompactOperator K) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ (LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap)ᗮ,
      c * ‖x‖ ≤ ‖(1 - K : E →L[ℝ] E) x‖ := by
  set N := LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap with hN
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ x : E,
      x ∈ Nᗮ ∧ ‖x‖ = 1 ∧ ‖(1 - K : E →L[ℝ] E) x‖ < 1 / (n + 1) := by
    intro n
    obtain ⟨x, hxmem, hxlt⟩ := hcon (1 / (n + 1)) (by positivity)
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hxlt
    have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
    refine ⟨‖x‖⁻¹ • x, Submodule.smul_mem _ _ hxmem, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn]
    · rw [map_smul, norm_smul, norm_inv, norm_norm]
      calc ‖x‖⁻¹ * ‖(1 - K : E →L[ℝ] E) x‖
          < ‖x‖⁻¹ * (1 / (n + 1) * ‖x‖) :=
            mul_lt_mul_of_pos_left hxlt (by positivity)
        _ = 1 / (n + 1) * (‖x‖⁻¹ * ‖x‖) := by ring
        _ = 1 / (n + 1) := by rw [inv_mul_cancel₀ hxn, mul_one]
  choose y hymem hynorm hylt using hseq
  -- the images `K yₙ` live in a compact set; extract a convergent subsequence
  have hK' : IsCompactOperator K.toLinearMap := hK
  have hcpt : IsCompact (closure (K.toLinearMap '' Metric.closedBall 0 1)) :=
    hK'.isCompact_closure_image_closedBall 1
  have hmem : ∀ n : ℕ, K (y n) ∈ closure (K.toLinearMap '' Metric.closedBall 0 1) :=
    fun n => subset_closure ⟨y n, mem_closedBall_zero_iff.mpr (le_of_eq (hynorm n)), rfl⟩
  obtain ⟨z, -, φ, hφ, hzlim⟩ := hcpt.tendsto_subseq hmem
  -- `(1 - K) y_{φ(n)} → 0` by the squeeze
  have hbound : ∀ n : ℕ, ‖(1 - K : E →L[ℝ] E) (y (φ n))‖ ≤ 1 / (n + 1) := by
    intro n
    refine (hylt (φ n)).le.trans ?_
    have h1 : (n : ℝ) + 1 ≤ (φ n : ℝ) + 1 := by
      have hn : n ≤ φ n := hφ.le_apply
      exact_mod_cast Nat.add_le_add_right hn 1
    exact one_div_le_one_div_of_le (by positivity) h1
  have h1K : Filter.Tendsto (fun n => (1 - K : E →L[ℝ] E) (y (φ n)))
      Filter.atTop (nhds 0) :=
    squeeze_zero_norm hbound tendsto_one_div_add_atTop_nhds_zero_nat
  -- the subsequence itself converges to `z`
  have hy_lim : Filter.Tendsto (fun n => y (φ n)) Filter.atTop (nhds z) := by
    have hsum : (fun n => y (φ n))
        = fun n => (1 - K : E →L[ℝ] E) (y (φ n)) + K (y (φ n)) := by
      funext n
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, sub_add_cancel]
    rw [hsum]
    simpa [Function.comp] using h1K.add hzlim
  -- `z` has norm one, lies in `Nᗮ` (closed), and lies in `N` (continuity): contradiction
  have hznorm : ‖z‖ = 1 := by
    have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds ‖z‖) :=
      hy_lim.norm.congr (fun n => hynorm (φ n))
    exact tendsto_nhds_unique hconst tendsto_const_nhds
  have hz_orth : z ∈ Nᗮ :=
    N.isClosed_orthogonal.mem_of_tendsto hy_lim
      (Filter.Eventually.of_forall (fun n => hymem (φ n)))
  have hz_ker : z ∈ N := by
    have hcont : Filter.Tendsto (fun n => (1 - K : E →L[ℝ] E) (y (φ n)))
        Filter.atTop (nhds ((1 - K : E →L[ℝ] E) z)) :=
      (((1 - K : E →L[ℝ] E).continuous.tendsto z).comp hy_lim)
    have hz0 : (1 - K : E →L[ℝ] E) z = 0 := tendsto_nhds_unique hcont h1K
    rw [hN, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    exact hz0
  have hz_zero : z = 0 := (Submodule.mem_bot ℝ).mp
    (N.orthogonal_disjoint.le_bot (Submodule.mem_inf.mpr ⟨hz_ker, hz_orth⟩))
  rw [hz_zero, norm_zero] at hznorm
  exact zero_ne_one hznorm

/-- **Closed range (Riesz theory).** For a compact operator `K` on a real Hilbert
space the range of `1 - K` is closed: `1 - K` is bounded below -- hence antilipschitz
with closed range -- on the orthogonal complement of its finite-dimensional kernel, and
the full range is the image of that complement. This is the geometric half of the
Fredholm alternative (Guo Thm VII.4.4). -/
theorem isClosed_range_one_sub (hK : IsCompactOperator K) :
    IsClosed (Set.range (1 - K : E →L[ℝ] E)) := by
  obtain ⟨c, hc, hbdd⟩ := exists_pos_bound_on_orthogonal_ker hK
  set N := LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap with hN
  haveI : FiniteDimensional ℝ N := finiteDimensional_ker_one_sub hK
  set T : Nᗮ →L[ℝ] E := (1 - K : E →L[ℝ] E).comp Nᗮ.subtypeL with hT
  have hbT : ∀ x : Nᗮ, ‖x‖ ≤ c⁻¹ * ‖T x‖ := by
    intro x
    have hx : c * ‖x‖ ≤ ‖T x‖ := hbdd (x : E) x.2
    have h := mul_le_mul_of_nonneg_left hx (le_of_lt (inv_pos.mpr hc))
    rwa [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at h
  have hanti : AntilipschitzWith (c⁻¹).toNNReal T :=
    T.antilipschitz_of_bound (fun x => by
      have h := hbT x
      rwa [← Real.coe_toNNReal c⁻¹ (by positivity)] at h)
  have hTclosed : IsClosed (Set.range T) :=
    hanti.isClosed_range T.uniformContinuous
  have hrange : Set.range ((1 - K : E →L[ℝ] E)) = Set.range T := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨n, hn, m, hm, rfl⟩ := N.exists_add_mem_mem_orthogonal x
      refine ⟨⟨m, hm⟩, ?_⟩
      have hn0 : (1 - K : E →L[ℝ] E) n = 0 := by
        rw [hN, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hn
        exact hn
      show (1 - K : E →L[ℝ] E) m = (1 - K : E →L[ℝ] E) (n + m)
      rw [map_add, hn0, zero_add]
    · rintro ⟨m, rfl⟩
      exact ⟨(m : E), rfl⟩
  rw [hrange]
  exact hTclosed

/-- A closed-range operator on a real Hilbert space has range exactly the orthogonal
complement of the kernel of its adjoint: `range A = (ker A†)ᗮ`. With
`isClosed_range_one_sub` this yields the solvability half of the Fredholm
alternative. -/
lemma range_eq_orthogonal_ker_adjoint (A : E →L[ℝ] E)
    (hA : IsClosed (Set.range A)) :
    LinearMap.range A.toLinearMap
      = (LinearMap.ker (ContinuousLinearMap.adjoint A).toLinearMap)ᗮ := by
  have h1 : (LinearMap.range A.toLinearMap)ᗮ
      = LinearMap.ker (ContinuousLinearMap.adjoint A).toLinearMap :=
    ContinuousLinearMap.orthogonal_range A
  rw [← h1, Submodule.orthogonal_orthogonal_eq_closure]
  refine (IsClosed.submodule_topologicalClosure_eq ?_).symm
  rw [LinearMap.coe_range]
  exact hA

end RieszTheory

variable {d : ℕ}

namespace FullEllipticOp

variable (Op : FullEllipticOp d) (Ω : Set (EuclideanSpace ℝ (Fin d)))

/-- The space `N` of weak solutions of the homogeneous problem `Lu = 0`: the kernel of
the Riesz representative `opA` of the full divergence form. -/
def solSpace : Submodule ℝ (H01 Ω) := LinearMap.ker (Op.opA Ω).toLinearMap

/-- Membership in `solSpace` is exactly being a weak solution of the homogeneous
problem: `B[u, v] = 0` against every `v ∈ H₀¹(Ω)`. -/
lemma mem_solSpace_iff (u : H01 Ω) :
    u ∈ Op.solSpace Ω ↔ ∀ v : H01 Ω, Op.fullBilin Ω u v = 0 := by
  rw [solSpace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro hu v
    rw [← Op.inner_opA Ω u v, hu, inner_zero_left]
  · intro hu
    refine ext_inner_right (𝕜 := ℝ) (fun v => ?_)
    rw [Op.inner_opA Ω u v, hu v, inner_zero_left]

/-- The homogeneous solution space is the eigenspace of the compact part `opK` at the
eigenvalue `1`: since `opA = opE ∘ (1 - opK)` with `opE` an equivalence,
`opA u = 0 ⟺ opK u = u`. -/
lemma solSpace_eq_eigenspace :
    Op.solSpace Ω = Module.End.eigenspace (Op.opK Ω).toLinearMap 1 := by
  ext u
  rw [solSpace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    Module.End.mem_eigenspace_iff, one_smul]
  have hfac : Op.opA Ω u = (Op.opE Ω) ((1 - Op.opK Ω) u) := by
    rw [Op.opA_factor Ω]; rfl
  constructor
  · intro hu
    have h0 : (1 - Op.opK Ω) u = 0 := by
      apply (Op.opE Ω).injective
      rw [← hfac, hu, map_zero]
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, sub_eq_zero] at h0
    exact h0.symm
  · intro hu
    have h0 : (1 - Op.opK Ω) u = 0 := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        show Op.opK Ω u = u from hu, sub_self]
    rw [hfac, h0, map_zero]

/-- **Finite-dimensionality of the homogeneous solution space (Guo Thm VII.4.4(i)).**
Under the Rellich-Kondrachov input (`opK` compact), the space of weak solutions of the
homogeneous problem `Lu = 0` is finite-dimensional: it is the eigenspace of the compact
operator `opK` at the nonzero eigenvalue `1`, and Riesz theory makes such eigenspaces
finite-dimensional. -/
theorem finiteDimensional_solSpace (hK : IsCompactOperator (Op.opK Ω)) :
    FiniteDimensional ℝ (Op.solSpace Ω) := by
  rw [solSpace_eq_eigenspace]
  exact ContinuousLinearMap.finite_dimensional_eigenspace hK 1 one_ne_zero

/-- **Closed range of the elliptic operator (towards Guo Thm VII.4.4/VII.4.7).** Under
the Rellich-Kondrachov input the range of `opA` -- the set of Riesz representatives of
solvable right-hand sides -- is closed: `opA = opE ∘ (1 - opK)` with `opE` a
homeomorphism, and `1 - opK` has closed range by Riesz theory. This is the geometric
input for the solvability criterion `Lu = f solvable ⟺ f ⊥ N*`. -/
theorem isClosed_range_opA (hK : IsCompactOperator (Op.opK Ω)) :
    IsClosed (Set.range (Op.opA Ω)) := by
  have h1 : IsClosed (Set.range (1 - Op.opK Ω : H01 Ω →L[ℝ] H01 Ω)) :=
    isClosed_range_one_sub hK
  have h2 : Set.range (Op.opA Ω)
      = (Op.opE Ω) '' Set.range (1 - Op.opK Ω : H01 Ω →L[ℝ] H01 Ω) := by
    rw [Op.opA_factor Ω, ContinuousLinearMap.coe_comp', Set.range_comp]
    rfl
  rw [h2]
  exact (Op.opE Ω).toHomeomorph.isClosedMap _ h1

/-- The **adjoint solution space** `N*`: the kernel of the Hilbert adjoint of `opA`,
which is exactly the space of weak solutions of the **transpose problem**
`B[v, u] = 0` for all `v` (Guo Remark VII.4.6: the adjoint problem is the transpose
form, with no differentiability demanded of the coefficients). -/
def solSpaceStar : Submodule ℝ (H01 Ω) :=
  LinearMap.ker (ContinuousLinearMap.adjoint (Op.opA Ω)).toLinearMap

/-- Membership in `solSpaceStar` is exactly being a weak solution of the transpose
problem: `B[v, u] = 0` against every `v ∈ H₀¹(Ω)`. -/
lemma mem_solSpaceStar_iff (u : H01 Ω) :
    u ∈ Op.solSpaceStar Ω ↔ ∀ v : H01 Ω, Op.fullBilin Ω v u = 0 := by
  rw [solSpaceStar, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro hu v
    rw [← Op.inner_opA Ω v u, ← ContinuousLinearMap.adjoint_inner_right, hu,
      inner_zero_right]
  · intro hu
    refine ext_inner_right (𝕜 := ℝ) (fun v => ?_)
    rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left, real_inner_comm,
      Op.inner_opA Ω v u]
    exact hu v

/-- **Solvability criterion (Guo Thm VII.4.7, solvability part).** Under the
Rellich-Kondrachov input, the weak problem `Lu = f` is solvable exactly when `f`
annihilates the adjoint solution space: `∃u ∀v, B[u, v] = f(v)` iff `f(w) = 0` for
every weak solution `w` of the transpose problem `B[v, w] = 0`. The proof is closed
range (`isClosed_range_opA`) plus the Hilbert-space duality
`range A = (ker A†)ᗮ`. -/
theorem solvable_iff_orthogonal_solSpaceStar (hK : IsCompactOperator (Op.opK Ω))
    (f : H01 Ω →L[ℝ] ℝ) :
    (∃ u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v)
      ↔ ∀ w ∈ Op.solSpaceStar Ω, f w = 0 := by
  set g : H01 Ω := (InnerProductSpace.toDual ℝ (H01 Ω)).symm f with hg
  have hgrep : ∀ v : H01 Ω, ⟪g, v⟫ = f v := fun v => InnerProductSpace.toDual_symm_apply
  have hiff : (∃ u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v)
      ↔ g ∈ LinearMap.range (Op.opA Ω).toLinearMap := by
    rw [LinearMap.mem_range]
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨u, ?_⟩
      show Op.opA Ω u = g
      refine ext_inner_right (𝕜 := ℝ) (fun v => ?_)
      rw [Op.inner_opA Ω u v, hu v, hgrep v]
    · rintro ⟨u, hu⟩
      have hu' : Op.opA Ω u = g := hu
      exact ⟨u, fun v => by rw [← Op.inner_opA Ω u v, hu', hgrep v]⟩
  rw [hiff, range_eq_orthogonal_ker_adjoint _ (Op.isClosed_range_opA Ω hK),
    Submodule.mem_orthogonal]
  constructor
  · intro h w hw
    rw [← hgrep w, real_inner_comm]
    exact h w hw
  · intro h w hw
    rw [real_inner_comm, hgrep w]
    exact h w hw

end FullEllipticOp

end EllipticDirichlet.Sobolev
