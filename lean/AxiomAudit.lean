/-
Axiom audit of the headline results.

Each declaration the README claims is checked here against the three axioms of
classical Lean: `propext`, `Classical.choice` and `Quot.sound`. `assert_classical_axioms`
fails the build when a listed declaration does not exist or depends on any other axiom,
so a `sorryAx` reaching one of these, or a new axiom entering through a dependency, fails
`lake build` rather than passing unnoticed.

This module is a build target in its own right. It is not imported by
`EllipticPdes`, and nothing imports it.
-/

module

public import EllipticPdes
public meta import Lean.Util.CollectAxioms

open Lean Elab Command

/-- `assert_classical_axioms n₁ n₂ …` fails unless every `nᵢ` is a declaration whose axioms
lie among `propext`, `Classical.choice` and `Quot.sound`. -/
syntax (name := assertClassicalAxioms) "assert_classical_axioms" (ppSpace ident)+ : command

/-- Elaborator for `assert_classical_axioms`. -/
@[command_elab assertClassicalAxioms]
public meta def elabAssertClassicalAxioms : CommandElab := fun stx => do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for id in stx[1].getArgs do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← liftCoreM <| collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwErrorAt id m!"{n} depends on axioms outside the classical three: {bad.toList}"


/-! ### Lax-Milgram -/

assert_classical_axioms
  EllipticPdes.lax_milgram

/-! ### Existence and uniqueness -/

assert_classical_axioms
  EllipticPdes.poisson_weak_solution
  EllipticPdes.Sobolev.FullEllipticOp.existence_three_of_bounded
  EllipticPdes.Sobolev.FullEllipticOp.weak_solution_L2_of_nonneg_zeroth_of_bounded

/-! ### Dual space `H⁻¹` -/

assert_classical_axioms
  EllipticPdes.hneg_characterization

/-! ### Gårding inequality -/

assert_classical_axioms
  EllipticPdes.Sobolev.FullEllipticOp.garding
  EllipticPdes.Sobolev.FullEllipticOp.weak_solution

/-! ### Fredholm alternative -/

assert_classical_axioms
  EllipticPdes.Sobolev.FullEllipticOp.fredholm_alternative
  EllipticPdes.Sobolev.FullEllipticOp.finiteDimensional_solSpace
  EllipticPdes.Sobolev.FullEllipticOp.finrank_solSpaceStar_eq_finrank_solSpace
  EllipticPdes.Sobolev.FullEllipticOp.solvable_iff_orthogonal_solSpaceStar
  EllipticPdes.Sobolev.fredholm_alternative_compact
  EllipticPdes.Sobolev.fredholm_dichotomy_compact
  EllipticPdes.Sobolev.FullEllipticOp.fredholm_alternative_of_bounded

/-! ### Resolvent bound and spectrum -/

assert_classical_axioms
  EllipticPdes.Sobolev.FullEllipticOp.resolvent_bound
  EllipticPdes.Sobolev.FullEllipticOp.resolvent_bound_of_bounded
  EllipticPdes.Sobolev.spectrum_compact_operator
  EllipticPdes.Sobolev.solOp_spectral
  EllipticPdes.Sobolev.dirichlet_spectral
  EllipticPdes.Sobolev.dirichlet_spectral_of_bounded
  EllipticPdes.Sobolev.embL2_isCompact
  EllipticPdes.Sobolev.symmetric_fullElliptic_spectral

/-! ### Interior regularity -/

assert_classical_axioms
  EllipticPdes.Regularity.interior_H2_estimate
  EllipticPdes.Regularity.interior_cutoffGrad_mem_H01
  EllipticPdes.Regularity.caccioppoli

/-! ### Higher interior regularity -/

assert_classical_axioms
  EllipticPdes.Regularity.HasWeakDeriv.unique
  EllipticPdes.Regularity.setIntegral_mul_partialD_cut_eq
  EllipticPdes.Regularity.outer_secondWeakDeriv
  EllipticPdes.Regularity.localWeakForm_of_fullBilin
  EllipticPdes.Regularity.differentiated_weakForm_of_weakSolution
  EllipticPdes.Regularity.higher_interior_regularity
  EllipticPdes.Regularity.exists_gradClosed_of_hasIteratedWeakDerivOn

/-! ### Campanato's characterisation of Hölder continuity -/

assert_classical_axioms
  EllipticPdes.Campanato.campanato_holderOnWith
  EllipticPdes.Campanato.campanatoOn_of_holderOnWith

/-! ### Boundary regularity -/

assert_classical_axioms
  EllipticPdes.Regularity.cutoffMulOn_tangDiffQuotG_mem_H01
  EllipticPdes.Regularity.HasWeakDerivOn.of_mul_contDiff_left
  EllipticPdes.Regularity.exists_hasWeakDerivOn_of_mul_diag

/-! ### Classical regularity -/

assert_classical_axioms
  EllipticPdes.Embedding.interior_holder_estimate
  EllipticPdes.Embedding.interior_holder_estimate_two
  EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le
  EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le_of_le
  EllipticPdes.Embedding.exists_eLpNorm_six_le
  EllipticPdes.Embedding.exists_eLpNorm_four_le
  EllipticPdes.Embedding.interior_holder_estimate_one
  EllipticPdes.Embedding.memLp_two_mul_of_gradClosed
  EllipticPdes.Embedding.hasFDerivAt_of_continuousOn_hasWeakGradOn
  EllipticPdes.Embedding.contDiffOn_of_gradClosed
  EllipticPdes.Regularity.interior_smooth

/-! ### One smooth representative on all of the interior -/

assert_classical_axioms
  EllipticPdes.Regularity.interior_smooth_global

/-! ### Localising coefficients smooth on an open set -/

assert_classical_axioms
  EllipticPdes.Regularity.exists_localOp
  EllipticPdes.Regularity.datum_hyp
  EllipticPdes.Regularity.localise

/-! ### Weak solutions with no boundary condition -/

assert_classical_axioms
  EllipticPdes.Regularity.cutoffMul_mem_H01_of_mem_W12
  EllipticPdes.Regularity.IsLocalWeakSolution.weakForm
  EllipticPdes.Regularity.isLocalWeakSolution_iff_localWeakSol
  EllipticPdes.Regularity.reduction_weakForm
  EllipticPdes.Regularity.caccioppoli_W12
  EllipticPdes.Regularity.interior_H2_estimate_W12
  EllipticPdes.Regularity.exists_reductionDatum
  EllipticPdes.Regularity.exists_collarFamily_of_weakDerivOn
  EllipticPdes.Regularity.higher_interior_regularity_W12
  EllipticPdes.Regularity.interior_smooth_W12
  EllipticPdes.Regularity.interior_smooth_global_W12
  EllipticPdes.Regularity.isLocalWeakSolution_of_localWeakSol
  EllipticPdes.Regularity.exists_contDiffOn_of_localWeakSol
  EllipticPdes.Regularity.exists_contDiffOn_of_weakSolution_evans
  EllipticPdes.Regularity.interior_H2_regularity_evans
  EllipticPdes.Regularity.higher_interior_regularity_evans
  EllipticPdes.Embedding.memLp_of_gradClosed_fullStep
  EllipticPdes.Embedding.memLp_two_mul_of_gradClosed_fullStep
  EllipticPdes.Embedding.contDiffOn_holder_of_gradClosed
  EllipticPdes.Regularity.exists_gradClosed_of_hasIteratedWeakDerivOn_le
  EllipticPdes.Regularity.exists_contDiffOn_holder_ball_of_hasIteratedWeakDerivOn
  EllipticPdes.Regularity.exists_contDiffOn_holder_ball

/-! ### Base of the Poincaré chain -/

assert_classical_axioms
  EllipticPdes.Poincare.intervalIntegral_mul_sq_le
  EllipticPdes.Poincare.poincare_oneDim
  EllipticPdes.Poincare.poincare_domain
  EllipticPdes.Poincare.poincare_H01
  EllipticPdes.Poincare.poincare_H01_euclBox
  EllipticPdes.Poincare.poincare_H01_of_bounded
  EllipticPdes.Embedding.eLpNorm_le_of_mem_H01
  EllipticPdes.Embedding.eLpNorm_le_of_mem_H01_of_isBounded
  EllipticPdes.Regularity.interior_holder_of_weakSolution
  EllipticPdes.Embedding.eLpNorm_weakSolution_le
  EllipticPdes.Analysis.eLpNorm_le_rpow_mul_rpow
  EllipticPdes.Embedding.rellichEmbL_isCompact
  EllipticPdes.Embedding.rellichEmbL_isCompact_of_le
  EllipticPdes.Embedding.rellichEmbL_isCompact_of_lt
  EllipticPdes.Embedding.exists_holderOnWith_of_gradClosed_even
  EllipticPdes.Embedding.exists_const_eLpNorm_le_of_gradClosed_fullStep
  EllipticPdes.Embedding.exists_const_holderOnWith_of_gradClosed_of_bound
  EllipticPdes.Embedding.not_isCompactOperator_critEmb
  EllipticPdes.Analysis.exists_weakLimit
  EllipticPdes.Embedding.exists_minimiser_of_lt
  EllipticPdes.Sobolev.exists_principal_eigenpair
  EllipticPdes.Sobolev.principalEigenvalue_le_of_weak_eigen
  EllipticPdes.Sobolev.dirichlet_principal_eigenpair
  EllipticPdes.Sobolev.dirichlet_poincare_sharp
  EllipticPdes.Analysis.hasDerivAt_integral_abs_rpow
  EllipticPdes.Analysis.euler_lagrange_of_norm_min
  EllipticPdes.Embedding.exists_weakSolution_semilinear_of_lt
  EllipticPdes.Sobolev.exists_higher_eigenpair
  EllipticPdes.Analysis.exists_bilin_minimiser
  EllipticPdes.Analysis.euler_lagrange_of_bilin_min
  EllipticPdes.Embedding.exists_weakSolution_dirichlet_of_lt
  EllipticPdes.Embedding.exists_weakSolution_dirichlet_of_lt'
  EllipticPdes.Sobolev.dirichlet_principal_eigenpair_of_bounded
  EllipticPdes.Sobolev.exists_eigen_family
  EllipticPdes.Sobolev.dirichlet_eigen_family_of_bounded
  EllipticPdes.Sobolev.dirichlet_principal_eigenpair_ball
  EllipticPdes.Sobolev.dirichlet_eigen_family_ball
  EllipticPdes.Sobolev.weak_eigenvalue_pos
  EllipticPdes.Sobolev.solOp_finiteDimensional_eigenspace
  EllipticPdes.Sobolev.dirichlet_eigenvalue_pos_ball
  EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le_compactSupport
  EllipticPdes.Embedding.memLp_of_gradClosed_compactSupport
  EllipticPdes.Embedding.memLp_of_gradClosed_compactSupport_ideal
  EllipticPdes.Embedding.memLp_of_gradClosed_general
  EllipticPdes.Embedding.memLp_of_gradClosed_general_ideal
  EllipticPdes.Extension.hasWeakGradOn_comp_reflect
  EllipticPdes.Extension.partialD_comp_reflect
  EllipticPdes.Extension.hasWeakGradOn_comp_translate
  EllipticPdes.Extension.partialD_comp_shear
  EllipticPdes.Extension.hasWeakGradOn_comp_shear
  EllipticPdes.Extension.hasWeakGradOn_chartExt
  EllipticPdes.Extension.eLpNorm_chartExt_le
  EllipticPdes.Extension.eLpNorm_chartExtGrad_le
  EllipticPdes.Extension.hasWeakGradOn_comp_linearIsometry
  EllipticPdes.Extension.hasWeakGradOn_mul_cutoff_inter
  EllipticPdes.Extension.exists_finite_chart_cover
  EllipticPdes.Extension.nonempty_boundaryPartition
  EllipticPdes.Extension.exists_localExtension
  EllipticPdes.Extension.exists_extension
  EllipticPdes.Extension.exists_extension_subset
  EllipticPdes.Analysis.tendsto_eLpNorm_translate_sub
  EllipticPdes.Extension.tendsto_eLpNorm_translate_convolution_sub
  EllipticPdes.Embedding.exists_holderOnWith_of_gradClosed_general
  EllipticPdes.Embedding.morreyExponent_eq_ladder

/-! ### Norm bound of the extension operator -/

assert_classical_axioms
  EllipticPdes.Extension.exists_localExtension_bound
  EllipticPdes.Extension.exists_extension_bound
  EllipticPdes.Extension.exists_extension_subset_bound

/-! ### The extension operator as a linear map -/

assert_classical_axioms
  EllipticPdes.Extension.localExtension_bound
  EllipticPdes.Extension.extension_bound
  EllipticPdes.Extension.extension_subset_bound
  EllipticPdes.Extension.exists_extLinear

/-! ### Solvability and interior smoothness composed -/

assert_classical_axioms
  EllipticPdes.Regularity.exists_weakSolution_interior_smooth

/-! ### Sobolev embedding on a bounded `C¹` domain -/

assert_classical_axioms
  EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le_domain
  EllipticPdes.Embedding.exists_const_memLp_of_gradClosed_domain
  EllipticPdes.Embedding.exists_const_holderOnWith_of_gradClosed_domain
  EllipticPdes.Embedding.exists_const_memLp_of_gradClosed_domain_ideal
  EllipticPdes.Embedding.exists_const_holderOnWith_domain_ideal
  EllipticPdes.Embedding.exists_const_holderOnWith_domain_free

/-! ### Classical derivatives up to the boundary -/

assert_classical_axioms
  EllipticPdes.Embedding.exists_const_contDiffOn_holderOnWith_of_gradClosed_domain
  EllipticPdes.Embedding.exists_const_contDiffOn_holderOnWith_domain_ideal
  EllipticPdes.Embedding.exists_const_contDiffOn_holderOnWith_domain_free

/-! ### Global approximation and Rellich-Kondrachov on the graph space -/

assert_classical_axioms
  EllipticPdes.Extension.exists_smooth_tendsto_of_hasWeakGradOn
  EllipticPdes.Extension.exists_smooth_tendsto_of_mem_W12
  EllipticPdes.Sobolev.transL2_toLp_sub_le_of_hasWeakGradOn_univ
  EllipticPdes.Regularity.norm_diffQuot_le_of_hasWeakDeriv
  EllipticPdes.Regularity.weakDeriv_of_diffQuot_bounded
  EllipticPdes.Embedding.morrey_ball_contDiff
  EllipticPdes.Embedding.morrey_ball
  EllipticPdes.Sobolev.embW12_isCompact

/-! ### The Poincaré inequality with the mean subtracted -/

assert_classical_axioms
  EllipticPdes.Embedding.ae_const_of_hasWeakGradOn_zero
  EllipticPdes.Sobolev.poincare_wirtinger

/-! ### The pointwise equation of a smooth representative -/

assert_classical_axioms
  EllipticPdes.Regularity.hasWeakGradOn_of_contDiffOn
  EllipticPdes.Regularity.weakSolution_ae_eq_of_contDiffOn
  EllipticPdes.Regularity.exists_weakSolution_interior_classical

/-! ### The unit ball as an instance of a bounded domain with `C¹` boundary -/

assert_classical_axioms
  EllipticPdes.Extension.hasC1Boundary_ball
  EllipticPdes.Sobolev.embW12_isCompact_ball
  EllipticPdes.Sobolev.poincare_wirtinger_ball

/-! ### The extension operator between the graph spaces -/

assert_classical_axioms
  EllipticPdes.Extension.mem_W12_of_hasWeakGradOn
  EllipticPdes.Extension.exists_extW12

/-! ### Poincaré's inequality on a ball -/

assert_classical_axioms
  EllipticPdes.Sobolev.hasWeakGradOn_comp_affineBall
  EllipticPdes.Sobolev.poincare_ball

/-! ### The chain rule and the weak maximum principle -/

assert_classical_axioms
  EllipticPdes.Embedding.hasWeakGradOn_comp

/-! ### Elementary properties of weak derivatives -/

assert_classical_axioms
  EllipticPdes.Embedding.hasWeakGradOn_unique_ae_of_locallyIntegrableOn
  EllipticPdes.Embedding.HasWeakGradOn.add_of_locallyIntegrableOn
  EllipticPdes.Embedding.HasWeakGradOn.neg
  EllipticPdes.Embedding.HasWeakGradOn.const_mul
  EllipticPdes.Embedding.HasWeakGradOn.mono
  EllipticPdes.Sobolev.instCompleteSpaceW12
  EllipticPdes.Sobolev.instCompleteSpaceH01
  EllipticPdes.Embedding.partialD_convolution_eq_of_hasWeakGradOn
  EllipticPdes.Embedding.tendsto_eLpNorm_convolution_sub
  EllipticPdes.Embedding.hasWeakGradOn_posPart
  EllipticPdes.Embedding.ae_eq_zero_of_eq_const_of_hasWeakGradOn
  EllipticPdes.Sobolev.weak_maximum_principle

/-! ### Truncation in `H₀¹` -/

assert_classical_axioms
  EllipticPdes.Sobolev.mem_H01_of_hasCompactSupport
  EllipticPdes.Sobolev.exists_mem_H01_posPart_sub_const
  EllipticPdes.Sobolev.weak_maximum_principle_H01
  EllipticPdes.Sobolev.eq_zero_of_weakSolution_H01

/-! ### The weak maximum principle with a transport term -/

assert_classical_axioms
  EllipticPdes.Sobolev.exists_truncation_mem_H01
  EllipticPdes.Sobolev.weak_maximum_principle_transport
  EllipticPdes.Embedding.hasWeakGradOn_negPart
  EllipticPdes.Embedding.hasWeakGradOn_abs

/-! ### The classical weak maximum principle -/

assert_classical_axioms
  EllipticPdes.Classical.sum_mul_nonpos_of_posSemidef
  EllipticPdes.Classical.sndFDeriv_nonpos_of_isLocalMax
  EllipticPdes.Classical.weak_maximum_principle
  EllipticPdes.Classical.weak_minimum_principle
  EllipticPdes.Classical.weak_maximum_principle_of_nonneg
  EllipticPdes.Classical.weak_minimum_principle_of_nonneg

/-! ### Hopf's lemma and the strong maximum principle -/

assert_classical_axioms
  EllipticPdes.Classical.hopf_lemma_ball
  EllipticPdes.Classical.hopf_lemma
  EllipticPdes.Classical.strong_maximum_principle
  EllipticPdes.Classical.strong_maximum_principle_of_nonneg

/-! ### Corollaries of the strong maximum principle -/

assert_classical_axioms
  EllipticPdes.Classical.dirichlet_unique
  EllipticPdes.Classical.hopf_lemma_of_zero
  EllipticPdes.Classical.strong_maximum_principle_of_zero
  EllipticPdes.Classical.avoidance_principle
  EllipticPdes.Classical.eq_of_eq_of_fderiv_eq
  EllipticPdes.Classical.neumann_unique
  EllipticPdes.Classical.neumann_unique_of_exists_pos

/-! ### A priori bound from the maximum principle -/

assert_classical_axioms
  EllipticPdes.Classical.apriori_bound_sub
  EllipticPdes.Classical.apriori_bound_abs

/-! ### Subharmonic and harmonic functions -/

assert_classical_axioms
  EllipticPdes.Classical.weak_maximum_principle_subharmonic
  EllipticPdes.Classical.strong_maximum_principle_subharmonic
  EllipticPdes.Classical.strong_minimum_principle_superharmonic
  EllipticPdes.Classical.harmonic_const_of_max
  EllipticPdes.Classical.harmonic_const_of_min
  EllipticPdes.Classical.dirichlet_unique_harmonic
  EllipticPdes.Classical.not_isLocalMax_of_nondivOp_neg
  EllipticPdes.Classical.comparison_principle
  EllipticPdes.Classical.abs_le_of_nondivOp_eq_zero
  EllipticPdes.Embedding.eLpNorm_le_of_mem_H01_two

/-! ### General theory over a finite-dimensional inner product space -/

assert_classical_axioms
  IsCoercive.existsUnique_apply_eq
  EllipticPdes.HasWeakFDerivOn.hasFDerivAt
  EllipticPdes.Poincare.integral_sq_le_of_tsupport_subset_slab
  EllipticPdes.H1Graph.poincare_H01_of_bounded
  EllipticPdes.H1Graph.embL2_isCompact
  EllipticPdes.DivForm.FullEllipticOp.garding
  EllipticPdes.DivForm.FullEllipticOp.weak_solution
  EllipticPdes.DivForm.FullEllipticOp.weak_solution_of_nonneg_zeroth_of_bounded
  EllipticPdes.DivForm.FullEllipticOp.fredholm_alternative_of_bounded
  EllipticPdes.DivForm.FullEllipticOp.fredholm_unique_imp_exists_of_bounded
  EllipticPdes.DivForm.FullEllipticOp.solvable_iff_orthogonal_transpose_of_bounded
  EllipticPdes.DivForm.FullEllipticOp.notMem_sigmaSet_iff_solvable_of_bounded
  EllipticPdes.DivForm.FullEllipticOp.existence_three_of_bounded
  EllipticPdes.DivForm.FullEllipticOp.resolvent_bound_of_bounded
  EllipticPdes.DivForm.FullEllipticOp.symmetric_spectral_of_bounded
  EllipticPdes.DivForm.FullEllipticOp.interior_smooth
  EllipticPdes.DivForm.FullEllipticOp.exists_weakSolution_interior_smooth
  EllipticPdes.H1Graph.embL2_isCompact_haar
  EllipticPdes.DivForm.FullEllipticOp.fredholm_alternative_of_bounded_haar
  EllipticPdes.DivForm.FullEllipticOp.fredholm_unique_imp_exists_of_bounded_haar
  EllipticPdes.DivForm.FullEllipticOp.solvable_iff_orthogonal_transpose_of_bounded_haar
  EllipticPdes.DivForm.FullEllipticOp.notMem_sigmaSet_iff_solvable_of_bounded_haar
  EllipticPdes.DivForm.FullEllipticOp.existence_three_of_bounded_haar
  EllipticPdes.DivForm.FullEllipticOp.resolvent_bound_of_bounded_haar
  EllipticPdes.DivForm.FullEllipticOp.symmetric_spectral_of_bounded_haar
  EllipticPdes.Classical.hopf_lemma
  EllipticPdes.Classical.nondivOperator.weak_maximum_principle
  EllipticPdes.Classical.nondivOperator.comparison_principle
  EllipticPdes.Campanato.Haar.campanato_holderOnWith
  EllipticPdes.H1Graph.hneg_characterization
