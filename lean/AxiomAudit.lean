/-
Axiom audit of the headline results.

Each declaration the README claims is pinned here to the three axioms of
classical Lean: `propext`, `Classical.choice` and `Quot.sound`. `#guard_msgs`
turns a change in the axiom set into a build error, so a `sorryAx` reaching any
of these, or a new axiom entering through a dependency, fails `lake build`
rather than passing unnoticed.

`whitespace := lax` is required because the pretty printer wraps the longer
declaration names across lines.

This module is a build target in its own right. It is not imported by
`EllipticPdes`, and nothing imports it.
-/
import EllipticPdes

/-! ### Existence and uniqueness -/

/-- info: 'EllipticPdes.dirichlet_weak_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.dirichlet_weak_solution

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.existence_three_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.existence_three_of_bounded

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.weak_solution_L2_of_nonneg_zeroth_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.weak_solution_L2_of_nonneg_zeroth_of_bounded

/-! ### Dual space `H⁻¹` -/

/-- info: 'EllipticPdes.hneg_characterization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.hneg_characterization

/-! ### Gårding inequality -/

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.garding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.garding

/-! ### Fredholm alternative -/

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.fredholm_alternative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.fredholm_alternative

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.finiteDimensional_solSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.finiteDimensional_solSpace

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.finrank_solSpaceStar_eq_finrank_solSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.finrank_solSpaceStar_eq_finrank_solSpace

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.solvable_iff_orthogonal_solSpaceStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.solvable_iff_orthogonal_solSpaceStar

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.fredholm_alternative_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.fredholm_alternative_of_bounded

/-! ### Resolvent bound and spectrum -/

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.resolvent_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.resolvent_bound

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.resolvent_bound_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.resolvent_bound_of_bounded

/-- info: 'EllipticPdes.Sobolev.spectrum_compact_operator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.spectrum_compact_operator

/-- info: 'EllipticPdes.Sobolev.solOp_spectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.solOp_spectral

/-- info: 'EllipticPdes.Sobolev.dirichlet_spectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.dirichlet_spectral

/-- info: 'EllipticPdes.Sobolev.dirichlet_spectral_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.dirichlet_spectral_of_bounded

/-- info: 'EllipticPdes.Sobolev.symmetric_fullElliptic_spectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.symmetric_fullElliptic_spectral

/-! ### Interior regularity -/

/-- info: 'EllipticPdes.Regularity.interior_H2_estimate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.interior_H2_estimate

/-- info: 'EllipticPdes.Regularity.interior_cutoffGrad_mem_H01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.interior_cutoffGrad_mem_H01

/-- info: 'EllipticPdes.Regularity.caccioppoli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.caccioppoli

/-! ### Higher interior regularity -/

/-- info: 'EllipticPdes.Regularity.HasWeakDeriv.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.HasWeakDeriv.unique

/-- info: 'EllipticPdes.Regularity.setIntegral_mul_partialD_cut_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.setIntegral_mul_partialD_cut_eq

/-- info: 'EllipticPdes.Regularity.outer_secondWeakDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.outer_secondWeakDeriv

/-- info: 'EllipticPdes.Regularity.localWeakForm_of_fullBilin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.localWeakForm_of_fullBilin

/-- info: 'EllipticPdes.Regularity.differentiated_weakForm_of_weakSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.differentiated_weakForm_of_weakSolution

/-- info: 'EllipticPdes.Regularity.higher_interior_regularity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.higher_interior_regularity

/-- info: 'EllipticPdes.Regularity.exists_gradClosed_of_hasIteratedWeakDerivOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.exists_gradClosed_of_hasIteratedWeakDerivOn

/-! ### Campanato's characterisation of Hölder continuity -/

/-- info: 'EllipticPdes.Campanato.campanato_holderOnWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Campanato.campanato_holderOnWith

/-- info: 'EllipticPdes.Campanato.campanatoOn_of_holderOnWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Campanato.campanatoOn_of_holderOnWith

/-! ### Boundary regularity -/

/-- info: 'EllipticPdes.Regularity.cutoffMulOn_tangDiffQuotG_mem_H01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.cutoffMulOn_tangDiffQuotG_mem_H01

/-- info: 'EllipticPdes.Regularity.HasWeakDerivOn.of_mul_contDiff_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.HasWeakDerivOn.of_mul_contDiff_left

/-- info: 'EllipticPdes.Regularity.exists_hasWeakDerivOn_of_mul_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.exists_hasWeakDerivOn_of_mul_diag

/-! ### Classical regularity -/

/-- info: 'EllipticPdes.Embedding.interior_holder_estimate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.interior_holder_estimate

/-- info: 'EllipticPdes.Embedding.interior_holder_estimate_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.interior_holder_estimate_two

/-- info: 'EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le

/-- info: 'EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le_of_le

/-- info: 'EllipticPdes.Embedding.exists_eLpNorm_six_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_eLpNorm_six_le

/-- info: 'EllipticPdes.Embedding.exists_eLpNorm_four_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_eLpNorm_four_le

/-- info: 'EllipticPdes.Embedding.interior_holder_estimate_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.interior_holder_estimate_one

/-- info: 'EllipticPdes.Embedding.memLp_two_mul_of_gradClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.memLp_two_mul_of_gradClosed

/-- info: 'EllipticPdes.Embedding.hasFDerivAt_of_continuousOn_hasWeakGradOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.hasFDerivAt_of_continuousOn_hasWeakGradOn

/-- info: 'EllipticPdes.Embedding.contDiffOn_of_gradClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.contDiffOn_of_gradClosed

/-- info: 'EllipticPdes.Regularity.interior_smooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.interior_smooth

/-- info: 'EllipticPdes.Embedding.memLp_of_gradClosed_fullStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.memLp_of_gradClosed_fullStep

/-- info: 'EllipticPdes.Embedding.memLp_two_mul_of_gradClosed_fullStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.memLp_two_mul_of_gradClosed_fullStep

/-- info: 'EllipticPdes.Embedding.contDiffOn_holder_of_gradClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.contDiffOn_holder_of_gradClosed

/-- info: 'EllipticPdes.Regularity.exists_gradClosed_of_hasIteratedWeakDerivOn_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.exists_gradClosed_of_hasIteratedWeakDerivOn_le

/-- info: 'EllipticPdes.Regularity.exists_contDiffOn_holder_ball_of_hasIteratedWeakDerivOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.exists_contDiffOn_holder_ball_of_hasIteratedWeakDerivOn

/-- info: 'EllipticPdes.Regularity.exists_contDiffOn_holder_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.exists_contDiffOn_holder_ball

/-! ### Base of the Poincaré chain -/

/-- info: 'EllipticPdes.Poincare.intervalIntegral_mul_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Poincare.intervalIntegral_mul_sq_le

/-- info: 'EllipticPdes.Poincare.poincare_oneDim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Poincare.poincare_oneDim

/-- info: 'EllipticPdes.Poincare.poincare_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Poincare.poincare_domain

/-- info: 'EllipticPdes.Poincare.poincare_H01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Poincare.poincare_H01

/-- info: 'EllipticPdes.Poincare.poincare_H01_euclBox' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Poincare.poincare_H01_euclBox

/-- info: 'EllipticPdes.Poincare.poincare_H01_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Poincare.poincare_H01_of_bounded

/-- info: 'EllipticPdes.Embedding.eLpNorm_le_of_mem_H01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.eLpNorm_le_of_mem_H01

/-- info: 'EllipticPdes.Embedding.eLpNorm_le_of_mem_H01_of_isBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.eLpNorm_le_of_mem_H01_of_isBounded

/-- info: 'EllipticPdes.Regularity.interior_holder_of_weakSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.interior_holder_of_weakSolution

/-- info: 'EllipticPdes.Embedding.eLpNorm_weakSolution_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.eLpNorm_weakSolution_le

/-- info: 'EllipticPdes.Analysis.eLpNorm_le_rpow_mul_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Analysis.eLpNorm_le_rpow_mul_rpow

/-- info: 'EllipticPdes.Embedding.rellichEmbL_isCompact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.rellichEmbL_isCompact

/-- info: 'EllipticPdes.Embedding.rellichEmbL_isCompact_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.rellichEmbL_isCompact_of_le

/-- info: 'EllipticPdes.Embedding.rellichEmbL_isCompact_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.rellichEmbL_isCompact_of_lt

/-- info: 'EllipticPdes.Embedding.exists_holderOnWith_of_gradClosed_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_holderOnWith_of_gradClosed_even

/-- info: 'EllipticPdes.Embedding.exists_const_eLpNorm_le_of_gradClosed_fullStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_const_eLpNorm_le_of_gradClosed_fullStep

/-- info: 'EllipticPdes.Embedding.exists_const_holderOnWith_of_gradClosed_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_const_holderOnWith_of_gradClosed_of_bound

/-- info: 'EllipticPdes.Embedding.not_isCompactOperator_critEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.not_isCompactOperator_critEmb

/-- info: 'EllipticPdes.Analysis.exists_weakLimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Analysis.exists_weakLimit

/-- info: 'EllipticPdes.Embedding.exists_minimiser_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_minimiser_of_lt

/-- info: 'EllipticPdes.Sobolev.exists_principal_eigenpair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.exists_principal_eigenpair

/-- info: 'EllipticPdes.Sobolev.principalEigenvalue_le_of_weak_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.principalEigenvalue_le_of_weak_eigen

/-- info: 'EllipticPdes.Sobolev.dirichlet_principal_eigenpair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.dirichlet_principal_eigenpair

/-- info: 'EllipticPdes.Sobolev.dirichlet_poincare_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.dirichlet_poincare_sharp

/-- info: 'EllipticPdes.Analysis.hasDerivAt_integral_abs_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Analysis.hasDerivAt_integral_abs_rpow

/-- info: 'EllipticPdes.Analysis.euler_lagrange_of_norm_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Analysis.euler_lagrange_of_norm_min

/-- info: 'EllipticPdes.Embedding.exists_weakSolution_semilinear_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_weakSolution_semilinear_of_lt

/-- info: 'EllipticPdes.Sobolev.exists_higher_eigenpair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.exists_higher_eigenpair

/-- info: 'EllipticPdes.Analysis.exists_bilin_minimiser' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Analysis.exists_bilin_minimiser
/-- info: 'EllipticPdes.Analysis.euler_lagrange_of_bilin_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Analysis.euler_lagrange_of_bilin_min
/-- info: 'EllipticPdes.Embedding.exists_weakSolution_dirichlet_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_weakSolution_dirichlet_of_lt
/-- info: 'EllipticPdes.Embedding.exists_weakSolution_dirichlet_of_lt'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_weakSolution_dirichlet_of_lt'
/-- info: 'EllipticPdes.Sobolev.dirichlet_principal_eigenpair_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.dirichlet_principal_eigenpair_of_bounded
/-- info: 'EllipticPdes.Sobolev.exists_eigen_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.exists_eigen_family

/-- info: 'EllipticPdes.Sobolev.dirichlet_eigen_family_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.dirichlet_eigen_family_of_bounded

/-- info: 'EllipticPdes.Sobolev.dirichlet_principal_eigenpair_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.dirichlet_principal_eigenpair_ball

/-- info: 'EllipticPdes.Sobolev.dirichlet_eigen_family_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.dirichlet_eigen_family_ball

/-- info: 'EllipticPdes.Sobolev.weak_eigenvalue_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.weak_eigenvalue_pos

/-- info: 'EllipticPdes.Sobolev.solOp_finiteDimensional_eigenspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.solOp_finiteDimensional_eigenspace

/-- info: 'EllipticPdes.Sobolev.dirichlet_eigenvalue_pos_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.dirichlet_eigenvalue_pos_ball

/-- info: 'EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le_compactSupport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le_compactSupport

/-- info: 'EllipticPdes.Embedding.memLp_of_gradClosed_compactSupport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.memLp_of_gradClosed_compactSupport

/-- info: 'EllipticPdes.Embedding.memLp_of_gradClosed_compactSupport_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.memLp_of_gradClosed_compactSupport_ideal

/-- info: 'EllipticPdes.Embedding.memLp_of_gradClosed_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.memLp_of_gradClosed_general

/-- info: 'EllipticPdes.Embedding.memLp_of_gradClosed_general_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.memLp_of_gradClosed_general_ideal

/-- info: 'EllipticPdes.Extension.hasWeakGradOn_comp_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.hasWeakGradOn_comp_reflect

/-- info: 'EllipticPdes.Extension.partialD_comp_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.partialD_comp_reflect

/-- info: 'EllipticPdes.Extension.hasWeakGradOn_comp_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.hasWeakGradOn_comp_translate

/-- info: 'EllipticPdes.Extension.partialD_comp_shear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.partialD_comp_shear

/-- info: 'EllipticPdes.Extension.hasWeakGradOn_comp_shear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.hasWeakGradOn_comp_shear

/-- info: 'EllipticPdes.Extension.hasWeakGradOn_chartExt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.hasWeakGradOn_chartExt

/-- info: 'EllipticPdes.Analysis.tendsto_eLpNorm_translate_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Analysis.tendsto_eLpNorm_translate_sub

/-- info: 'EllipticPdes.Extension.tendsto_eLpNorm_translate_convolution_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.tendsto_eLpNorm_translate_convolution_sub

/-- info: 'EllipticPdes.Embedding.exists_holderOnWith_of_gradClosed_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_holderOnWith_of_gradClosed_general

/-- info: 'EllipticPdes.Embedding.morreyExponent_eq_ladder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.morreyExponent_eq_ladder
