/-
Axiom gates for the headline results.

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

/-! ### The Gårding inequality -/

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.garding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.garding

/-! ### The Fredholm alternative -/

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.solvable_iff_orthogonal_solSpaceStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.solvable_iff_orthogonal_solSpaceStar

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.fredholm_alternative_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.fredholm_alternative_of_bounded

/-! ### The resolvent bound and the spectrum -/

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.resolvent_bound_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.resolvent_bound_of_bounded

/-- info: 'EllipticPdes.Sobolev.dirichlet_spectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.dirichlet_spectral

/-- info: 'EllipticPdes.Sobolev.dirichlet_spectral_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.dirichlet_spectral_of_bounded

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

/-- info: 'EllipticPdes.Embedding.exists_eLpNorm_six_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_eLpNorm_six_le

/-- info: 'EllipticPdes.Embedding.interior_holder_estimate_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.interior_holder_estimate_one

/-! ### The Poincaré chain the development reduces to -/

/-- info: 'EllipticPdes.Poincare.poincare_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Poincare.poincare_domain
