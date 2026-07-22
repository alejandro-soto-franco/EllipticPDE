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

/-- info: 'EllipticPdes.Regularity.caccioppoli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.caccioppoli

/-! ### The Poincaré chain the development reduces to -/

/-- info: 'EllipticPdes.Poincare.poincare_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Poincare.poincare_domain
