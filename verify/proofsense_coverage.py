#!/usr/bin/env python3
"""
Warrant coverage between AxiomAudit.lean and the proofsense manifest.

`adduce formalize check` compares the LaTeX statement with the Lean declaration
that discharges it. The other link goes unchecked: whether the Lean declaration
states the theorem in the literature it cites. That link is proofsense's, and
this script requires its coverage, so a result cannot be presented as checked
against the literature when no warrant names it.

Three things are asserted:

  * every declaration audited in `lean/AxiomAudit.lean` either has a warrant
    in `proofsense/manifest.json` or appears in EXEMPT below with a reason;
  * every warrant names a declaration AxiomAudit.lean audits, so the manifest
    cannot drift onto a declaration whose axioms nothing pins;
  * every warrant's locator names a statement rather than a section, since a
    section locator hands the judge every theorem under the heading and makes
    the equivalent relation unreachable.

The transcribed sources are copyrighted and gitignored, so this runs without
them: it reads the manifest, not the literature. `proofsense resolve` is the
check that every locator hits a passage, and it needs the sources.

Run:  uv run python verify/proofsense_coverage.py
Exit code 0 iff covered.
"""

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
AUDIT = ROOT / "lean" / "AxiomAudit.lean"
MANIFEST = ROOT / "proofsense" / "manifest.json"

# Audited declarations with no warrant, and why. Adding a name here is a claim
# that no transcribed statement matches it, which the README under
# proofsense/ has to justify in prose.
EXEMPT = {
    "EllipticPdes.Sobolev.hasWeakGradOn_comp_affineBall": (
        "a weak gradient transported through the affine map of the unit ball onto a ball picks "
        "up the factor r. Evans performs the change of variables inside the proof of 5.8.1 "
        "Theorem 2, writing v(y) = u(x + r y) and reading Dv off without a lemma, so no "
        "transcribed statement matches it"
    ),
    "EllipticPdes.Extension.mem_W12_of_hasWeakGradOn": (
        "a class with an L^2 weak gradient, paired with it, lies in the graph space W12. It is "
        "the converse of the unpacking of that space's defining constraint and states nothing "
        "either text numbers; both define W^{1,2}(Omega) as the set of such classes"
    ),
    "EllipticPdes.Extension.hasC1Boundary_ball": (
        "the unit ball has C^1 boundary in the sense of Evans C.1 and Guo III.1.1. Both texts "
        "define the notion and neither states a lemma that a ball satisfies it, so no transcribed "
        "statement matches it; it is the instance that shows the boundary hypothesis of every "
        "bounded-domain theorem here is inhabited"
    ),
    "EllipticPdes.Regularity.hasWeakGradOn_of_contDiffOn": (
        "the classical gradient of a C^1 function on an open set is a weak gradient there, by "
        "integration by parts against a test function of compact support. Both texts read a "
        "classical derivative as a weak one without stating a lemma, Evans in 5.2.1 after the "
        "definition of the weak derivative and Guo in II.1, so no transcribed statement matches it"
    ),
    "EllipticPdes.Embedding.ae_const_of_hasWeakGradOn_zero": (
        "a class with zero weak gradient on a preconnected open set is constant almost "
        "everywhere. Evans uses it in the proof of 5.8.1 Theorem 1 and refers it to Problem 11 "
        "of Chapter 5, which is an exercise and not a numbered statement, so no transcribed "
        "statement matches it"
    ),
    "EllipticPdes.Extension.tendsto_eLpNorm_translate_convolution_sub": (
        "a shifted mollification converges in L^p to the function it started from. Evans "
        "performs the shift and the mollification together inside the proof of 5.3.3 Theorem 3 "
        "and states no lemma for their composition, so no transcribed statement matches it"
    ),
    "EllipticPdes.Analysis.tendsto_eLpNorm_translate_sub": (
        "continuity of translation in L^p. Evans uses it inside the proof of 5.3.3 Theorem 3, "
        "where the shift into the domain must be small in the norm, and states no "
        "lemma; Brezis states it as Lemma 4.3, which is not transcribed. Mathlib has the two "
        "halves, translation as an L^p isometry and density of the continuous compactly "
        "supported functions, and not the statement"
    ),
    "EllipticPdes.Extension.hasWeakGradOn_comp_translate": (
        "the change of variables for a weak gradient under a translation. Evans shifts the "
        "function into the domain in the proof of 5.3.3 Theorem 3 and reads the shifted "
        "derivative off without stating a lemma, so no transcribed statement matches it. It is "
        "the second of the two rigid motions the extension operator runs on, beside "
        "hasWeakGradOn_comp_reflect"
    ),
    "EllipticPdes.Extension.hasWeakGradOn_comp_reflect": (
        "the change of variables for a weak gradient under a coordinate reflection. Evans "
        "5.4 Theorem 1 reflects a C^1 function across the flat boundary of a half-ball and "
        "computes with classical derivatives throughout, stating no lemma about weak ones, so "
        "no transcribed statement matches it. It is the first step of the extension operator "
        "and is stated for an arbitrary set, since the boundary charts of that construction "
        "reflect across the image of a hyperplane"
    ),
    "EllipticPdes.Extension.eLpNorm_chartExt_le": (
        "the local half of clause (iii) of Evans 5.4 Theorem 1 for the class itself: the "
        "extension across one C^1 chart is bounded by twice the seminorm over the region above "
        "the graph, both shears preserving measure and the reflection doubling. Evans states "
        "the bound for the assembled operator over the whole domain and proves the local pieces "
        "inline, so no transcribed statement matches a single chart"
    ),
    "EllipticPdes.Extension.eLpNorm_chartExtGrad_le": (
        "the same clause for the gradient: componentwise, twice the seminorm of the matching "
        "component plus four times the chart's gradient bound against the normal one. The three "
        "maps each contribute, the shear costing the chart's bound against the normal component, "
        "the reflection doubling, and the inverse shear costing the bound once more. Evans "
        "states no local bound of this shape"
    ),
    "EllipticPdes.Extension.hasWeakGradOn_chartExt": (
        "the local half of the extension operator: a class with a weak gradient above the graph "
        "of a C^1 chart extends across that graph, the extension being the flattened class "
        "reflected across the interface and returned through the inverse chart. Evans 5.4 "
        "Theorem 1 performs the straightening and the reflection inside one proof and states no "
        "lemma for the composite, and it works throughout with a function smooth up to the "
        "boundary, reaching W^{1,p} by density, so no transcribed statement matches a weak "
        "gradient. exists_extension_bound patches the local pieces over a finite cover of the "
        "boundary, which is the remaining step of that theorem"
    ),
    "EllipticPdes.Extension.exists_extension_subset": (
        "clauses (i) and (ii) of Guo III.2.2 together: the extension agrees with the class on the "
        "domain and is supported inside any open set the closure of the domain sits in. Guo "
        "reaches (ii) by multiplying by a cutoff equal to one on the domain, which is what this "
        "does. exists_extension_subset_bound adds clause (iii), the norm bound. Neither builds the "
        "operator as a bounded linear map, so each statement is an existence with an estimate"
    ),
    "EllipticPdes.Extension.exists_extension": (
        "step 3 of Guo's proof of III.2.2, the sum of the local extensions against a partition of "
        "unity, which extends the class across the whole boundary and agrees with it on the "
        "domain. That is clause (i) of the theorem together with the existence of the extension's "
        "weak gradient; exists_extension_subset states clause (ii) on the support and "
        "exists_extension_bound clause (iii) on the norm. Steps of a proof are not "
        "transcribed statements, so no locator matches"
    ),
    "EllipticPdes.Extension.exists_localExtension_bound": (
        "the local half of clause (iii) of Guo III.2.2, at every exponent p >= 1: near a "
        "boundary point the extension is bounded by the class and its gradient over the "
        "domain, with a constant reading off the chart alone. Evans 5.4 Theorem 1 and Guo "
        "both prove the local bound inside the proof of the assembled operator and state no "
        "lemma for a single chart, so no transcribed statement matches it"
    ),
    "EllipticPdes.Extension.exists_localExtension": (
        "step 2 of Guo's proof of III.2.2: near a boundary point the class extends across the "
        "boundary, agreeing with the original on the part of the domain the neighbourhood meets. "
        "That is a step of a proof rather than a numbered statement, and Evans 5.4 Theorem 1 "
        "performs the same passage inside its own proof, so no transcribed statement matches it. "
        "Guo runs the step on a function smooth up to the boundary and reads the chain rule off "
        "it; every step here is a weak gradient"
    ),
    "EllipticPdes.Extension.nonempty_boundaryPartition": (
        "the cover and the partition of unity that step 3 of Guo's proof of III.2.2 glues with, "
        "bundled. Guo takes the partition for granted in one clause of that step and states no "
        "lemma for it, so no transcribed statement matches it. Mathlib proves the partition for "
        "a manifold; a normed space is one over itself, and the smoothness of each piece is read "
        "back as ContDiff so that nothing downstream meets a manifold"
    ),
    "EllipticPdes.Extension.exists_finite_chart_cover": (
        "the finite subcover of the boundary that opens step 3 of Guo's proof of III.2.2, where "
        "he writes that the boundary being compact there are finitely many points whose "
        "neighbourhoods cover it. That is a step of a proof rather than a statement of its own, "
        "so no transcribed statement matches it. The dimension is asked to be positive, since a "
        "chart names a direction for its graph and dimension zero has none"
    ),
    "EllipticPdes.Extension.hasWeakGradOn_mul_cutoff_inter": (
        "the product rule for a weak gradient against a cutoff whose support straddles the "
        "boundary of the set, which is what a boundary chart's ball does. Guo glues the local "
        "extensions with a partition of unity in step 3 of the proof of III.2.2 and states no "
        "lemma for the cutoff of a single piece, so no transcribed statement matches it. "
        "hasWeakGradOn_univ_mul_cutoff is the case where the cutoff sits inside the set, where "
        "the conclusion reaches the whole space"
    ),
    "EllipticPdes.Extension.hasWeakGradOn_comp_linearIsometry": (
        "the change of variables for a weak gradient under the relabelling and reorientation of "
        "the coordinate axes, which Evans C.1 asks for in the definition of a C^1 boundary and "
        "which every chart of that definition begins with. Both texts change the axes without "
        "comment and state no lemma about what it does to a weak gradient, so no transcribed "
        "statement matches it. It generalises hasWeakGradOn_comp_reflect, whose sum has a single "
        "term and a sign"
    ),
    "EllipticPdes.Extension.hasWeakGradOn_comp_shear": (
        "the change of variables for a weak gradient under the shear that flattens a C^1 "
        "boundary. Evans 5.4 Theorem 1 straightens the boundary near a boundary point and works "
        "with the straightened function from there on, stating no lemma about the weak gradient "
        "of a composition with the chart, so no transcribed statement matches it. It is the third "
        "of the three maps the extension operator runs on, beside hasWeakGradOn_comp_reflect and "
        "hasWeakGradOn_comp_translate, and the only one whose derivative is not an isometry"
    ),
    "EllipticPdes.Extension.partialD_comp_shear": (
        "the chain rule for a partial derivative under the shear that flattens a C^1 boundary, "
        "which is the classical computation Evans performs inline in the proof of 5.4 Theorem 1 "
        "and states as no lemma of its own"
    ),
    "EllipticPdes.Extension.partialD_comp_reflect": (
        "the chain rule for a partial derivative under a coordinate reflection, which is the "
        "classical computation Evans performs inline in the proof of 5.4 Theorem 1 and states "
        "as no lemma of its own"
    ),
    "EllipticPdes.Regularity.caccioppoli": (
        "states a first-derivative Caccioppoli estimate, which Evans proves "
        "inside 6.3.1 Theorem 1 rather than stating as a numbered result; "
        "Gilbarg and Trudinger Theorem 8.8 is the match and is not transcribed. "
        "Guo Lemma X.3.5 carries the name but states the non-negative "
        "subsolution form with no datum, so it is a different lemma"
    ),
    "EllipticPdes.Poincare.poincare_domain": (
        "the averaging step over an arbitrary family, with no gradient and no "
        "geometry, so there is nothing to cite; poincare_H01_of_bounded is the "
        "Poincare inequality and is bound in the adduce lock"
    ),
    "EllipticPdes.Poincare.poincare_oneDim": (
        "the one-dimensional inequality on an interval, for u continuously "
        "differentiable with u a = 0 at the left endpoint alone, and with the "
        "explicit constant (b - a)^2 / 2. Evans 5.6.1 Theorem 3 is the "
        "W_0^{1,p} statement, which in one dimension asks u to vanish at both "
        "ends and names no constant, and 5.8.1 Theorems 1 and 2 subtract the "
        "mean over a connected C^1 domain or over a ball. The manuscript "
        "records this lemma as the one new analytic ingredient of the Poincare "
        "chain and prepares it for Mathlib, so no transcribed statement "
        "matches it"
    ),
    "EllipticPdes.Poincare.poincare_H01": (
        "the density step alone, carrying an abstract constant C from the test "
        "functions to their closure in H_0^1(Omega), with no geometry and no "
        "bound on C. Evans performs the corresponding passage inside the proof "
        "of 5.6.1 Theorem 3, by approximating u in W_0^{1,p}(U) with "
        "C_c^infty(U) functions, and states no separate lemma; "
        "poincare_H01_euclBox and poincare_H01_of_bounded are the inequality "
        "itself and carry the warrants"
    ),
    "EllipticPdes.Embedding.hasFDerivAt_of_continuousOn_hasWeakGradOn": (
        "a continuous function with a continuous weak gradient is Frechet "
        "differentiable with that gradient. Evans performs the passage inside "
        "the proof of 5.6.3 Theorem 6, where a weak derivative with a "
        "continuous representative is read as a classical one, and states no "
        "separate lemma, so no transcribed statement matches it"
    ),
    "EllipticPdes.Regularity.exists_gradClosed_of_hasIteratedWeakDerivOn": (
        "bookkeeping with no analytic content of its own: higher interior "
        "regularity is proved order by order, so the weak derivatives arrive "
        "as one family per order with nothing relating them, and this "
        "assembles them into a single family closed under differentiation, by "
        "uniqueness of the weak gradient on a ball. Evans carries D^alpha u as "
        "one symbol throughout and never faces the question"
    ),
    "EllipticPdes.Regularity.exists_gradClosed_of_hasIteratedWeakDerivOn_le": (
        "the same bookkeeping at a bounded order, where the whole supply is "
        "one family and nothing has to be reconciled, so it is a restatement "
        "of HasIteratedWeakDerivOn on a ball rather than a result. Evans "
        "carries D^alpha u as one symbol throughout and never faces the "
        "question"
    ),
    "EllipticPdes.Embedding.not_isCompactOperator_critEmb": (
        "the sharpness of the range in 5.7 Theorem 1. Evans states compactness "
        "for q < p* and says nothing of the endpoint, and the scaling family "
        "that rules it out is Guo's Example IV.2.11, which is not among the "
        "transcribed sources, so no transcribed statement matches it. The "
        "compactness it complements is warranted at rellichEmbL_isCompact_of_lt"
    ),
    "EllipticPdes.Embedding.eLpNorm_weakSolution_le": (
        "the composition of 5.6.1 Theorem 3 with the a priori bound of 6.2.2 "
        "Theorem 3: the solution's L^q seminorm bounded by the L^2 norm of "
        "the datum, for every q up to the critical exponent. Evans states "
        "each factor and draws no such conclusion for the solution, so no "
        "transcribed statement matches it. The two factors are warranted at "
        "eLpNorm_le_of_mem_H01_of_isBounded and at "
        "weak_solution_L2_of_nonneg_zeroth_of_bounded"
    ),
    "EllipticPdes.Regularity.interior_holder_of_weakSolution": (
        "the finite-order form of the composition Evans performs inside the "
        "proof of 6.3.1 Theorem 3: higher interior regularity supplies the "
        "weak derivatives and 5.6.3 Theorem 6 clause (ii) converts them. His "
        "numbered statement is the C^infty one, under coefficients and datum "
        "of every order, which interior_smooth formalises; at finite order he "
        "draws no separate conclusion and keeps no Holder exponent, so no "
        "transcribed statement matches it. The two factors are warranted at "
        "higher_interior_regularity and exists_contDiffOn_holder_ball"
    ),
    "EllipticPdes.Campanato.campanatoOn_of_holderOnWith": (
        "the converse half of the Campanato characterisation; Fernandez-Real "
        "and Ros-Oton record only the space equality, attributed to Janson, "
        "Taibleson and Weiss, which is not transcribed, so no transcribed "
        "statement matches the direction this declaration proves"
    ),
    "EllipticPdes.Sobolev.exists_higher_eigenpair": (
        "obtains a later eigenpair by minimising the Rayleigh quotient over "
        "the part of the unit sphere orthogonal to a finite family of "
        "eigenfunctions. Evans reaches the later eigenvalues only through the "
        "spectral theorem for the compact self-adjoint solution operator, "
        "6.5.1 Theorem 1, and states no theorem that a constrained minimum is "
        "an eigenpair; the ordering appears as a Remark after 6.5.1 Theorem 2 "
        "rather than as a statement, and Courant's min-max is in neither "
        "transcribed source, so no transcribed statement matches it. The "
        "unconstrained case is warranted at exists_principal_eigenpair"
    ),
    "EllipticPdes.Analysis.hasDerivAt_integral_abs_rpow": (
        "differentiation under the integral sign for the L^q functional, a "
        "step Evans takes inside the proof of 8.4.1 Theorem 2 and states as "
        "no numbered result; the dominated convergence he cites is 'the "
        "dominated convergence theorem' of Appendix E.3, which is not "
        "transcribed. The theorem it serves is warranted at "
        "euler_lagrange_of_norm_min"
    ),
    "EllipticPdes.Sobolev.dirichlet_poincare_sharp": (
        "reads the principal eigenvalue as the optimal constant in the "
        "Poincare inequality. Evans records 0 < lambda_1 in the definition "
        "preceding 6.5.1 Theorem 2 and never states it as a Poincare "
        "constant, and the transcribed Poincare inequalities, 5.6.1 Theorem 3 "
        "and 5.8.1 Theorems 1 and 2, name no constant at all, so no "
        "transcribed statement matches it. The variational principle it reads "
        "is warranted at exists_principal_eigenpair"
    ),
}

# A statement locator names one statement, never a whole section. Three forms
# name one, and a bare section number names none of them:
#
#   §6.3.1 Thm 1                  a numbered result inside a numbered section
#   §7.11 Lemma 7.23              a result numbered by chapter inside a numbered section
#   §I.2 Lemma I.2.4              the same with the chapter in roman numerals
#   §1.1 Thm (Sobolev inequality) a named result in a section that numbers none
#   App. A (H3)                   a labelled property in a lettered appendix
#
# The chapter-numbered form arrived with Gilbarg and Trudinger, who number every
# result by chapter, and the roman form with Guo, whose chapters are roman. The named and lettered forms arrived with the Fernandez-Real and Ros-Oton text,
# which numbers its appendix properties (H1) to (H8) and leaves several chapter
# theorems unnumbered. Restricting the rule to the first form would have forced
# a warrant for either to cite the enclosing section, which is the failure this
# script exists to prevent.
_MARKER = r"Thm|Theorem|Lem|Lemma|Cor|Corollary|Def|Definition|Rmk|Remark|Prop|Proposition"
STATEMENT_LOCATOR = re.compile(
    rf"""^(?:
          §?\s*(?:\d+|[IVX]+)(?:\.\d+)*\s+(?:{_MARKER})\s*(?:(?:\d+|[IVX]+)(?:\.\d+)*|\([^)]+\))
        | (?:App\.?|Appendix)\s*[A-Z]\s*\([^)]+\)
      )$""",
    re.IGNORECASE | re.VERBOSE,
)


def audited_declarations(path: Path) -> list[str]:
    """Every declaration `#print axioms` pins in AxiomAudit.lean, in file order."""
    text = path.read_text(encoding="utf-8")
    return re.findall(r"^#print axioms\s+(\S+)\s*$", text, re.MULTILINE)


def check(audited: list[str], warrants: list[dict], exempt: dict) -> list[str]:
    """Every way the manifest and AxiomAudit.lean can disagree, as failure lines."""
    warranted = {w["decl"] for w in warrants}
    failures: list[str] = []

    for decl in audited:
        if decl not in warranted and decl not in exempt:
            failures.append(
                f"{decl} is audited but carries no warrant and is not exempt"
            )

    for decl in sorted(d for d in exempt if d not in audited):
        failures.append(f"{decl} is exempt but AxiomAudit.lean no longer audits it")

    for decl in sorted(warranted & set(exempt)):
        failures.append(f"{decl} is both warranted and exempt; drop the exemption")

    for decl in sorted(d for d in warranted if d not in audited):
        failures.append(
            f"{decl} carries a warrant but AxiomAudit.lean does not audit it"
        )

    for w in warrants:
        if not STATEMENT_LOCATOR.match(w["locator"]):
            failures.append(
                f"{w['decl']} cites {w['locator']!r}, which names a section "
                f"rather than a statement"
            )

    return failures


def main() -> int:
    for path in (AUDIT, MANIFEST):
        if not path.exists():
            print(f"missing {path}", file=sys.stderr)
            return 2

    audited = audited_declarations(AUDIT)
    if not audited:
        print(f"no `#print axioms` lines found in {AUDIT}", file=sys.stderr)
        return 2

    warrants = json.loads(MANIFEST.read_text(encoding="utf-8")).get("warrants", [])
    failures = check(audited, warrants, EXEMPT)

    for failure in failures:
        print(f"  FAIL  {failure}")

    warranted = {w["decl"] for w in warrants}
    exempt_count = len([d for d in audited if d in EXEMPT])
    uncovered = len([d for d in audited if d not in warranted and d not in EXEMPT])
    print(
        f"\n{len(audited)} audited declarations: "
        f"{len(audited) - exempt_count - uncovered} warranted, "
        f"{exempt_count} exempt, {uncovered} uncovered"
    )

    if failures:
        print(f"{len(failures)} failure(s)")
        return 1

    print("covered")
    return 0


if __name__ == "__main__":
    sys.exit(main())
