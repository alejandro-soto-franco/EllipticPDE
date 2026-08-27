# proofsense warrants

A [proofsense](https://github.com/alejandro-soto-franco/proofsense) manifest
pairing this development's audited results with the literature statements
they cite, so a claim of the form "this formalises Evans Theorem N" is checkable
rather than asserted. Two sources supply warrants: Evans for the existence,
Fredholm, spectral and interior-regularity chain, and Fernández-Real and
Ros-Oton for Campanato's characterisation of Hölder continuity.

proofsense supplies the formal verdict: a Lean declaration against the
literature statement it cites, yielding a relation, a trust rung and any defect.
adduce keeps the literature-claim side, meaning citations, the bibliography and
overlapping-claim detection.

## Running it

```
ANTHROPIC_API_KEY=... proofsense check proofsense/manifest.json
```

The source it reads is `latex/litreview/sources/transcribed-mineru/`, which is
gitignored: the transcriptions are of copyrighted textbooks and stay on the
machine that made them. A clone without them cannot run this, by design.

**The installed binary does not run this manifest, as of 2026-08-01.** Two
blockers, both ahead of any warrant in this file, so neither is evidence about
the warrants themselves:

- `proofsense check` requires `ANTHROPIC_API_KEY` and fails with
  `ANTHROPIC_API_KEY is not set; required for LlmEntailment` before reading a
  source.
- `proofsense check --stub`, which skips the judge, fails on the pre-existing
  Evans entry with a `parsing content_list JSON` error at line 2 column 1. The
  binary expects a MinerU `content_list.json` where the manifest supplies a
  Markdown transcription, and no `.json` file exists in the corpus.

The binary also exposes only `check`; there is no `resolve` subcommand, and
`check` spawns `lake exe proofsense-lean`, which this lakefile does not declare.
So no warrant in this manifest has been machine-checked end to end. What **is**
enforced in CI is `verify/proofsense_coverage.py`, which checks that every
declaration whose axioms `lean/AxiomAudit.lean` pins has a warrant or a recorded
exemption, and that no locator names a bare section. It passes.

## Locators naming theorems

A locator naming a section resolves to every theorem under that heading, and the
declaration is then asked to entail all of them, which is answered false almost
always. Measured across the nine warrants of the 2026-07-22 audit, section
granularity hands the judge 88,249 characters where statement granularity hands
it 7,617, which is 11.6 times as much. Section 6.3.1 alone has three theorems over
12,555 characters, of which `interior_H2_estimate` formalises one, at 1,304.

Every warrant here therefore names its theorem, `§6.3.1 Thm 1` rather than
`§6.3.1`, and `App. A (H3)` rather than the whole Hölder-space appendix.
`verify/proofsense_coverage.py` enforces this, admitting three forms: a numbered
result in a numbered section, a named result in a section that numbers none
(`§1.1 Thm (Sobolev inequality)`), and a labelled appendix property
(`App. A (H3)`). A bare section or a bare appendix fails.

## Coverage

Forty-two of the forty-nine declarations pinned in `lean/AxiomAudit.lean` have a
warrant. The seven that do not, and why:

| Declaration | State |
|---|---|
| `EllipticPdes.Regularity.caccioppoli` | No transcribed target. It states a first-derivative Caccioppoli estimate, which Evans proves inside §6.3.1 Theorem 1 rather than stating as a numbered result. Gilbarg and Trudinger Theorem 8.8 is the statement it matches, and the transcribed corpus omits that text. |
| `EllipticPdes.Poincare.poincare_domain` | Nothing to cite. It is the averaging step, taking `n` bounds over an arbitrary family and returning their average, with no gradient and no geometry. `poincare_H01_of_bounded` is the Poincaré inequality and is bound in `latex/.adduce/formalization.lock.toml`. |
| `EllipticPdes.Poincare.poincare_oneDim` | No transcribed target. It is the interval inequality `∫_a^b u² ≤ (b-a)²/2 ∫_a^b (u')²` for `u` continuously differentiable with `u(a) = 0` at the left endpoint alone. Evans §5.6.1 Theorem 3 is the `W_0^{1,p}` statement, which in one dimension asks `u` to vanish at both ends and names no constant, and §5.8.1 Theorems 1 and 2 subtract the mean over a connected `C¹` domain or over a ball. The manuscript records this lemma as the one new analytic ingredient of the Poincaré chain and prepares it for Mathlib. |
| `EllipticPdes.Poincare.poincare_H01` | Nothing to cite. It is the density step alone, taking an abstract constant `C` from the test functions to their closure in `H₀¹(Ω)`, with no geometry and no bound on `C`. Evans performs the corresponding passage inside the proof of §5.6.1 Theorem 3, by approximating `u ∈ W_0^{1,p}(U)` with `C_c^∞(U)` functions, and states no separate lemma. |
| `EllipticPdes.Embedding.hasFDerivAt_of_continuousOn_hasWeakGradOn` | No statement to name. It reads a continuous weak gradient as a classical derivative. Evans performs the passage inside the proof of §5.6.3 Theorem 6, where a weak derivative with a continuous representative is treated as a classical one, and states no separate lemma. |
| `EllipticPdes.Regularity.exists_gradClosed_of_hasIteratedWeakDerivOn` | Nothing to cite. Higher interior regularity is proved order by order, so the weak derivatives arrive as one family per order with nothing relating them, and this assembles them into a single family closed under differentiation, by uniqueness of the weak gradient on a ball. Evans writes `D^α u` as one symbol throughout and never faces the question. |
| `EllipticPdes.Campanato.campanatoOn_of_holderOnWith` | No statement to name. It is the converse of property (H3), which Fernández-Real and Ros-Oton record only as the space equality `L^{p,β} = C^{k,α}` in the remark following (H8), attributed to Janson, Taibleson and Weiss and proved there. The transcribed corpus omits that source. |

The first two were findings of the 2026-07-22 warrant audit
(`docs/review/2026-07-22-warrant-audit.md`). Neither was ever a live
misattribution in the manuscript: `caccioppoli` is cited nowhere in
`latex/manuscript`, and the adduce lock binds `poincare_H01_of_bounded`. The
audit judged the declarations against sections they had been pointed at during
that run.

## Known divergence

`dirichlet_weak_solution` cites Evans §6.2.2 Theorem 3, the First Existence
Theorem, which states that there is `γ ≥ 0` such that for every `μ ≥ γ` and
every `f ∈ L²(U)` the problem `Lu + μu = f` has a unique weak solution, for the
general operator `L`. The declaration proves Lax-Milgram existence for
`dirichletBilin`, the pure Dirichlet form `B[u,v] = ∑ᵢ ⟪∂ᵢu, ∂ᵢv⟫`, with no
drift, no zeroth-order term and no shift `μ`, taking the Poincaré bound as a
hypothesis rather than deriving coercivity from Gårding. It is more general in
the datum, admitting any continuous functional on `H₀¹` where Evans takes
`f ∈ L²`, and narrower in the operator, which is the point of the theorem it
cites. The general-operator statements are
`weak_solution_L2_of_nonneg_zeroth_of_bounded` and `existence_three_of_bounded`.
This pairing was the weakest of the four the 2026-07-22 audit let stand, at
confidence 0.70, and the audit judged it at section granularity.

`interior_H2_estimate` quantifies `u` over `H01 Ω`. Evans §6.3.1 Theorem 1
requires only `u ∈ H¹(U)` and its Remark (i) says `u ∈ H¹₀(U)` is not required,
so the declaration is a special case of the theorem it cites. The drift work of
2026-07-22 closed the other two grounds the audit raised, leaving this one.

The warrant claims `formalises` rather than `follows_from`, which is the
stricter reading and the one the manuscript makes. A run should report the
divergence rather than pass, and recording the weaker claim to obtain a pass
would hide a known difference.

`interior_holder_estimate` and `interior_holder_estimate_one` both cite Evans
§5.6.3 Theorem 6, whose case (ii) at `k = 2, p = 2, n = 3` and at
`k = 1, p = 2, n = 1` gives Hölder exponent `1/2` in each case. Two differences
stand. Evans states the theorem on a bounded open set with `C¹` boundary and
concludes on the closure, while both declarations are interior, stated on a ball
whose closure of the larger radius lies in the domain. Evans bounds the Hölder
norm by `‖u‖_{W^{k,p}}`, while both declarations bound it by `‖f‖ + ‖u‖`, having
already spent the interior `H²` estimate to reach the `W^{2,2}` norm. Neither
difference weakens the claim; both narrow it.

`spectrum_compact_operator` is cited in the manuscript to Brezis, *Functional
Analysis, Sobolev Spaces and Partial Differential Equations*, §6.3. The
transcribed corpus omits Brezis. Evans states the same theorem as Appendix D
Theorem 6, with
the third clause read as the disjunction that the nonzero spectrum is finite or
a sequence tending to zero, where the declaration states countability together
with finiteness above every `δ > 0`. The warrant therefore names Evans where
the manuscript names Brezis. The divergence lies between the two texts; the
declaration states what Evans Appendix D Theorem 6 states.

Appendix D numbers its theorems 1 to 7 straight through §D.1 to §D.6, so
`App. D (Thm 6)` names one statement. Appendix B labels the inequalities of
§B.2 by name rather than by number, so `App. B (Hölder's inequality)` names the
`p`-`q` conjugate-exponent inequality of item (e), which is distinct from the
general Hölder inequality of item (g).

The three Poincaré warrants all cite Evans §5.6.1 Theorem 3, which restricts to
`1 ≤ p < n` and so needs the hypothesis `n > 2` at `p = 2`. The declarations
hold in every dimension, since the box route through the one-dimensional
inequality and Fubini replaces the Gagliardo-Nirenberg-Sobolev route, and the
constant it yields is `C_P = L/√(2n)` in place of the sharp one. Evans exhibits
no constant at all.

`exists_eLpNorm_six_le` cites the Sobolev inequality of Fernández-Real and
Ros-Oton §1.1 rather than Evans §5.6.1, because the declaration is stated at the
`Lᵖ`-seminorm level on a pair of nested balls, which is closer to the
Fernández-Real form.
