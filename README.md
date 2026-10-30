# Uniform attachment with freezing

[![CI](https://github.com/igor-kortchemski/uniform-attachment-with-freezing/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/igor-kortchemski/uniform-attachment-with-freezing/actions/workflows/ci.yml)
[![Comparator](https://github.com/igor-kortchemski/uniform-attachment-with-freezing/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/igor-kortchemski/uniform-attachment-with-freezing/actions/workflows/ci.yml)

**All Introduction theorem conclusions T01–T07, the unordered binary bijection P01 and tangent/Bernoulli enumeration C01 are proved; whole-paper coverage remains incomplete.** This project develops Lean proofs for *Uniform attachment with
freezing*, by Étienne Bellin, Arthur Blanc-Renaudie, Emmanuel Kammerer, and Igor
Kortchemski. The supplied [manuscript](attachement-uniforme-1-final.tex) is preserved
unchanged. The [coverage report](FORMALIZATION_REPORT.md) retains all 24 named result
environments, substantive unnamed claims, open questions, and source issues.

The badges refer to an earlier partial snapshot in the private repository and
to the same aggregate CI workflow. The current local proofs are ahead of that
snapshot and nothing has been uploaded; the badges do not verify the local
development or a Palomar candidate. See the report for current evidence.

**Certification interface for T01–T07 (prepared locally, not yet verified by the
official tools).** `Challenge/` and `Solution/` state the seven main theorems
(twenty conclusions) in four self-contained interfaces, one Comparator
configuration each (`comparator/{locallimits,heights,samelaw,sir}.json`):
T01–T02, T03–T04, T05, T06–T07. This is **not** a certification of the whole
manuscript. The correspondence with the manuscript, the independent statement
reviews, the local comparison and kernel-replay evidence, and the exhaustive list of
limits are in [verification/certification/](verification/certification/README.md)
([correspondence](verification/certification/MAIN_RESULTS_CORRESPONDENCE.md),
[open obligations](verification/certification/OPEN_OBLIGATIONS.md)). The official
`lake comparator` (Linux sandbox) and the Palomar mechanical report have not been
run; the workflows `.github/workflows/{comparator,palomar}.yml` are prepared and
unrun.

For the actual forward random-tree law, the development proves the normalized
uniform-active height limit in every real $L^p$, the universal maximum-height
window, and the maximum-height $L^p$ limit when $\log n=o(h_n^+)$. It constructs
both forward and reverse graph laws, their invariants and graph heights, and the
uniform birth-time law on the constructed reverse tree. A coherent reverse
history now proves the full-history conditional increment law, independent
increments for each fixed vertex, and the corrected distinct-vertex
coalescence-time distribution. Equal vertices are handled separately. Uniform-pair
coalescence tends to zero after division by $n$, and a stronger logarithmic
estimate is proved under the full linear assumptions. The linear regime now
has the exact height-scale limit, the uniform-all-vertex limit for every real
$p\ge1$, the pair-distance limit in every real $L^p$,
and the maximum-height limit in probability. The local-convergence criterion T01 is proved, with its common limit law. The geometric Bienaymé identification T02 is also proved for the actual iid-sign process. For the constructed embedded SIR model, both local conclusions of T06 are proved. The strong-infection uniform population limit T07.II(a) is also proved for the embedded model. All three terminal geometry limits in T07.II(b) are now proved for the embedded model: uniform height, independent-pair distance and maximum have logarithmic limits $1$, $2$ and $e$. The finite-rate height/distance weak mixtures are also proved, on the same concrete geometric survival event. `SIRPhysicalLimits` and `SIRPhysicalFiniteLimits` transfer every SIR main conclusion to the actual full-contact protocol supplied with the source's independent recovery/Poisson process data; rate positivity is derived eventually.

Supporting results include $h_n^+\ge\log(n/4)$, exact finite counts, the coefficient
$f(c)$, Bennett concentration and all-real-power moment estimates. A fully
probabilistic counterexample refutes the printed finite maximum-height upper
bound; the actual reverse bound is proved with the true number of vertices.
Stamped reverse histories preserve all edge times and frozen labels, with
verified reconstruction and probability products. The exact active-label fibres
and reconstructed forward support now prove construction equivalence (T05),
including extinction. The corrected fixed-schedule support and mass formula
of L04 are also proved; its literal overly broad support remains false. Exact
canonical sampling preserves the joint law of two heights and their distance.
Timestamped cuts identify the actual forward block counts, proving the mean
lower bound L12, concentration lemma L10 and component-size bound L11. True tagged continuation, permutation averaging and a corrected initial population now complete the maximum lower bound.

The SIR development constructs actual population and infection-tree path laws,
proves their exact count projection and finite absorption, and establishes the
geometric local limit and strong-infection non-tightness in
[Freezing1/MainSIREmbedded.lean](Freezing1/MainSIREmbedded.lean).
[Freezing1/SIRSusceptibleFluid.lean](Freezing1/SIRSusceptibleFluid.lean) proves
the auxiliary susceptible and integer infectious fluid limits for general
asymptotic rates. The complete positive-rate physical history bridge is proved from the original independent clock array and the actual whole-contact next-point protocol. The zero-rate branch now has a genuine empty-contact carrier, an actual next-event protocol and complete tree/count laws. Compatibility with the positive-path protocol is proved. Complete tree/count prefixes are also identified jointly with the original adaptive-word forward process; the main asymptotic transfers do not require uniform positivity.

The degree/local-convergence equivalence and the corrected conditional
independence/Borel–Cantelli argument are now checked separately from T01.
The exact uniform-active Bernoulli representation and its Bennett bounds
also verify A33 by the paper's strategy. Actual finite adjacent swaps now verify
the harmonic-bound proof A32; real tail integrals, the split at 7 and exact
dilation verify A34, with a logarithmic-envelope proof of the tail asymptotic. Full augmented cut forests have
proved past independence and uniform root matching; the marked-root clock
correction and remaining conditional bare-forest formulas stay explicit.
The arbitrary plane labelled local topology is proved, while the broader
unordered-labelled realization remains under development.

The three local-convergence equivalences and the common limit are in
[Freezing1/MainLocalLimit.lean](Freezing1/MainLocalLimit.lean). The iid-sign geometric Bienaymé limit T02 is proved in [Freezing1/MainGeometricLimit.lean](Freezing1/MainGeometricLimit.lean), including chronological ordering, extinction and $p=0$. The source iid extinction/drift and unique increasing reindexing arguments A28 are also proved. The random-birth conditional mean, Bennett/layer-cake moments and corrected harmonic tail now check the paper's own uniform-height proof A40–A43. The requested T01–T02 milestone is complete. See [CLAUDE_HANDOFF.md](CLAUDE_HANDOFF.md) for current evidence and the remaining whole-paper obligations; publication remains suspended.

For the height results, start with [Freezing1/MainHeight.lean](Freezing1/MainHeight.lean) and
[Freezing1/MainMaximum.lean](Freezing1/MainMaximum.lean), then
[Freezing1/MainLinearHeightScale.lean](Freezing1/MainLinearHeightScale.lean) and
[Freezing1/MainLinearUniformHeight.lean](Freezing1/MainLinearUniformHeight.lean), [Freezing1/MainLinearDistance.lean](Freezing1/MainLinearDistance.lean)
and [Freezing1/MainLinearMaximumLower.lean](Freezing1/MainLinearMaximumLower.lean).
[Freezing1.lean](Freezing1.lean) imports the maintained proof library.

| Module | Content |
| --- | --- |
| `Path`, `Extinction` | Signs, integer walk, counts, first zero, exact survival criterion |
| `HeightScale` | Harmonic comparison, logarithmic bound and triangular-array divergence |
| `BirthTime` | Disjoint active/frozen labels, uniform probability measure and birth law |
| `IntervalCounts` | Exact interval counts and the bounds in `EqProp9` |
| `RateFunction` | Definition and characterization of $f(c)$ and analytic Bennett rates |
| `BernoulliConcentration` | Two Bennett tails, derived from Bernoulli laws and independence |
| `ForwardTree`, `ForwardLaw`, `ForwardLabels`, `ForwardAbsorption` | Genuine forward trees, uniform choices, graph distances, labels, counts and stopping |
| `RootedForest`, `RootedForestLaw`, `ReverseForest` | Root merges, the reverse random graph construction, components, terminal labels and birth law |
| `ForwardHeight`, `ForwardMaximum` | Actual height distributions, MGF recurrences and finite maximum tails |
| `BernoulliLimits`, `BernoulliArrayLimits`, `MGFLimits`, `MaximumMGFLimits` | Every real-power moment limit, including varying probability spaces |
| `MainHeight`, `MainMaximum` | All three parts of Theorem `thm:height` |
| `LinearRegimeAssumptions`, `LinearRegimeIntervals`, `LinearRegimeUniform` | Exact nested-limit hypotheses and Lemma 8, using Abel summation |
| `HeightScaleBounds`, `LinearRegimeCutoffs`, `MainLinearHeightScale` | Integer cutoffs, negligible early/late pieces and Theorem `thm:lineaire` I |
| `ForwardUniformHeight`, `ForwardHeightOrder`, `ForwardUniformHeightTails` | Actual sampling over all vertices, exact birth mixture and finite tails |
| `CenteredMGFLimits`, `MainLinearUniformHeight`, `LinearMaximumUpper`, `MainLinearMaximumLower` | Linear-regime uniform-vertex $L^p$ limit and complete maximum-height limit in probability |
| `ForwardScheduleSupport`, `RootedForestCoalescence` | Corrected fixed-schedule support and genuine one-step component coalescence |
| `BernoulliProductLaw`, `ReverseHeightLaw`, `ReverseHeightBounds` | Actual birth-truncated height laws and corrected finite reverse maximum tails |
| `ReverseHistory`, `ReverseHistoryHeight`, `ReverseHistoryBernoulli` | Coherent history, conditional increments, mutual independence for one vertex and telescoping |
| `ReverseSeparationLaw`, `ReverseCoalescenceTime` | Actual phase products, corrected coalescence-time distribution and diagonal law |
| `CoalescenceBounds`, `UniformCoalescence`, `CoalescenceLimits`, `CoalescenceLogScale` | Actual independent uniform sampling, all-label hazard bounds, L09 and stronger logarithmic decay |
| `ForwardReconstruction`, `ForwardHistorySupport`, `ForwardPointMass` | Unique legal histories, actual support and exact forward atom masses |
| `ReverseStampedForest`, `ReverseTimestampSupport`, `ReverseTimestampOrder` | Actual edge timestamps, exact schedule support and increasing labels |
| `CanonicalTreeObservable`, `ReverseStampedReconstruction`, `ReverseStampedPointMass` | Common graph observable, history reconstruction and actual reverse probability products |
| `PoissonLowerTail`, `PoissonApproximation`, `BlockAttachmentParameters` | Strict Poisson tail scale, proved Le Cam event bound and exact block parameters |
| `ReverseHistoryBlocks`, `ReverseHistoryBlockCount`, `MainLinearBlockCount` | Actual block increments, random-root first moment and reverse counterpart of L12 |
| `CanonicalPairSampling`, `CanonicalMaximum`, `UniformPairDistance`, `MainLinearDistance` | Actual joint sampling, maximum transfer and linear-regime distance in every real $L^p$ |
| `ReversePairHeightKernel`, `ReversePairHeightBlocks`, `ReversePairHeightVariance` | Actual pair-tail comparison, coalescence error and root-count variance |
| `CanonicalCutForest`, `CanonicalCutHeight`, `ForwardBlockCountLaw`, `MainForwardBlockConcentration`, `MainLinearComponentMaximum` | Verified forward cut graphs and literal L10–L12 |
| `PolyaBernoulliMGF`, `SignedUrn`, `SignedUrnContinuation`, `SignedUrnConcentration` | Actual signed urn, finite MGF and endpoint concentration; `SignedUrnInfinite` proves the maximal Markov-path formulation, with the source filtration issue retained |
| `HistoryProbability`, `UniformRootPair` | Factorial history identity and exact finite pair probabilities |
| `SourceChecks`, `TreeSourceChecks` | Scalar and actual reverse-tree counterexamples at $n=1$ |

Lean and Mathlib are pinned to **v4.35.0**; the manifest fixes every dependency
revision. Install [Elan and Lean tooling](https://leanprover-community.github.io/install/project.html),
open this folder in VS Code, and run from the project root:

```sh
lake exe cache get
lake build
lake env lean scripts/AxiomAudit.lean
```

For an authorized user of the private repository, the clone command is:

```sh
git clone https://github.com/igor-kortchemski/uniform-attachment-with-freezing.git
cd uniform-attachment-with-freezing
```

The repository was created privately on 29 October 2026. Do not use `lake update`
to reproduce this snapshot.

[Challenge.lean](Challenge.lean), [Solution.lean](Solution.lean), and
[comparator.json](comparator.json) retain the earlier 16 supporting-result
interface. They do not yet include the new main-result declarations. Challenge imports only Mathlib and contains complete proofs to avoid
introducing any proof holes. Its statements were independently audited; the
copied proof implementations are **not** independent proofs. On Linux with
Bubblewrap installed, run:

```sh
lake comparator --config comparator.json
```

Comparator is not the full Palomar verification. The prepared manual Palomar
workflow is restricted to public repositories; the requested private repository
cannot currently be deposited. Whole-paper completion, source repairs, and the
full official mechanical report remain outstanding.

The code and original project documentation use [Apache-2.0](LICENSE).
Contributor and responsible maintainer: **Igor Kortchemski**, as requested.
Codex and collaborating automated agents assisted with proofs and audits;
no human review or endorsement is claimed. See [CITATION.cff](CITATION.cff) for
artifact and paper credits, and [NOTICE](NOTICE) for third-party rights. The code
license does not relicense the manuscript or the bundled workflow skills.

Contributions should preserve the pinned environment and mathematical statements,
update the coverage report, and pass the commands above. Follow the local
[project instructions](AGENTS.md) and [Lean skill index](.agents/README.md).


The latest source-proof milestone includes the full unordered local topology
and closed chronological-model embedding, T01/T02 consumers in that ambient,
actual scalar interleaved-chain factorizations, repaired geometric L08,
full-forest conditional covariance/Chebyshev/tower growth, the quantitative
Poisson polynomial bound, and the positive infinite-urn component-tail route.
The source reverse-SIR coupling and other explicitly retained obligations
remain open. See the coverage report and continuation checkpoint for current
proof evidence; this remains a partial development rather than a verified
whole-paper publication candidate.
