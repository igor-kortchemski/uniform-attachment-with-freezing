# Module map

A partial guide to the `Freezing1` library: 647 modules under
[`Freezing1/`](../Freezing1), imported through [`Freezing1.lean`](../Freezing1.lean).
The statement-level correspondence with the paper is in
[MAIN_RESULTS_CORRESPONDENCE.md](../verification/certification/MAIN_RESULTS_CORRESPONDENCE.md),
and the status of every result of the paper is in
[FORMALIZATION_REPORT.md](../FORMALIZATION_REPORT.md).

## Main results

| Paper result | Module(s) |
| --- | --- |
| T01 `thm:cvlocale` | [`MainLocalLimit`](../Freezing1/MainLocalLimit.lean); unrestricted ambient version in [`MainLocalAmbient`](../Freezing1/MainLocalAmbient.lean) |
| T02 `thm:BGW` | [`MainGeometricLimit`](../Freezing1/MainGeometricLimit.lean) |
| T03 `thm:height` | [`MainHeight`](../Freezing1/MainHeight.lean), [`MainMaximum`](../Freezing1/MainMaximum.lean) |
| T04 `thm:lineaire` | [`MainLinearHeightScale`](../Freezing1/MainLinearHeightScale.lean), [`MainLinearUniformHeight`](../Freezing1/MainLinearUniformHeight.lean), [`MainLinearDistance`](../Freezing1/MainLinearDistance.lean), [`MainLinearMaximumLower`](../Freezing1/MainLinearMaximumLower.lean) |
| T05 `thm:samelaw` | [`ConstructionEquivalence`](../Freezing1/ConstructionEquivalence.lean) |
| T06, T07 `thm:SIRlocallimit`, `thm:SIR` | [`SIRPhysicalLimits`](../Freezing1/SIRPhysicalLimits.lean), [`SIRPhysicalFiniteLimits`](../Freezing1/SIRPhysicalFiniteLimits.lean); non-vacuity of the SIR data in [`SIRPoissonExistence`](../Freezing1/SIRPoissonExistence.lean) |

## Selected supporting modules

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

