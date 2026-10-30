# A28 probability assertions: author self-review

This document records the author's checks of newly authored modules. It is
not an independent statement audit; root-owned review and full-project trust
replay are separate evidence. Source scope is the proof paragraph at lines
973–979 of `attachement-uniforme-1-final.tex`. Consecutive-label relabelling
is a separate A28 obligation and is not covered by these probability proofs.

## Actual iid model and source conventions

`ForwardAnnealed.iidSignLaw` is the actual infinite product
`Measure.infinitePi (fun _ : ℕ => signLaw p)`. Coordinate laws, independence
and its exact positive-index finite-word pushforward are proved. Coordinate
zero is unused, matching the source walk. `activeCount` is the original
integer walk, which is not stopped after hitting zero. Its zero-crossing
event is distinguished from the absorbing natural-count walk throughout.

`IidScheduleDrift.lean` applies the installed Mathlib strong law to bounded
real observables of the independent sign coordinates. It derives, rather
than assumes,

$$
\frac{S_n}{n}\longrightarrow 2p-1
$$

almost surely, and the freezing-sign frequency tends to $1-p$. The strong
law is proved unconditionally and then restricted to nonextinction; no
conditional independence after conditioning is assumed.

## Critical and subcritical extinction

`SIRBiasedWalkMonotone.lean` constructs a genuine three-atom monotone coupling
for $p\leq q$. The two complete projected path laws are the existing actual
absorbed biased-walk laws, and the order holds along their entire histories.
`SIRBiasedWalkCritical.lean` compares $p\leq 1/2$ with slightly supercritical
$q$ and the already proved extinction odds $(1-q)/q$. These odds approach
one, proving absorption with probability one, including the critical and
zero-attachment endpoints. The actual plane process and the whole geometric
Bienaymé tree inherit the corresponding almost-sure extinction/finiteness.
This is an expanded alternative proof of the paper's standard random-walk
recurrence assertion.

`IidScheduleExtinction.lean` identifies each finite zero-crossing event of the
raw infinite iid sign schedule with the original finite iid mixture of fixed
forward constructions and its genuine chronological count projection.
Continuity from below transfers the absorbing-walk probability to the raw
source schedule. Thus almost-sure extinction for $p\leq 1/2$ is about the
paper's actual iid signs, not a walk only declared to have a matching law.
The supercritical source extinction and nonextinction probabilities are also
identified explicitly.

## Source local-convergence argument on nonextinction

`FreezingDensityCriterion.lean` proves a finite Abel summation identity and
uses Cesaro convergence to show that summability forces a vanishing linearly
weighted average. Positive freezing density therefore makes the reciprocal
freezing-time series diverge. On a nonextinct nearest-neighbour schedule,
$S_{i+1}\leq i+1$ on freezing steps and $S_{i+1}>0$, so the exact printed
reciprocal series dominates this divergent series.

`IidScheduleLocalCriterion.lean` combines that deterministic argument with
the proved iid freezing density. For $1/2<p<1$, surviving schedules have the
positive source drift, divergent literal reciprocal partial sums, and the
actual fixed-schedule local convergence supplied by T01. Finite-extinction
schedules use the proved held trajectory after absorption. This checks the
source's two-case local-convergence argument for every $p<1$, rather than
only using the earlier annealed hazard proof of the same conclusion.

## Evidence and remaining scope

All six new probability modules pass actual-file direct Lean checks with
zero diagnostics: `SIRBiasedWalkMonotone`, `SIRBiasedWalkCritical`,
`IidScheduleDrift`, `FreezingDensityCriterion`, `IidScheduleLocalCriterion`
and `IidScheduleExtinction`. Root artifact integration also passed; root
build logs and the full-project trust replay are separate evidence.
`verification/A28ProbabilityStatements.lean` passes its actual-file direct
check with five expanded examples and thirteen transitive axiom probes
(`/tmp/a28-probability-statements.log`). Every probed closure is contained in
`propext`, `Classical.choice` and `Quot.sound`. The literal increasing consecutive-label
reindexing is handled separately in `A28_CONSECUTIVE_SELF_REVIEW.md` and the
new actual quotient-class relabelling modules. The root's A66 full
adaptive-word/forward-prefix adapter is separate and is not duplicated here.
