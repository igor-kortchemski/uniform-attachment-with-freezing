# Independent audit of the SIR certification interface

Reviewed base: `4b3e78c6b9cd9db80f1b63fd85046e2805589123`.
Scope: the nine T06/T07 conclusions in `comparator/sir.json`, their four
additional comparison targets, the model definitions in `Challenge/Sir.lean`,
and the new `SIRPoissonExistence*` construction. This reviewer did not author
these interfaces or implementations. No mathematical source, configuration
or workflow was changed by this review.

The original supplied manuscript was read at lines 2023–2107. Its SHA-256
is `88953dd87165a14b0e643c5b3d0075d8ce5ec39cdcfc0c25d313570fc3ab00df`.
The manuscript is retained in the development directory, not copied into
the candidate. The four target files and the three existence implementation
files have no changes between the rebuilt source commit `ab3d936` and this
reviewed base. The older SIR review's non-vacuity finding is now resolved;
its earlier line numbers and pending-existence statements are historical.

## Verdict

No blocking mathematical defect was found in the nine conclusions or the
positive-rate non-vacuity construction. The statements preserve the source
rate assumptions, terminal samples, scaling, constants and distributional
or probabilistic quantifiers within the explicitly disclosed chronological
plane/age-indexed representation.

This does not assert official Comparator, Linux sandbox or Palomar acceptance.
In particular the module-name devices still need the official pipeline test;
their presence alone is not a proved policy violation or a mathematical flaw.

## Source-to-interface reconstruction

| Source conclusion | Current Challenge lines | Checked content |
| --- | --- | --- |
| T06.I | 888–894 | Rate ratio tends to one with positive limiting intensity; genuine terminal full-contact tree law converges to the geometric Bienaymé law with attachment parameter $\lambda/(1+\lambda)$. |
| T06.II | 897–902 | Divergent $n\lambda_n$ gives genuine non-tightness of the whole family of actual terminal tree laws. |
| T07.I.a | 907–913 | Locally uniform weak path-law convergence to $\max(2-2g_\lambda(t)-t,0)$ on the canonical geometric survival event, and zero otherwise. |
| T07.I.b height/distance | 858–874 | Conditional-uniform terminal height and same-tree pair distance, divided by $\log n$, with limits $\lambda/(\lambda-1)$ and $2\lambda/(\lambda-1)$ on that same target survival event. |
| T07.II.a | 916–923 | Probability of the uniform-on-$[0,2]$ deviation exceeding every fixed positive tolerance tends to zero. |
| T07.II.b height/distance/maximum | 926–951 | Actual terminal observables, including frozen vertices and the pair diagonal, have constants $1$, $2$ and $e$. |

The first two ratio types are literally `rate n / (lam/n) → 1` and
`rate n / (1/n) → +∞`; the singular convention at $n=0$ is immaterial to
`atTop`. The implementation derives eventual rate positivity from these
assumptions (`SIRPhysicalLaws.lean:120–132`). It does not add positivity at
every size or condition on a major outbreak.

The canonical survival event is infinitude of the explicitly constructed
geometric Bienaymé tree (`Challenge/Sir.lean:179–180,527–548`), not an
uninterpreted Bernoulli parameter. The path and scalar target laws all use
the same event. The source asserts these marginal distributional limits;
the interface does not claim an additional joint convergence theorem.

## Model definitions and actual histories

`Challenge/Sir.lean:388–432` defines $n+1$ labelled individuals, one initial
infective, a susceptible set, an infectious set, their chronological tree
addresses and the actual infection tree. Infection removes the target from
susceptibility, adds it to the infectious set, and adds the next child of
the infector. Recovery removes the source from the infectious set and
freezes its retained tree vertex.

The contact protocol (`625–742`) uses entire increasing arrival paths;
at each event it reads the next live contact/recovery clock. Ties or an
empty live set hold the frame. Under the source-data law the tie default
is outside the used almost-sure support. The terminal observation index
$2n+1$ is justified by at most $n$ infections and $n+1$ recoveries.

The formal contact specification prescribes Poisson counting marginals,
not independent increments within an individual path. This is a broader
admissible class than an abstract Poisson-process axiom. It does not weaken
the resulting theorem for the source model: only each directed path's first
point is relevant while its target remains susceptible and its source
infectious. `first_law` identifies that point's exponential law, and slot
independence includes all recovery variables. The actual full-protocol to
preassigned-clock identity is proved in `SIRPoissonFullContactLaw.lean:28–43`;
the whole tree/count-history identities are at lines 66–98.

Crucially, `physicalCountsPathLaw` (`Challenge/Sir.lean:771–775`) reads the
susceptible and infectious **individual sets** directly. It is not defined
as an arbitrary proxy for the count process. The development also proves
`PoissonSIRData.countsPathLaw_eq` (`SIRPhysicalLaws.lean:80–83`). Adding it as
another comparison pin could improve presentation, but its omission is not
an identified error in the current compared definitions: the comparison
already traverses the body of `physicalCountsPathLaw`.

The uniform sampling definitions use every vertex, including old frozen
ones. The pair kernel samples independently conditional on one tree before
mixing over that tree (`Challenge/Sir.lean:274–290,795–798`). It retains the
diagonal and uses the actual parent graph's distance.

## Positive-rate existence and zero-rate boundary

The three existence implementation bodies were read. `waiting r` is an
actual countable product of exponential measures. Independence of the
partial sum and the next waiting time gives an explicit convolution formula
for the sum's CDF. The convolution integral is computed term by term as a
Poisson tail. Finite Poisson tail summability gives almost-sure unboundedness
of the partial sums; positive waits give strictly increasing arrivals.

`SIRPoissonExistenceProcess.lean:26–91` proves the good set measurable and
of probability one, then defines a measurable arrival-path map. The fixed
fallback path is used only on that null complement. The count law is derived
from $S_k\leq t<S_{k+1}$ and the difference of consecutive Poisson tails;
it is not assumed.

`SIRPoissonExistence.lean:58–82` assembles genuine independent data on the
finite product over all clock slots. `exists_family` at lines 97–116 provides
the exact sequence-level hypothesis needed by the physical theorems. Its
fallback at finitely many nonpositive-rate sizes remains outside the
eventual source-data assertion.

Rate zero is genuinely incompatible with an arrival path tending to infinity
and identically zero counting marginals. `not_hasPoissonCounts_zero` and
`exists_data_iff` prove the sharp domain. The main asymptotic assumptions
give eventual positivity, so this boundary does not make their hypotheses
vacuous or add a rate restriction absent from the source.

## Topology, measurability and representation caveats

The encoded tree is a chronological plane tree. A labelled/non-plane
interpretation of the source uses the disclosed forgetting/ordering
correspondence; this interface does not create a new unordered ambient
tree-space theorem. The age-indexed clock formulation is the natural
infectious-age realization of the source contact dynamics.

The population path space is all real functions on nonnegative time with
locally uniform topology and its Borel sigma-algebra
(`Challenge/Sir.lean:499–521`). The relevant prelimit step paths and the
two-valued limit have proved measurability; the proof does not rely on a
nonmeasurable `ProbabilityMeasure.map` fallback. The passage to the usual
càdlàg carrier with this topology remains a disclosed representation
correspondence, not an extra compared formal theorem.

## Metaprogramming devices

The `setMainModule` commands change Lean environment header metadata and
the realization context; they do not replace a theorem or definition.
Their purpose is reproducing the private auxiliary names of the original
multi-module development. The name is restored at line 992.

The explicitly written `advanceClockFrame.match_1` at lines 673–676 is
exactly dependent `Option.casesOn`. `geometricSurvivalScalarLaw._proof_1`
at lines 541–542 is a genuine probability-instance proof. The matcher-code
options avoid sharing generated matchers across formerly separate modules.
No invented mathematical stub was found in these devices.

The pinned `Lake.Check.compareAt` traverses the types of selected theorem
targets and compares all unselected reachable definitions and their used
constants structurally. The base local logs report this comparison passed,
and the source expressions of the devices were independently inspected.
This is meaningful local evidence, not a guarantee of official sandbox or
editorial acceptance. Do not report the devices as already rejected by policy
without such an actual result.

## Corrections worth making

The header of `Challenge/Sir.lean:57–61` still says existence is not a target
unless stated elsewhere. It is now explicitly selected at lines 978 and 984.
This stale wording should be updated; no mathematical refactor is needed.
The older `EXISTENCE_NOTES.md` phrase that `Freezing1.lean` does not import the
new modules is also historical. The main theorems remain conditional on the
given physical model data, as a model theorem should; existence discharges
the non-vacuity concern rather than deleting the model assumptions.

## Independent current probe

`CODEX_SIRProbe.lean` constructs a family at constant positive contact rate
one using `exists_family`, then derives the actual terminal-tree
non-tightness and the genuine physical uniform fluid conclusion. Its theorem
has no `PoissonSIRData`, coupling or probability-bound premise. This checks
that the new existence result and the existing source-facing limits really
compose on one family of actual model data.

Its direct imported check passed with exit zero in `codex-sir-probe.log`.
Six transitive closure queries use only `propext`, `Classical.choice`,
`Quot.sound`. There are two proof-style linter suggestions about `letI`,
not errors. This is one independently constructed end-to-end example, not
a rerun of the author's mirrored target probe. No artifact-writing build
or external action was performed by this reviewer.

Integration note: the integrating reviewer replaced two `letI` binders by
`let` in the new verification probe to remove style warnings, then reran
the actual imported check successfully. The current probe log contains only
the six permitted-axiom reports. No model, theorem or interface changed.
