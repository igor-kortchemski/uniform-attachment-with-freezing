# Static first-contact history bridge: verified interfaces and remaining work

This is the author's development and self-review record. Independent source
and statement audits are performed and recorded separately by the root agent.

This record concerns the physical-history portion of A65. The original
static array now has proved complete event-word and infection-tree laws.
The original whole-arrival-path protocol is tracked separately below.

## Actual preassigned model

Individuals have the fixed labels $V=\{0,\ldots,n\}$. A clock slot is a pair
$(v,q)$ with $v\in V$ and $q\in\{\mathrm{none}\}\cup V$: `none` records the
source's recovery delay and `some w` its first-contact delay to $w$.
`preassignedClockLaw r n` samples this entire finite array once, with
independent recovery delays of rate one and contact delays of rate $r>0$.

`preassignedRun` is a deterministic function of that one array. The frame
records the physical time, infection times, susceptible and active labels,
and their actual chronological infection-tree addresses. At each selected
event its time is exactly the source's infection time plus its preassigned
slot delay. No coordinate is resampled. A non-strict minimum is totalized by
holding. The proved product law of the relevant residual clocks gives zero
probability to such false holding before absorption, and this is included in
the history induction.

The static exponential-array process assumes positive contact rate.
Zero-rate recovery races were first proved separately in
`SIRExponentialWinner.disabledContactClockLaw`. The complete zero-contact
source protocol is now proved separately by root-authored optional/no-arrival
carrier modules, independently reviewed in `SIR_ZERO_RATE_AUDIT.md`. A missing
contact is an absent event, not a rate-zero exponential random variable.

## Verified building blocks

- `SIRExponentialWinner.lean`: designated finite-clock winner law, null ties,
  responsible-individual uniformity, independence of individual and event
  kind, uniform susceptible recipient, and aggregate-minimum event matching.
- `SIRExponentialMemoryless.lean`: actual joint winner, global minimum and
  nonwinning residual law. No memorylessness or factorization is assumed as
  a theorem premise.
- `SIRClockPopulation.lean`: fixed labels, valid chronological genealogy,
  exact projection to the existing `TreeState`, live/unused/relevant slots,
  and total live rate $I(1+rU)$.
- `SIRClockPopulationUpdates.lean`: legal labelled infection and recovery
  preserve validity and project to the actual `treeStep`. Every next relevant
  slot belongs to the old relevant slots with the winner removed.
- `SIRPreassignedClocks.lean`: the actual static-array recursion and its
  measurability, initial probability law, positive delays and absolute-time
  identity. No full path-law identity is claimed here.
- `SIRPreassignedResiduals.lean`: exact deterministic aging, deletion and
  activation semantics. Old surviving live delays lose elapsed time; unused
  coordinates retain their original delays. The initial relevant view has
  its actual independent product law, proved by injective coordinate
  projection.
- `SIRPreassignedChronology.lean`: all live clocks stay in the future on
  positive arrays; physical time is nondecreasing and strictly increases at
  selected events.
- `SIRClockNextCoordinates.lean`: the next relevant coordinates inject into
  old nonwinning live coordinates plus unused coordinates, preserving every
  physical coordinate and rate.
- `SIRRaceWithUnused.lean`: exact winner/time/next-coordinate law for the
  actual product of live and untouched unused clocks, under any injective
  coordinate selection.
- `SIRClockRaceStep.lean`: the exact specialization to the concrete valid
  population, with coefficient $\mathrm{rate}(c)/[I(1+rU)]$ and the original
  exponential rates on every next relevant slot.
- `SIRClockRaceSemantics.lean`: that probabilistic next-coordinate map equals
  the actual static-array next residual view pointwise.
- `SIRClockRelevantProduct.lean`: the current relevant product itself yields
  the live/unused split and the exact next-clock law; independence is proved
  by coordinate projection.
- `SIRRelevantClockChoice.lean`: the relevant-view selector equals the actual
  static selector; false holding has zero measure before absorption.
- `SIRClockEventWords.lean`: reversed finite event words, deterministic replay
  of the actual population, measurable prefix events and residual maps, and
  recursively specified event/word weights.
- `SIRClockChoiceTransition.lean`: one unified next-product measure identity
  for every possible choice, including absorption and impossible events.

The listed modules pass their actual-file direct Lean checks. Root-owned
project integration and global axiom checks are separate evidence.

## Proved finite-word residual invariant

`SIRClockPrefixLaw.lean` is source-frozen and passes the actual-file direct
Lean check without diagnostics. Root also built it successfully in
`verification/sir-clock-prefix-finite-capture-build.log`. Its five probed
transitive axiom closures contain only `propext`, `Classical.choice` and
`Quot.sound`; the check is recorded in
a local log (not retained).

For a finite event word $w$ (stored newest first), let $E_w$ be the event that
the deterministic static run has that word, let $z_w$ be its proved population
replay, and let $\rho_w$ be its residual view. The implemented theorem
`preassigned_clock_prefix_residual_law` proves

$$
(\rho_w)_*(\mu|_{E_w})
=a(w)\bigotimes_{c\in\mathrm{Relevant}(z_w)}
                 \mathrm{Exp}(\mathrm{rate}(c)).
$$

Here $a(w)$ is the recursively computed event-word weight, and
`preassigned_clock_word_probability` proves $\mu(E_w)=a(w)$ as a conclusion.
No conditional-independence premise is introduced. The
initial case is the proved initial relevant-view law. In the inductive step,
split the relevant product into live and unused coordinates, restrict to a
particular live winner, apply the genuine race-with-unused factorization,
and use the proved coordinate injection and deterministic aging identity.
The unified choice law handles impossible events with zero measure and
absorbed holding with the same residual product. The proved strict-winner
existence for the live product excludes false holding before absorption.

## Proved complete event-word law

`SIRClockWordKernel.lean` passes the actual-file direct Lean check with zero
diagnostics (a local log, not retained). Root integration passed in
`verification/sir-clock-word-finite-profiles-build.log`. Expanded examples and
five transitive axiom probes in `verification/SIRClockWordLawStatements.lean`
passed; their closures are contained in `propext`, `Classical.choice`, and
`Quot.sound` (a local log, not retained). Its reference transition draws
the current relevant-clock selector and prepends that choice to the reversed
word. This construction alone is not used as evidence for the original
array. Instead, `preassigned_word_marginal_eq` derives equality of every
single-time word distribution from the preceding original-array prefix
invariant. Both word histories are coherent: each new word prepends one
choice. The deterministic lemma `coherent_word_drop` therefore recovers every
earlier word by dropping entries of the last word. Consequently every finite
history prefix has the same law, and countable path-space uniqueness proves
`preassigned_clock_word_fullLaw`, an equality of measures on complete
infinite event-word histories. No resampling or conditional independence is
assumed in this argument.

## Proved original-array tree-law transport

The resulting finite-history transition weights are

$$
\frac{\mathrm{rate}(c)}{I(1+rU)}.
$$

Summing the contact recipients yields the infection weight $rU/(1+rU)$;
recoveries have weight $1/(1+rU)$, and each active source contributes the
uniform factor $1/I$. The legal population projection is already the exact
tree transition. The finite-word induction and countable path-space uniqueness are now
proved. `SIRPopulationUniformActor.lean` also passes its actual-file direct
check: injectivity of the stored chronological addresses transports uniform
labelled active-source choice to exactly uniform tree-active actor choice.
`SIRClockTreeProjection.lean` now proves that finite weighted source/recipient
calculation, including zero susceptibles and absorption. Its root artifact
build passed in `verification/sir-clock-projection-scalar-build.log`.
`SIRClockTreeFullLaw.lean` passes its actual-file direct check with zero
diagnostics (a local log, not retained) and proves the complete
required tree identity

$$
\mu\circ\left(\omega\mapsto
    (\mathrm{project}(\mathrm{population}(\mathrm{preassignedRun}(\omega,k))))_{k\geq0}
       \right)^{-1}
=\mathrm{treeFullLaw}(r,n).
$$

`preassigned_clock_tree_fullLaw` proves this equality from the independently
proved original-array word law and the exact labelled-source tree projection.
`preassigned_clock_absorbed_by` also proves the entire actual clock frame,
including physical time and infection-time records, holds after event
$2n+1$. The source-data exports `independent_poisson_tree_fullLaw`,
`independent_poisson_absorbed_by` and `independent_poisson_terminal_tree_law`
compose the independently proved first-arrival-array law with these results.
The terminal target is exactly `embeddedTerminalTreeLaw`, not a newly defined
law postulated to equal the source process.

## Separate Poisson identification

The source uses independent Poisson contact processes and independent
infectious periods. Only the first contact to a still-susceptible target can
matter: that contact infects the target and removes its incoming susceptible
slots. A new infective activates its previously unused independent outgoing
array and recovery clock. Thus a finite first-arrival reduction appears
possible without constructing all later Poisson points.

The independent worker has now proved `PoissonContact.first_law` from an
actual canonical arrival-path law with Poisson one-time count marginals, and
`independent_firstArrivalArray_law` from independent measurable whole-contact
path coordinates and exponential recovery coordinates. The latter proves the
joint array pushforward is exactly `preassignedClockLaw`. Source modules
`SIRPoissonFirstArrival.lean` and `SIRPoissonClockArray.lean` passed their
actual-file direct Lean checks; root-owned integration is separate evidence.
These results do not assume exponential contact delays or the embedded
history law. The complete first-contact tree-history composition is now proved as
above. The next-point protocol of the entire actual contact paths is also
implemented and verified independently in `SIRPoissonFullContacts.lean`:
each event recomputes the next contact after the source's current infection
age. Its entire deterministic clock-frame path equals the static-array run
on positive arrays. `SIRFirstContactIrrelevance.lean` additionally checks that
susceptibility decreases, removed individuals stay removed, and later
contacts cannot be effective when the first contact was ineffective.

The new consumer `SIRPoissonFullContactLaw.lean` passes its actual-file direct
Lean check with zero diagnostics (a local log, not retained). It transports
that genuine next-point protocol to the already proved complete tree and
literal susceptible/infectious count laws, complete clock-frame absorption,
and the terminal tree law. The zero-contact source case is now also proved separately by
`SIRPhysicalZeroRate.lean`, including complete tree/count paths and actual
positive exponential recovery timing. Its independent audit is
`SIR_ZERO_RATE_AUDIT.md`. Transport for positive-intensity arbitrary optional
path data is outside that zero-branch audit; the original positive source
carrier and its proved history law remain available. No global-calendar-time Poisson construction or
strong-Markov-at-a-random-infection-time theorem is being silently asserted:
the source coordinates are independent contact paths indexed by infection
age and activated when their source becomes infected.

## Source-facing asymptotic transfers

`SIRPhysicalLaws.lean` and `SIRPhysicalLimits.lean` pass their actual-file
direct Lean checks without diagnostics. The former bundles exactly the
source recovery/contact process assumptions and defines observable laws from
the genuine whole-contact next-point protocol. Its law-identification
methods invoke the proved physical history theorem. It also verifies that the
finite-word scaled path equals the uncapped stopped count path simultaneously
at all nonnegative observation times.

The latter transports T06.I, T06.II, the finite-rate whole-path fluid limit,
the strong uniform fluid limit, and terminal strong uniform height, pair
distance and maximum-height limits. Each theorem assumes source process data
only eventually in the population size. The exact source rate ratio itself
implies eventual positive intensity; no assertion that every rate is positive
has been added. The non-tightness transfer uses proved bounded-root-degree
escape, so it does not need a separate assumption on the finitely many early
models. The finite-rate fluid target is the law indexed by the actual
geometric Bienaymé tree's survival event, shared by the entire limiting path.

`SIRPhysicalFiniteLimits.lean` also passes its actual-file direct Lean check
without diagnostics (a local log, not retained). It defines the
scaled actual terminal conditional-sample laws and proves their finite-rate
weak limits from the independently proved embedded sampling laws. The sampling kernels include all vertices;
the pair kernel retains independent conditional draws and their diagonal.


## Current proof evidence

Root-owned artifact integration passed for the clock full-history and
whole-contact source modules in
`verification/sir-clock-full-finite-prefix-build.log`,
`verification/sir-poisson-full-contacts-build.log` and
`verification/sir-poisson-full-contact-law-build.log`. The physical law
foundation and eight physical asymptotic wrappers are integrated in
`verification/sir-physical-laws-build.log` and
`verification/binary-rotation-sir-physical-limits-build.log`.

Expanded statement checks passed in
`verification/SIRClockTreeFullLawStatements.lean` (seven axiom probes),
`verification/SIRPoissonFullContactStatements.lean` (six probes), and
`verification/SIRPhysicalLimitStatements.lean` (eleven probes). Every probed
transitive closure is contained in `propext`, `Classical.choice` and
`Quot.sound`. Their direct logs were local and are not retained. The finite sampling wrapper's four expanded examples and five axiom probes
also pass against the actual built module in
`verification/SIRPhysicalFiniteLimitStatements.lean`, with all five closures
contained in the same standard three axioms
(a local log, not retained). Root artifact integration
passed in `verification/binary-bijection-sir-physical-finite-build.log`.
The root agent independently reviews the full physical protocol and wrapper
statements; this document remains the author's self-review record.
