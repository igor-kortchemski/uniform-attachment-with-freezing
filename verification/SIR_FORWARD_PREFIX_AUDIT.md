# A66 complete-prefix adapter: independent source and statement audit

Scope: `SIRForwardPrefixBridge.lean` and
`SIRPhysicalForwardPrefixBridge.lean`, authored by the root agent. This audit
and its probe were written by a different agent. The underlying physical
clock-history construction was authored by the auditing agent and was
independently reviewed by the root; its author self-review is labelled
separately in `SIR_CLOCK_HISTORY_PLAN.md`.

The checked source is lines 2039–2046 of
`attachement-uniforme-1-final.tex`: the adaptive sign sequence consists of
infectious-count increments up to absorption, and the whole stopped infection
tree history has the original forward-tree law with that random schedule.

## Exact observations and assumptions

The embedded adapters apply to every nonnegative finite rate, initial
susceptible population size $n$, and deterministic prefix horizon $k$. The
prefix starts at time zero and retains every time through $k$. In particular,
the result is stronger than equality of the last-tree marginal.

`originalForwardPrefix_map_tree` begins with the actual original
`ForwardInfiniteHistory.fullLaw (wordSchedule w)`. The coordinate map is the
proved chronological address projection. Its conclusion is derived from the
actual original forward transition kernels and their validity support,
including holding after extinction. The auxiliary `planePrefixWordLaw` is
not simply declared to be the source law.

`conditionalTreePrefixWordLaw_map_tree` requires word feasibility, precisely
to exclude an infection when no susceptibles remain. The actual adaptive
`signWordLaw` has that feasibility support. Its sign probabilities depend on
the susceptible-count history; the adapter does not assume iid signs or
independence of the entire sign word from the geometry.

`treeFullLaw_countsPrefix_original_treePrefix_word_mixture` keeps the entire
count prefix and entire original-forward tree prefix in one joint law. The
count prefix on the right is `countsPrefixWord n w` for the same random word
that drives the original tree. It is not an independently sampled count
path. Phase support in the conditional SIR law proves the deterministic
count prefix at every time before the joint map is applied.

The physical consumer uses only `PoissonSIRData` and positive intensity. The
source data comprise independent measurable whole-contact arrival paths and
recovery periods, recovery marginal $\mathrm{Exp}(1)$, and exact Poisson count
marginals. The physical-to-embedded identity is supplied by its proved
`treePathLaw_eq` method. No process-law identity, conditional independence,
survival or asymptotic premise is added to A66.

## Random stopping and labels

The count/tree joint law determines the first index where the infectious
count is zero and the tree observed at that same index. The independent probe
checks both that the mixed count coordinate's infectious population equals
the mixed tree's active cardinality at every prefix time, and that every
index read from the count prefix observes its tree at that same index.
Consequently the random absorption index does not require an extra
independence argument.

Use the already proved terminal horizon $2n+1$ when reading the full stopped
infection tree. Both the embedded and physical clock frames are absorbed by
that horizon and held afterwards. No observation at time $n$ is substituted
for the terminal tree. Padding a sign word beyond absorption is harmless:
both original and embedded kernels hold the complete state there.

The equality is stated in canonical chronological plane coordinates. Fixed
individual labels in the physical population and step labels in the original
forward algorithm are transported through their proved injective genealogy
addresses. This retains roots, edges, active vertices and child order. The
source shape equality follows from this stronger canonical observation;
literal equality of the two unrelated ambient label sets is not asserted.

## Verification and scope

`verification/SIRForwardPrefixStatements.lean` expands the original fixed-word
prefix law, the full joint count/tree law and the physical source-data input.
It also reconstructs same-population support and arbitrary bounded
count-index observations. The actual-file direct check passes without
diagnostics: three expanded adapter examples, two reconstructed joint/stopping
observations, and seven transitive axiom probes. Every probed closure is
contained in `propext`, `Classical.choice` and `Quot.sound`
(`/tmp/sir-forward-prefix-audit-probe.log`). Root artifact integration passed
separately in `verification/mean-limit-physical-forward-prefix-build.log`.
No implementation files or root coverage report were edited by this audit.

No source mismatch was found in the reviewed adapter statements or proof
structure. The physical wrapper's positive-rate scope is explicit; the
separate no-arrival/zero-rate carrier remains outside this audit. This audit
does not assert a new global-calendar-time Poisson construction or a
full-infinite random-word object beyond what the finite stopped source
identity requires.
