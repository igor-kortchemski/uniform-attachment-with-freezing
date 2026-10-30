# Complete forest laws and source matching

This authored record concerns A47–A49 and A51–A53, especially manuscript
lines 1509–1512, 1648–1678 and 1693–1788. Independent source review and root-controlled build
evidence are separate. The fixed schedule and the actual forward transition
law are retained throughout; no forest-independence or matching premise is
inserted into the advertised process theorems.

## Exact objects and corrected conventions

`forestCut s a` retains all later vertices and edges and the old roots active
at the lower cut. It erases earlier parent edges and replaces their heights
by the verified cut heights. It retains each root's later freezing time and
genuine activity. Its unused parent values are self-pointers, which makes
root relabeling well defined without extra data.

This is an **augmented** forest. The manuscript relabels all old roots by stars
and declares them active even after a later freeze. `starForest` and
`slotStarForest` implement that convention by adding every marked root to
the active set and clearing its freezing clock. The root permutation quotient
then erases the old names. `slotStarForest_actual` identifies this coarsening
with the source construction, including all descendant data.

S08 remains necessary: roots must be matched to active vertices of the
**lower-cut** tree. S17 also has a full-state consequence: the bare star forest
does not retain root freezing times and cannot by itself reconstruct the full
active/frozen terminal state by an activity-preserving matching. The formal
`star_activity_counterexample` gives a strictly surviving legal schedule
$[+,-]$: the marked forest has two displayed active roots whereas the actual
terminal tree has one active vertex. Geometry, height observables and the
conditional moment arguments must be distinguished from full-state recovery.

No claim is made that the trees in a forest are independent. The fixed
schedule couples their populations. The source's rigorous independence
assertion concerns the past tree and the anonymously represented future
forest.

## Proved bridges

`ForwardForestCutState` proves that every legal original transition commutes
with the complete forest cut and that the initial cut state is exactly the
isolated set of currently active roots. `ForwardForestCutLaw` identifies the
entire original continuation's forest pushforward, then proves the joint law
of the whole earlier tree and the complete later cut forest.

`ForwardForestRelabel` proves equivariance for every field of the complete
forest. `FiniteRootSlots` supplies a bijection of bounded old root sets fixing
every future birth ID. `ForwardForestSlots` proves that the full slot forest
and the whole earlier tree have a product law under the actual tree measure.
`ForwardForestStarOrbit` proves the corresponding independence for the complete
bare source forest after erasing the extra root clocks and old names.

`ForwardForestRootOrbit` defines exactly the finite root-name quotient and
proves invariant resampling by a genuinely independent uniform permutation.
`ForwardForestRootMatchingEquiv` parametrizes all bijections of old roots by
these permutations, with neither omissions nor repeated matchings.

`ForwardForestReconstruction` proves that an actual prefix and the augmented
root-labelled forest determine every field of the actual terminal state:
vertices, parents, freezing clocks, heights, graph and active set. Its total
classical reconstruction operator is characterized on every compatible pair.
Existence is supplied by the actual forest law. Off-support defaults are not
used to assert process behavior.

`ForwardForestUniformMatching` gives the exact actual joint law of past,
root-erased augmented forest and full terminal state through an independent
fresh forest and uniform permutation. `ForwardForestBareMatching` retains
the bare source forest jointly in that identity while keeping hidden root
clocks in the independent driving forest. This full-state identity is not a
claim of deterministic recovery from bare data alone.

`ForwardForestBareGeometry` separately proves that the prefix and matched
bare forest uniquely determine the terminal vertices, parent map, heights
and graph. Its total classical reconstruction is characterized on every
actual compatible pair. Thus S17's lost-clock issue is confined to labelled
freezing/activity data; it does not invalidate geometric reconstruction.

`ForwardForestRematchingAction` proves that each fixed root bijection preserves
the actual terminal law and almost surely preserves the complete observed
past and bare forest. These are the actual hypotheses used by conditional
averaging; they are not source assumptions.
`ForwardForestConditionalExchangeability` exports the actual conditional
exchangeability explicitly for every integrable observation and every event,
given the whole earlier tree, and also given that tree together with the
complete bare forest.

`ForwardBlockHeightAncestor` proves the source's height-increment
interpretation exactly: the increment between two cuts is the earlier-cut
height of the later-cut component root.

## Actual statistics

`ForwardForestTaggedProjection` identifies the full active root/height
population of the complete forest with the actual tree's population, and
proves exact transport under root relabeling.
`ForwardForestPopulationLaw` identifies its whole tagged continuation law,
including root support and population bounds.

`ForwardForestTallStatistics` proves that the genuine tall-descendant count
is a quotient-measurable function of the complete bare source forest. Added
marked roots have height zero and contribute nothing for a nonnegative
threshold. `ForwardForestMaximumStatistics` proves the same for the marked
component maximum, counting each distinguished root exactly once even after
it freezes. These facts discharge the source's full-forest measurability
claims for $N$ and $M$.

`TaggedPopulationSlotMoments` supplies the exact mean and variance for the
same finite slot permutations used in the proved actual forest law. These
finite formulas alone do not certify the source's conditional expectation or
variance under the actual tree measure.

The actual consumers now supply those missing bridges.
`ForwardForestConditionalMean` applies the proved rematching actions to the
actual tree measure, using conditional finite averaging given the complete
past and bare forest. The literal source good-chain formula is
`condExp_goodSet_succ_given_forest` in `ForwardForestConditionalChainMean`.
Its denominator is the exact real population $S_{C^k}$, including the initial
root; its numerator is $\overline N_kN_k$.

`ForwardForestConditionalVariance` proves the actual conditional centered
second-moment bound, supplying all population caps and integrability.
`ForwardForestConditionalChainVariance.condVar_goodSet_succ_given_forest`
then states the literal conditional variance bound through Mathlib's
`condVar`. No invariant-law, forest-law, matching, mean or variance estimate
is added to the source hypotheses. The finite matching correspondence thus
now certifies the source mean and variance arguments themselves, in addition
to the earlier joint-event alternative used for the main theorem.

`ForwardForestConditionalVertexCovariance` now also proves the actual
conditional pair inequality through full rematching and conditional finite
averaging. `ForwardForestConditionalChainCovariance` transfers it to the
source good-chain event for every pair of vertices in different source
forest components. Old marked roots are included explicitly: their new
block height is zero, so their next-good indicator vanishes for a nonnegative
threshold. `ForwardForestChainVertexEvents` proves both the actual event
identity and the same-component/tall-pair identity.
`ForwardForestChainComponentMarks` also proves the literal inherited
height-test event is constant on every source-star-active component,
including distinguished roots that freeze after the lower cut. No independence or
pairwise-correlation premise is added.

`ForwardForestUpperPrefix` proves the full two-cut forest independence when
both cuts are observed inside any later terminal tree. The conditional
formulas above are stated on the actual upper-cut law; they are not silently
identified with conditional expectations on a different carrier.

`ForwardHeightChainTelescoping` checks the height telescope along every
finite chain under the full original history law. `ForwardTerminalGoodPredicate`
exports the exact terminal-source predicate and historical active set, including
the root and all printed cutoff indices. `ForwardCutAncestorPath` supplies
actual parent iterates, graph distances and historical activity.
`ForwardGoodGraphAncestorChain` explicitly quantifies the whole chain of
historically active ancestors and proves the distance of each successive
pair exceeds its block threshold. These supply the previously retained
A48 predicate and A49 graph-chain interfaces. The finite source cutoff is
exactly $\max(1,\lceil\log(A_n)/\log C\rceil)$:
`GeometricChainPositiveCutoff` retains the positive-index condition also
for $A_n\le1$, proves the exact terminal source filter for every $A_n>0$,
and instantiates the graph chain with that cutoff. It proves eventual
reduction to the original ceiling cutoff under $A_n\to\infty$.
Rounded logarithmic span asymptotics remain in `GeometricChainCutoffs`.

`ConditionalRelativeChebyshev` proves conditional Chebyshev with a random
observation-measurable center, including the full pull-out and integrability
requirements. `ForwardForestConditionalChebyshev` applies it to the actual
source count and actual conditional mean. The literal false population bound
$S_a\leq a$ is retained as S08; the corrected bound is $S_a\leq a+1$.
For $a\ge3$, the favorable event gives a mean of at least three times the
old target, hence a conditional doubling-failure bound $3M/b$. At the
printed thresholds the exported bound is $3k^3/2^k$, preserving the already
checked uniform $O(k^{-2})$ order. The relative theorem also includes the
printed half-mean Chebyshev bound as $\theta=1/2$. The printed repeated
$N_k$ denominator is still corrected to $\overline N_kN_k$ (S08).
No moment bound, conditional law or forest independence assumption is
added to these actual-process conclusions.

The finite-sum/integral bridge is explicitly independent of the chosen
enumeration of the permutation carrier (`UniformPermutationFiniteAverage`).
This prevents expensive definitional comparison between the computable
enumeration of permutations of `Fin m` and the classical generic enumeration.
The correction changes no mathematical statement and raises no heartbeat
budget.

## Evidence scope

The authored `verification/ForestSourceConditionalStatements.lean` expanded
probe passes eight source-interface examples and twenty-nine axiom queries.
Every queried closure uses only `propext`, `Classical.choice` and `Quot.sound`.
Its conditional-exchangeability, finite cutoff, graph ancestry and covariance
checks are distinct from the independent review maintained by the root.
The full A53 probability consumer has direct checked tower/favorable-event
integration and normalized conditional probability in
`ForwardForestConditionalGrowth`. `MainConditionalGoodChainForest` has a
clean direct Lean check for the final terminal and uniform inverse-square
source conclusions. Its root-controlled artifact build passes 3959 jobs. The final
three-example/seven-closure expanded probe also passes, using only the
three standard axioms. The proof route is reviewed in
`FOREST_CONDITIONAL_GROWTH_PROOF_NOTES.md`.

Each frozen source file has a focused direct Lean check and a root-controlled
dependency build. The full project's existing global axiom audit remains
separate from the scoped authored probes. This record does not certify
whole-paper coverage or Palomar deposit checks.
