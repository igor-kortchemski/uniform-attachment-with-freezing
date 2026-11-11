# A24: independent audit of the all-vertex degree obstruction

This review independently reads source lines 912–921 and the root-authored
`LocalBallTightness`, `ForwardDegreeDivergence`, `ForwardDegreeCoupling`,
and `MainLocalDegreeNecessity`. The reviewer did not write those four
modules. The earlier deterministic degree/local-convergence criterion and
vertex-degree monotonicity were authored by this reviewer; their reuse
here does not turn that earlier self-review into an independent review.
Their relevant interfaces and the actual height-versus-birth-ID bound
were inspected again for this consumer.

## Source content and exact new scope

The source argues that failure of almost-sure local convergence leaves
one named vertex with positive probability of degree tending to infinity.
It extracts increasing row indices whose schedules agree with the fixed
schedule on longer prefixes, couples the matching prefixes, and uses
degree growth to contradict diagonal local convergence in distribution.

The new result
`ForwardInfiniteHistory.ae_local_limit_of_diagonal_tendsto_via_degrees`
assumes coordinatewise eventual agreement of the schedules and weak
convergence of the actual diagonal chronological local-tree laws. It
concludes almost-sure existence of a local limit for the genuine fixed
full-history law. It adds no freezing-series criterion, nonextinction
condition, limiting-degree estimate, or root-only witness premise.

The carrier is the established `LocalTree.Tree`, with actual chronological
vertex records in its finite balls. This audit certifies the all-vertex
necessity argument on that carrier. Transfer from the source's ambient
unordered labelled quotient, and identification of a common measurable
limit law, remain separately proved bridges; they are not new conclusions
of these four files. This is the same scope retained in the implementing
self-review.

## All actual vertices, the root, and absorption

`vertexDegree s r` is the cardinality of the actual vertex filter
`{v ∈ s.vertices | s.graph.Adj r v}`. It is not a count of active vertices
or only of children. Both the parent edge and child edges are counted.
The parameter $r$ ranges over every natural-number birth identifier,
including the initial root $r=0$. Invalid or absent names cannot create
spurious neighbours in a valid state. The proof does not rely on finding
a nonroot witness even though the source prose names an added vertex.

`ForwardDegreeDivergence.degreeUnbounded` is the event
$\forall d\,\exists n:\deg(r,H_n)>d$. On the actual full-history law,
each degree is monotone, including the held trajectory after absorption.
Consequently this event agrees almost surely with degree divergence to
infinity. Positive mass of this event yields one positive real constant
$\delta$, independent of the threshold $d$, such that every sufficiently
late marginal has degree tail at least $\delta$. The eventual time may
depend on $d$, which is exactly what the later tightness contradiction
needs.

This tail argument uses continuity from below for finite time-prefix
unions and actual degree monotonicity. It does not infer a positive
event from a formal supremum of unrelated random variables. The
independent expanded probe additionally reconstructs the first source
display: the decreasing degree-threshold union probabilities converge
to the probability of the unbounded-degree event. Together with the
proved monotonicity equivalence, this checks that displayed limiting
event interpretation. This auxiliary reconstruction is reviewer-authored
probe work, separate from the independent audit of the four root modules.

## Prefix extraction and coupling distinction

`exists_strictMono_matching_prefixes` constructs a strictly increasing
$\varphi$ with $n\leq\varphi(n)$ and exact schedule agreement through
time $n$. The bound on the terminal horizon is proved, not presumed from
the word “increasing”. `exists_matching_degree_couplings` supplies, for
each extracted row, a genuine pair of full-history laws with both correct
marginals and simultaneous degree domination for every named vertex.

The quantifier order is a family of pair couplings. It does not supply
one common probability space carrying the same fixed trajectory and all
row trajectories at once. Neither the Lean theorem nor its self-review
claims that stronger assertion. In particular, no equality of unions
across different pair-coupling spaces is used.

The final proof transfers marginal tail probabilities directly. For any
fixed threshold it first chooses a sufficiently long fixed prefix of the
limiting schedule, then uses exact equality of the row's law at that
prefix and monotonicity from the prefix to the row's terminal horizon.
One tail mass is thereby retained in every sufficiently late diagonal
row. This also avoids requiring an explicit extracted subsequence in the
final contradiction; the matching-prefix extraction and genuine pair
couplings are nevertheless separately verified source ingredients.

## Finite-ball tightness and conclusion

For every actual valid state and named vertex $r$, the proof establishes

$$
\deg(r,s)\leq\left|B_{r+1}(s)\right|.
$$

The radius is deterministic: the actual parent ordering proves that the
height of vertex $r$ is at most $r$, and each neighbour lies within one
additional edge. No random radius or uniform bound in $r$ is assumed.
`ballCard (r+1)` is a continuous natural-valued observable in the actual
local topology. Its tail events are clopen; every probability law has
tails tending to zero because every finite ball has finite cardinality.
Weak convergence transfers the probability of each fixed clopen tail.
Thus a single sufficiently high threshold has an eventually arbitrarily
small diagonal tail, contradicting the uniform positive tail mass.

All named unbounded-degree events are therefore null. A countable
intersection supplies simultaneous boundedness of every actual vertex
degree almost surely. The genuine deterministic legal-or-held history
criterion then constructs a local limit. Finite extinction is included
by its held paths and requires no separate survival premise. No
freezing-series implication is called to obtain this conclusion.

## Verdict and proof correspondence

No statement mismatch or hidden estimate was found in the reviewed new
all-vertex route. Its conclusion and prefix-coupling ingredients follow
the source's degree obstruction, and improve the earlier root-focused
route by retaining every actual vertex. The concluding contradiction is
a marginal finite-ball tightness argument. The manuscript's last
displayed union argument and its asserted pointwise divergence of a
possibly nonmonotone diagonal family under a single coupling are not
certified literally. A positive probability that a supremum is infinite
alone would not prove such pointwise diagonal divergence. This scoped
proof-route departure remains necessary in the report.

## Current evidence

The independent expanded probe is
`verification/A24AllVertexIndependentStatements.lean`. Its nine examples
cover the increasing extraction, actual pair-coupling marginals and
all-vertex domination, unboundedness versus divergence, the source's
first limiting union identity, the positive diagonal ball-tail mass,
nullity of every named obstruction, almost-sure local-limit existence,
the actual neighbour/ball inclusion, and clopen-tail tightness. Its
twelve root-declaration axiom closures use only `propext`,
`Classical.choice`, and `Quot.sound`. The fresh actual-file direct check
passed with exit code zero and no diagnostics in
a local log (not retained); the durable output is
`verification/a24-all-vertex-independent-statements.log`. Root artifact
evidence for the final new necessity module is retained in
`verification/unordered-topology-source-geometry-local-necessity-build.log`.
The probe does not manufacture a common joint coupling of all rows.
