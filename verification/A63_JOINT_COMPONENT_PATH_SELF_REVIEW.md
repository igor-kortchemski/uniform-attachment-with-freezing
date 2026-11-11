# A63 actual joint component path: authored proof review

This document concerns the new `ForwardComponentUrnPath` modules. Their
author also independently reviewed the earlier positive-extension endpoint
route. That earlier independent review did not prove or certify a joint
component path identity. The present work is an authored extension and
requires its own independent review.

## Source obligation

At source lines 2011–2015, the urn occupancy $U_i$ is identified with the
number of active vertices in one actual component of the forest between
the lower cut $a=C^k$ and the later time $a+i$. This is a statement about
one process and its complete joint law. Equality of separate endpoint
marginals alone does not establish it.

The required observable is the true active population

$$
U_i(H)=\#\{v\in H_{a+i}.\mathrm{active}:
\mathrm{cutAncestor}(H_{a+i},a,v)=r\}.
$$

The root $r$ is active at the cut. It is counted subsequently only while
actually active. A permanently marked root remains a separate observable
with the previously recorded $+1$ correction S17.

## Finite joint records

`ForwardComponentUrnPath.continuationLaw_componentPrefixRecord` pushes
the genuine tree continuation law to the complete component record at
all times $a,\ldots,a+k$. Earlier states are recovered from the final
state by its actual canonical truncations, whose preservation under
the forward transitions is already proved. The result is exactly the
recursive `SignedUrn.pathLaw` for population `activeCount x`, starting
at the actual current component count.

The proof inducts through the original tree transition kernels, uses
their almost sure genuine-history support, and projects each actual
one-step component transition onto the urn transition. It neither
assumes a path law nor reconstructs one from endpoint marginals. The
horizon is allowed through extinction, with every step before the last
proved to have a nonempty active set. Thus no division by a vanished
population is used in the source application.

The finite positive-extension specialization retains the original
tree continuation through $b$, starts at occupancy one, and identifies
the full record with the shifted positive-extension population.

## Actual infinite tree history

`continuationHistoryLaw x a past` is the original forward
Ionescu–Tulcea trajectory kernel conditioned on the entire finite past.
It is not a new urn process. `fullLaw_bind_continuationHistoryLaw`
proves the exact disintegration of the original full tree law over its
whole finite prefix.

`continuationHistoryLaw_component_record` proves the joint record law
directly for these actual infinite trajectories. It splits the actual
trajectory after its first new step, preserves the entire old prefix,
uses genuine next-state support, and then applies the same actual
component transition projection. All finite horizons are proved at
once. The proof does not require consistency assumptions on the remote
past to generate a legal future: the current state has a genuine
history, and the final source consumer supplies actual pasts almost
surely.

## Positive extension and original pasts

`positiveExtension_bind_original_prefix` proves that the full extended
tree law is obtained by sampling the original complete past through
$a\leq b$ and then drawing the actual extended conditional future.
The equality of finite prefix laws follows from the literal equality
of every retained sign. This is an equality of genuine process laws,
not merely equality of the current state distributions.

`positiveExtension_actual_component_hasPathLaws` proves
`SignedUrn.HasPathLaws` for the actual component observable along this
tree future. Positivity through $b$ implies that the extended lifetime
is infinite, so every finite record theorem applies. The population is
exactly $Z_i=S^{\mathrm{ext}}_{a+i}$ and the starting occupancy is one.

`positiveExtension_original_component_pathLaws` removes the genuine
current-state hypothesis from the source formulation: it holds for
almost every complete past under the original full tree law, and for
every root active at the cut. The quantifier over roots is simultaneous
inside this almost sure statement.

The maximal consumer applies `infinite_maximal_summable` with this
proved actual-process `HasPathLaws`. It supplies positivity, signed
increments and summability from the actual positive extension and
rewrites the reciprocal maximum to the exact source finite epsilon.
Its deviation event therefore concerns the genuine tree component at
some $i\geq1$, over the entire infinite future. It is stronger than an
endpoint-only transfer and uses no assumed probability estimate.

## Scope retained

These declarations close the additional A63 joint-component-process
identification under the genuine original forward history kernels.
They do not repair S11 for an arbitrary process specified only by a
weaker current-occupancy conditional statement. They do not identify
the permanently marked-root count with the urn, so S17 remains.
The earlier A63 audit and A64 endpoint argument retain their original
provenance and proof routes.

## Proof evidence

The finite joint-record file passed its actual-file direct check with
exit code zero and no diagnostics in
a local log (not retained). Its parent artifact build is
PASS3931 in `verification/pair-thinning-separated-component-path-build.log`.

The infinite actual-history file passed its actual-file direct check
with exit code zero and no diagnostics in
a local log (not retained); its parent artifact
build is PASS3937 in
`verification/component-infinite-pair-source-tails-build.log`.
The positive-extension consumer passed with no diagnostics in
a local log (not retained), and its parent artifact
is PASS3932 in `verification/component-positive-pair-error-build.log`.
The actual infinite-maximal consumer passed with no diagnostics in
a local log (not retained); its parent artifact
is PASS3943 in
`verification/component-actual-maximal-pair-conclusions-build.log`.

The actual imported expanded probe
`verification/A63JointComponentPathStatements.lean` passed with exit
code zero, eight examples, thirteen axiom closures and no diagnostics
in a local log (not retained). Its durable output
is `verification/a63-joint-component-path-author-statements.log`.
Every closure uses only `propext`, `Classical.choice`, and `Quot.sound`.
These are authored checks; the independent review is coordinated by
the parent. No global coverage or publication verdict is implied.
