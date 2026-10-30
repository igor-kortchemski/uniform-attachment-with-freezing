# A64: independent audit of the source infinite-urn tail route

The integrating reviewer independently read source lines 2011–2019,
then `SourceUrnComponentTailScalar`, `SourceUrnComponentTail` and
`SourceUrnComponentMaximum`. The reviewer did not author these modules.
The separate independent A63 audit covers their constructed urn and
exact infinite budgets. The weaker arbitrary-process L13 premise remains
outside the certified scope under S11.

The actual infinite-urn estimate at deviation $t=k^2$ has exponent
bounded below by $k^2/(16K)$ when the common budgets are at most $K/a$.
The proof retains the true initial population bound $S_a\le a+1$ and
positive denominators. A common source-window constant controls the
population ratio. Consequently the marked-root threshold
$1+(1+k^2)S_b/S_a$ is eventually at most $k^3$. The extra one preserves
the paper's all-star convention, including roots frozen during a block.

The actual component endpoint is identified with the constructed urn's
endpoint, and this gives the conditional component tail for every
genuine lower-cut state and active root. The maximum event is included
in the union over exactly that state's active roots. Actual prefix
preservation proves that these are the terminal cut roots. Their number
is the actual $S_a$, so a finite union bound followed by the genuine
past-state mixture gives $S_a\,2e^{-k^2/(16K)}$. No independence between
components is asserted or needed.

The geometric population factor is absorbed by the quadratic
exponential uniformly for all sufficiently large indices. Growth of
$A_n$ supplies that same index threshold in every allowed row window.
The final theorem has the original near-origin limsup, bulk liminf,
strict survival and cutoff hypotheses; there is no additional component
tail, budget, ratio or threshold assumption. It uses the source infinite
extension/maximal-urn route, not the earlier finite-MGF concentration
theorem. Only generic cutoff bookkeeping is reused from that assembly.

The source endpoint bound and union argument are therefore checked
after the S17 root correction. This does not supply a separate joint
actual-component-path identification; that stronger source-process
correspondence is being completed separately from the endpoint transfer.

`A64SourceUrnIndependentStatements.lean` reconstructs three types and
queries eight closures, passing with exit zero in
`a64-source-urn-independent-statements.log`; all axioms are permitted.
The final source consumer builds in
`source-urn-component-maximum-build.log` (3,880 jobs). Authored expanded
checks have separate provenance. No publication or whole-paper
completion is claimed.
