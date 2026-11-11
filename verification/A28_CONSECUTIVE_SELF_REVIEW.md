# A28 consecutive relabelling: author self-review

This is the author's development and statement-check record for source lines
973–975. Independent root review and trust replay are separate evidence.
The probability assertions in A28 are recorded separately in
`A28_PROBABILITY_SELF_REVIEW.md`.

## Actual source class and unique label map

The input is the actual `UnorderedIncreasingClass k n A`, the proved
sibling-permutation quotient from P01. No abstract equivalence with ordered
codes is assumed: the existing P01 canonical-representative and rooted/binary
bijections are used, with their proved inverses.

For finite label sets $A$ and $B$, the map is their actual order isomorphism.
Uniqueness is proved by conjugating with the installed finite-order
isomorphisms to initial finite orders. Its total numeric extension outside
$A$ is arbitrary and never used on the source tree. Strict increase is
required only on $A$, which is necessary when gaps in numeric labels are
compressed.

The class's proved cardinal relation gives

$$
|A|=2n-k-1.
$$

Thus the source's map $f:\{1,\ldots,2n-k-1\}\to A$ is the inverse order
isomorphism to the consecutive interval. Both existence and uniqueness are
proved, including the empty-label case. The input tree supplies only the
cardinality proof; uniqueness shows that the order isomorphism depends on
the label set rather than the choice of tree.

## Literal tree relabelling and preservation

`RootedLabelMap.lean` defines a literal numeric label map and proves its exact
rooted-node equation: the same child stays attached to the same parent, each
edge receives the mapped label, and a frozen vertex's label is mapped while
an active vertex remains unlabelled. Vertex and active counts are preserved.
Edge-label and frozen-vertex-label multisets are mapped separately.
`numericSkeleton` erases numeric values while retaining every rooted
incidence and active/frozen mark; its invariance is proved.

`IncreasingRelabelling.lean` transports the actual binary, canonical rooted
and unordered source classes along the finite label order isomorphism.
Increase is proved on every present label, and inverse relabellings cancel
on those labels. The unordered quotient's canonical representative is
proved to be exactly the literal relabelled original representative.
Consequently the operation preserves the actual tree and active marks,
not only class cardinalities or label multisets.

`existsUnique_paper_consecutive_relabelling` proves a unique actual unordered
increasing target tree on $\{1,\ldots,2n-k-1\}$. Its defining predicate is
literal per-incidence relabelling of canonical representatives.
`verification/A28ConsecutiveStatements.lean` also checks the source's two-way
label condition $f(i)\leftrightarrow i$, the unique increasing bijection,
the unique tree and the separate edge/frozen-label and skeleton identities.

## Evidence

Both `RootedLabelMap.lean` and `IncreasingRelabelling.lean` pass their
actual-file direct Lean checks with zero diagnostics
(local logs, not retained). Root
artifact integration passed in
`verification/consecutive-labels-birth-moment-conclusions-build.log`.
`verification/A28ConsecutiveStatements.lean` passes four expanded examples,
a two-way source label-condition proof and eight transitive axiom probes.
Every probed closure is contained in `propext`, `Classical.choice` and
`Quot.sound` (a local log, not retained). Root independent
statement review and the project's full trust replay remain separate from
this author self-review.
