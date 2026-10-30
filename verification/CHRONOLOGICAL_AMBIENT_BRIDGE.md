# Chronological model and full source ambient

This is an authored proof record for the representation dependency affecting
T01 and T02. It supplements the independent A20 audit; it is not an
independent review of the modules authored here. The source and the main
theorem hypotheses are unchanged.

The source ambient at lines 882–889 allows arbitrary locally finite rooted
labelled trees. `UnorderedLocal.Tree` is the actual unordered labelled graph
quotient constructed for A20, with vertex labels in `Option Nat`, edge
labels in `Nat`, and genuine finite-distance-ball isomorphisms. Repeated
labels are allowed in this ambient. `LocalTree.Tree` is the more specialized
chronological carrier used in the existing main proofs.

## Actual representative and redundant records

`ChronologicalPlaneVertices` and `ChronologicalPlaneVertexEquiv` identify
actual present plane addresses with actual chronological vertices. The map
is proved bijective; it is not an assumed coding equivalence.
`ChronologicalPlaneLabels.toLabelledPlaneTree` decorates this actual shape
with the original frozen/active vertex labels and original incoming
birth-time edge labels. At the root there is no incoming edge. An active
vertex has an actual `none` label inside a present slot, which differs from
an absent vertex slot.

`ChronologicalPlaneGeometry` proves that birth zero identifies exactly the
root and that parenthood is equivalent to the nonzero-birth and parent-ID
record condition. `ChronologicalBallRecords` then proves that any genuine
finite-ball isomorphism preserves every chronological record field. The
birth and frozen fields come from labels; height comes from distance to
the root; the parent field comes from the parent relation and the parent's
birth label.

`ChronologicalBallIso` constructs the converse actual finite-ball
isomorphism from equality of chronological record balls. Its final result
is an exact same-radius equivalence:

$$
B_h(F(T))=B_h(F(U))\quad\Longleftrightarrow\quad T_h=U_h.
$$

Here the left equality is equality of unordered labelled finite classes,
and the right equality is equality of the original complete chronological
record balls. Boundary labels are retained. No change of radius or
extra distinctness hypothesis is introduced. The specialization to unique
chronological IDs follows from `LocalTree.Tree`'s proved valid-ball data.

## Closed image and limits

`ChronologicalAmbientEmbedding.toUnordered` is the actual representative
followed by the forgetting-order quotient. Its injectivity and reflected
local convergence follow from the exact ball equivalence.

The image is proved closed, rather than postulated. A candidate ambient
tree in the image of every finite-ball coordinate has, at each radius, a
chronological record representative. The exact ball equivalence makes
these representatives compatible under restriction. Their records glue
to a valid coherent chronological tree, and equality of all generic finite
balls identifies its image with the candidate ambient tree. Equivalently,
the image is the intersection of the closed finite-coordinate support
conditions.

`isClosedEmbedding_toUnordered` and `exists_localLimit_iff_ambient` thus
hold for arbitrary filters, with a nontrivial-filter hypothesis only in
the existence-of-limit statement. An ambient pathwise limit is not
allowed to escape the chronological image.

`ChronologicalAmbientLaws` consumes the separately authored generic
`ProbabilityMeasureClosedEmbedding` theorem. The pushforward on genuine
probability laws is also a closed embedding. It reflects weak convergence,
preserves and reflects existence of weak limits, and derives support of
any ambient weak limit from closedness. There is no added support premise.

## Main-result consumers and paper argument checked

`MainLocalAmbient.source_local_convergence_equivalences` reconstructs
T01 in the full source ambient. Both the diagonal weak limit and the
fixed-history almost sure local limit quantify over `UnorderedLocal.Tree`.
The schedule quantifiers, infinite limiting schedule and literal printed
freezing reciprocal sum are retained. Its common-limit theorem supplies
the same measurable pathwise limit and its pushed-forward law.

The T02 consumer proves actual iid-history convergence in the same full
labelled ambient. The very same chronological limit, ordered by incoming
birth labels and then stripped of labels, has the already proved geometric
Bienaymé plane law. The geometric law and the $p<1$ hypothesis are unchanged,
including $p=0$ and finite extinction.

The checked paper argument is the assertion that canonical chronological
ordering and erasing labels are compatible with local convergence, together
with the use of the full locally finite labelled-tree ambient for T01.
The formal proof makes its representation step explicit through actual
vertices and complete finite balls. The closed-image argument is an
additional proof needed to justify the converse implication for arbitrary
ambient weak limits; it is not inferred merely from continuity.

## Current proof evidence

`ChronologicalPlaneGeometry.lean` passes an actual-file direct Lean check
with zero diagnostics; its log is
`chronological-plane-geometry-direct.log`. The six new modules from that
geometry through `MainLocalAmbient` pass an exact-source temporary
concatenation check with zero diagnostics, recorded in
`main-local-ambient-concat.log`. This development check writes no artifacts
and is clearly distinguished from the final imported check.

The expanded authored probe `ChronologicalAmbientStatements.lean` passes
nine expanded examples and fifteen closure queries in the exact-source
development check. Every closure is exactly `propext`, `Classical.choice`
and `Quot.sound`; the output is
`chronological-ambient-statements-concat.log`. The command and source
fingerprints are retained in `chronological-ambient-concat-evidence.txt`.
The complete dependency chain and `MainLocalAmbient` subsequently passed
the root artifact batch, 4,142 jobs, in
`ambient-positive-urn-poisson-reverse-build.log`. The authored probe also
passes its actual-import check, with nine examples and fifteen closures
using exactly the three permitted axioms; its current log is
`chronological-ambient-statements.log`.

The root independently reconstructed six statement types and seven
closures, all passing in `chronological-ambient-independent-statements.log`,
and reviewed the actual same-radius isomorphisms, closed-image gluing,
probability support argument and main consumers. That independent review
is recorded in `CHRONOLOGICAL_AMBIENT_INDEPENDENT_AUDIT.md` and found no
encoding or support premise left to discharge. The additional
chronological-to-full-ambient dependency is closed. No whole-paper
coverage or publication-ready claim is made from this scoped proof record.
