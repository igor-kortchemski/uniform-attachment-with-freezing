# A20 finite semantic helper: unordered equivalence gives an actual isomorphism

This is the author's self-review of `RootedUnorderedGraphIso.lean`.
The assigned scope is the finite forward semantic bridge needed by the
separate unordered local-topology construction. It is not a claim that
all of A20, or the finite converse, has been completed.

## Exact result

The exported theorem is
`Rooted.UnorderedEq.nonempty_unorderedIso` in namespace
`Freezing1.BinaryBijection`. For arbitrary finite `Rooted` trees $s,t$,

$$
s\mathrel{\texttt{UnorderedEq}}t
\quad\Longrightarrow\quad
\text{there exists a genuine rooted labelled isomorphism between their plane codings}.
$$

The witness has the exact existing type
`PlaneLabelled.UnorderedIso s.toPlaneLabelled t.toPlaneLabelled`. It
bijections actual present Ulam–Harris vertices, fixes the empty-address
root, preserves the parent relation in both directions, and preserves
complete vertex and incoming-edge label slots at every actual vertex.
The interface's `graphIso` therefore also gives an isomorphism of the
actual `PlaneTree.graph` simple graphs.

Vertex labels are arbitrary `Option ℕ`, and edge labels are arbitrary
natural numbers. In particular, labels may repeat, active vertex labels
`none` are retained, and no distinctness, chronological validity,
increasing-label, or normalization hypothesis is introduced. Equality of
the complete nested vertex slots distinguishes an active label from an
absent vertex; the root's absent incoming-edge slot is also preserved.

## Structural proof and reusable interfaces

`Rooted.nodeVertexEquiv` proves an actual decomposition

$$
\operatorname{Vertex}(\operatorname{node}(\ell,C))
\simeq
\{\text{root}\}\;\sqcup\!
\coprod_{j\in\operatorname{Fin}(|C|)}\operatorname{Vertex}(C_j).
$$

The branch embedding prefixes the address by $j+1$. Surjectivity follows
from the actual `Rooted.subtree` lookup defining the plane coding; it is
not a cardinality-only substitute for the vertex set. The public
`ActualVertex`, `NodeParts`, `nodeVertexEquiv`, branch-slot formulas, and
parent formulas are retained for downstream finite-converse work.

`Rooted.nodeGluedIso` glues genuine child isomorphisms along any bijection
of child positions whose paired incoming-edge labels agree. It checks the
parent relation separately at the overall root, within a child subtree,
and between different child branches. At a child-subtree root, the outer
incoming slot is the parent's edge label; at deeper vertices it is the
child's incoming slot. Both cases are proved explicitly.

For a sibling permutation of the full labelled child-pair list, occurrence
positions are bijected using equal finite fibres of each complete child
pair. The fibre cardinality is its list multiplicity, which is preserved
by `List.Perm`. This handles repeated identical child pairs without any
`Nodup` premise. Ordered `List.Forall₂` gluing handles the single-child
congruence constructor. The final theorem inducts over every constructor
of the actual `Rooted.UnorderedEq` relation: reflexivity, symmetry,
transitivity, sibling permutation, and subtree congruence.

## Verification and retained obligations

The actual proof file passed its direct Lean check with exit code zero
and no diagnostics in a local log (not retained). The root
artifact build is retained in
`verification/rooted-unordered-graph-iso-build.log`.

The authored expanded probe
`verification/RootedUnorderedGraphIsoStatements.lean` contains seven
examples and eight axiom closures. It reconstructs all witness fields,
the genuine simple-graph isomorphism, the root/child decomposition,
unrestricted gluing, and a concrete example with repeated edge and vertex
labels. Its actual-file direct check completed with exit code zero and no
diagnostics in a local log (not retained). All eight closures use
only `propext`, `Classical.choice`, and `Quot.sound`. The durable log is
`verification/rooted-unordered-graph-iso-author-statements.log`.

At this forward milestone, the finite converse from an actual isomorphism
to `Rooted.UnorderedEq` remained a separate obligation. It was subsequently
proved in `RootedUnorderedGraphIsoConverse.lean`; its separate authored
evidence and exact scope are recorded in
`A20_FINITE_GRAPH_ISO_CONVERSE_SELF_REVIEW.md`. Infinite coherent-ball
compactness, construction of a global isomorphism, and identification of
the full source quotient topology are owned by the topology worker. No
claim about those results follows merely from this forward helper.
