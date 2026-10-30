# A20: independent audit of the unordered local topology

The integrating reviewer read source lines 882–889 independently of the
construction. The source asks for a complete separable metric on rooted,
vertex-labelled, edge-labelled, locally finite trees, with convergence
equivalent to eventual equality of every positive-radius labelled ball.
The reviewer did not author the broad-space construction or the finite
graph-isomorphism classification used here.

`UnorderedTreeTopology` supplies this statement without an unproved
reflection premise. Its carrier is the quotient of all actual locally
finite labelled plane trees by root- and label-preserving vertex
bijections. `PlaneRootedGraphIso` proves that the parent formulation is
equivalent to an ordinary rooted labelled graph isomorphism. Child order
is forgotten. Labels may repeat; no chronological ordering, increasing
edge labels or distinct vertex labels are assumed. The alphabets are
`Option ℕ` for vertices and `ℕ` for edges, representing the paper's
natural labels and the active symbol.

The finite classification is proved in both directions, including
repeated labels. Closed coherent towers of finite unordered balls form a
Polish space. Finite representative fibres and compactness produce
compatible ordered representatives and an actual infinite locally finite
tree. Compactness of the finite ball-isomorphism fibres produces a single
global vertex bijection when all balls agree. These constructions prove
both surjectivity onto coherent towers and injectivity modulo actual
graph isomorphism. The internal `FiniteIsoReflection` premise of the core
module is discharged in the final module by
`Rooted.unorderedEq_of_nonempty_unorderedIso`.

`complete_separable_metric`, `localMetricSpace_complete` and
`localMetricSpace_topology` supply an actual compatible complete metric.
`tree_sequence_tendsto_iff` has exactly the source quantifiers: for every
positive radius there exists a threshold after which all balls agree.
`exists_actual_graph_representative` supplies an actual tree graph with
finite degrees. The corresponding plane labelled topology is proved for
arbitrary countable alphabets; the unlabelled variant was checked at the
earlier topology milestone.

The independent expanded probe is
`A20IndependentTopologyStatements.lean`: ten examples and ten axiom
closures, with output `a20-independent-topology-statements.log`. It passed
without errors; every closure contains only `propext`, `Classical.choice`
and `Quot.sound`. The final focused artifact build passed in
`unordered-topology-source-geometry-local-necessity-build.log` (3,952 jobs).

The broad A20 topology claim is proved. A separate affected dependency
remains: earlier main local-limit formulations use the chronological
record-ball model. Their faithful embedding with closed image into this
full ambient space, and the associated weak-law transport, are being
proved. This audit does not count that bridge as complete and does not
certify whole-paper coverage or publication readiness.
