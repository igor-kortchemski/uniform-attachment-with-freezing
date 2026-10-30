# Independent review of full-forest independence and matching

The integrating reviewer read source lines 1648–1659 and the relevant
definition/height paragraph, then reviewed the new cut-state, continuation,
relabel, slot, orbit and reconstruction modules authored by the forest
worker. This review concerns A47 and the full-forest independence input to
A51. The source hash is unchanged. Conditional means/variances in A51/A52
remain separate obligations until their actual consumers are checked.

`forestCut` is a complete augmented forest: it retains all surviving cut
vertices, actual later edges and parents, cut heights, true active vertices
and later freezing labels. Existing geometric bridges identify its unique
old root per component and distances. The actual step commutes with this
cut under the proved invariants; the cut-at-cut state consists of isolated
active roots. Thus the continuation law is derived from Algorithm 1,
rather than supplied as an independent-forest premise.

The normalizer bijects the actual bounded root set with slots $0,\ldots,m-1$
and fixes every future birth ID. The bound $m\le a+1$ prevents collisions
with later IDs. Relabeling changes the arguments of parent/height/clock
data and the graph vertices, while preserving every actual time label.
The exact joint law of the earlier whole tree and the complete slot forest
is the product of their genuine laws. This proves full-forest independence,
not merely independence of two statistics. It does not assert independence
of different forest components under the fixed schedule.

The root-erasure quotient is the actual orbit under permutations fixing
all later IDs. Kernel equivariance proves the full forest law invariant
under each slot permutation. Independent sampling from the genuine uniform
permutation measure therefore gives the same joint law with the erased
orbit and any observation. `rootMatchingParametrization` proves that these
permutations enumerate all bijections of the root slots with the actual
old active set, uniquely, including the empty case.

Full terminal reconstruction uses the old tree and the root-named
augmented forest. Its uniqueness proof recovers every field from genuine
history support, including defaults outside actual vertices. The total
choice operator is characterized on every actual compatible pair. The
final joint matching law proves compatibility on the law's support; it
does not assume an unproved reconstruction or forest distribution.

The bare source forest is a further, explicitly verified coarsening. Roots
become active stars and their freezing clocks are erased before old names
are forgotten. This whole bare forest remains independent of the earlier
tree. The bare matching identity retains the actual full terminal tree
jointly, while its independent driving data retain hidden root clocks.
It is not deterministic full-state reconstruction from bare data alone.

This distinction is necessary: the strictly surviving schedule $(+1,-1)$
at cuts 1 and 2 has two conventionally active stars and only one genuinely
active terminal vertex. `star_activity_counterexample` formally verifies
the loss. S17 therefore remains a source correction. The textual matching
must use the lower-cut active set (S08); the figure caption already does.
The corrected augmented reconstruction and actual bare independence are
verified; the incorrect full-state interpretation of the unaugmented
description is not certified.

`ForestIndependenceStatements.lean` independently reconstructs six exact
interfaces: the complete product law, bare independence, characterized
reconstruction, joint bare/full-terminal matching, all-root-bijection
parametrization and the cut-height/ancestor identity. Its direct check in
`forest-independence-statements.log` passes seven standard axiom closures.
The namespace audit and full-build record in the main report cover the
integrated dependencies. Downstream conditional-statistic results require
their own completion and source review.
