# A20 finite semantic reflection: actual isomorphisms give quotient equality

This is the author's self-review of
`Freezing1/RootedUnorderedGraphIsoConverse.lean`. It completes the finite
converse to the separately verified forward bridge. Its scope is finite
rooted labelled trees, as required to identify the finite-radius classes
in the source's local topology (source lines 879–889). The infinite
quotient, metric, Polishness, and convergence characterization remain
separate results and require their own current evidence.

## Exact meaning

The two headline exports in namespace `Freezing1.BinaryBijection.Rooted`
are `unorderedEq_of_nonempty_unorderedIso` and
`unorderedEq_iff_nonempty_unorderedIso`. For arbitrary finite rooted trees,

$$
s\mathrel{\texttt{UnorderedEq}}t
\quad\Longleftrightarrow\quad
\text{there exists a rooted labelled isomorphism of their actual plane codings}.
$$

The isomorphism is the established `PlaneLabelled.UnorderedIso` structure:
an equivalence of actual present vertices, preservation of the root and
the parent relation in both directions, and equality of the complete
vertex and incoming-edge label slots. The statement does not merely
compare numbers of vertices, collections of labels, or unlabelled simple
graphs. Conversely, an isomorphism of the unlabelled simple graphs alone
is not used as a sufficient premise.

All `Option ℕ` vertex labels and all natural-number edge labels are
allowed, including repeated labels, repeated isomorphic branches, and
active labels `none`. No increasing-label, normalization, distinctness,
or chronological-validity premise is added. The finite quotient equality
is the actual quotient by the sibling-permutation and subtree-congruence
relation, not an additional equivalence relation defined from the target
isomorphism.

## Proof correspondence

The source treats equality of finite rooted labelled trees as standard.
The present proof supplies the encoding equivalence needed to justify
that interpretation. It is an explicit structural proof of finite
isomorphism classification, not a new probabilistic argument or an
assumed topological identification.

First, actual root children are recovered from the parent relation. The
source and target lists of child positions are each equivalent to their
actual root-child sets. The given isomorphism therefore induces a
bijection of child positions even when all labels repeat. Preservation of
the incoming-edge slot matches the corresponding edge labels;
preservation of the root vertex slot matches the root labels.

For each child, induction on the relative address length proves that the
whole descendant branch maps into the branch determined by that child.
The inverse global vertex equivalence proves surjectivity of this branch
map. This constructs `childVertexEquiv` and the genuine restricted
`childIso`. The latter checks the parent relation and both complete label
slots. At the relative child root, the restricted incoming-edge slot is
absent on both sides; its outer incoming edge was matched separately.
At every deeper vertex, the restricted incoming slot is exactly the
corresponding outer slot.

Finally, strong induction on the size of the source finite tree applies
the converse to every child. Child equivalences are assembled in order
using the actual subtree-congruence constructor. The induced position
bijection is then converted to a permutation of the target list. The
finite position permutation preserves multiplicities; no choice of a
unique label is used. This gives the original `Rooted.UnorderedEq`
relation. The reverse implication is the previously verified
`Rooted.UnorderedEq.nonempty_unorderedIso`.

## Verification

The complete actual proof file passed a fresh direct Lean check with
exit code zero and no diagnostics in
`/tmp/rooted-unordered-graph-iso-converse9.log`. Parent artifact evidence
is retained in `verification/rooted-unordered-graph-iso-converse-build.log`.

The authored expanded probe
`verification/RootedUnorderedGraphIsoConverseStatements.lean` has eight
exact-type examples and twelve axiom closures. It reconstructs the
reflection and its converse, actual quotient equality, the branch
position equivalence with edge-label and subtree-isomorphism witnesses,
the complete restricted-isomorphism fields, a repeated-label instance,
the active-versus-frozen root obstruction, and unrestricted structural
assembly. Its actual-file direct check passed with exit code zero and no
diagnostics in `/tmp/rooted-unordered-graph-iso-converse-statements.log`.
The durable log is
`verification/rooted-unordered-graph-iso-converse-author-statements.log`.
All twelve closures contain only `propext`, `Classical.choice`, and
`Quot.sound`.

This is self-review; the topology consumer's independent use does not by
itself turn it into an independent source review.

## Retained scope

No assertion of whole-paper coverage, publication verification, or
Palomar mechanical validation follows from this finite bridge. The
infinite local-topology worker must still supply the actual realization,
global isomorphism, and topology transfer results, and instantiate them
with the proved finite reflection rather than leave reflection as a
premise.
