# Source proposition P01: unordered trees and binary rotation

Independent review by the integrating agent, which did not author the
tree, normalization or quotient modules. Source lines 742–867 are unchanged.
The scalar list-sort helper was authored by this reviewer; this dependency
is not described as independently reviewed here.

The source class consists of finite rooted unordered trees, with active
vertices labelled by the same letter, distinct integer labels on every
other vertex and edge, increasing edge labels away from the root, and a
frozen vertex label larger than all its adjacent edge labels. The target
consists of full plane binary trees with active leaves, integer labels on
every other vertex, and increasing labels along descending paths.

`Rooted.UnorderedEq` permits arbitrary sibling permutations and replacement
of an unordered-isomorphic child in any context, with equivalence closure.
This is a finite rooted unordered-tree coding. `HeapIncreasing` expresses
the intrinsic source label conditions without a sibling order. Its
node characterization checks every child, its incoming edge and its
parent vertex label; recursive `rootAbove` conditions check the next edges.
Its invariance under the quotient relation is proved, so the increasing
source subtype is intrinsic.

`Rooted.normalize` recursively normalizes children and sorts siblings by
their edge labels. With the source's distinct global integer labels, it
produces the unique canonical representative in the same unordered class.
The proof supplies actual equivalence, uniqueness, invariance under every
generator and preservation of both edge and frozen-vertex labels.
`unorderedCanonicalEquiv` constructs the quotient equivalence; no existence,
uniqueness or representation premise is assumed.

On canonical representatives `phi` takes the least root edge as the binary
root, sends its child subtree to the left and the remaining root tree to
the right. The recursive `psi` glues the two inverse trees by the same
labelled edge. Their inverse identities are proved on raw ordered trees;
`phi_increasing_iff` restricts them to the independently defined increasing
classes. Canonical normalization and the intrinsic increasing subtype then
give `unorderedPaperEquiv`, the full source P01 bijection.

The map preserves active labels and integer labels, separately sending edge
labels to binary internal vertices and frozen-vertex labels to leaves.
An $n$-vertex source tree has $n$ binary leaves and $2n-1$ binary vertices.
The standard label set is exactly $\{1,\ldots,2n-k-1\}$. Zero or inconsistent
parameters introduce empty classes rather than a missing extra hypothesis;
positive source parameters are included.

The constructive inverse argument of the manuscript is checked. The source
figure's parameter inconsistency S20 is certified for the actual quotient:
the image of the $k=4,n=8$ tree has fifteen vertices, whereas binary
parameter fifteen would require twenty-nine vertices.

`UnorderedBinaryStatements.lean` reconstructs the quotient, exact standard
classes, canonical uniqueness, map/inverse and label-preservation interfaces.
Its focused Lean and axiom evidence is recorded in
`unordered-binary-statements.log`. The enumeration of this class by tangent
numbers and Bernoulli numbers (C01 and the final part of A19) remains a
separate obligation.
