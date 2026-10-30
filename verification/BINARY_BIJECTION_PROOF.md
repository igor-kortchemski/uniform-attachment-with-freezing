# Recursive increasing binary-tree bijection: proof record

Source scope: P01 and the bijection component of A19. Definitions checked
at source lines 638–646 and 666, binary definitions and recursive map at
lines 724–755, inverse at lines 858–867, and the separate counting
corollary at lines 869–875. The tangent/Bernoulli enumeration C01 is now
proved separately; see `TANGENT_ENUMERATION_PROOF.md` and the two scoped
independent audits. It is not inferred from the bijection alone.

The source has unordered rooted trees with $n$ vertices, $n-1$ integer
edge labels, $n-k$ frozen integer vertex labels, and $k$ active vertices
all bearing the same symbol $a$. The combined integer labels occur exactly
once and are the prescribed finite set $A$. In the implementation, `none`
is the active symbol and `some l` is a frozen label. Integer labels remain
natural numbers; there is no extra distinct label for an active vertex.

`BinaryTreeRotation.lean` first constructs the actual recursive rotation
on auxiliary ordered rose-tree codes. A nontrivial rooted code splits off
its first child edge, sends that child subtree to the binary left branch,
and sends the remaining rooted tree to the right branch. The inverse
attaches the left subtree's root to the right subtree's root using the
binary root label. Their two inverse identities are proved by recursion.
This auxiliary raw equivalence is not asserted to be an unrestricted
unordered-tree bijection.

The target is a full plane binary tree: every vertex is either a labelled
leaf or a labelled vertex with exactly two ordered children. Mathlib's
ordinary `BinaryTree` stores no leaf values, so a separate full binary
datatype retains the frozen/active labels required here. Original rooted
vertices become binary leaves; original edge labels become binary internal
vertex labels. The implementation proves separate preservation of these
two label multisets and of the number of active labels. It proves

$$
\#\operatorname{leaves}(\Phi(t))=n,
\qquad
\#\operatorname{vertices}(\Phi(t))=2n-1.
$$

`IncreasingBinaryBijection.lean` defines the intrinsic local label bounds
independently of the binary map. Its `increasing_node_iff` characterizes
the ordered representative by strictly increasing sibling edge labels,
increasing child subtrees, increasing successive edges down paths, and a
frozen vertex label greater than every adjacent edge. It proves that the
rotation preserves and reflects increasing labels. The exact classes
retain $k$, $n$, and the complete multiset $A$. The derived count identities
give $n-1$ edge labels, $n-k$ frozen labels, and
$|A|=2n-k-1$; these counts are not extra bijection hypotheses.

Sibling order is only an auxiliary representation. The source-faithful
bridge uses `RootedUnorderedTrees.lean`: unordered rooted trees are
quotients by the equivalence and subtree-congruence closure of sibling
permutations. Integer/active data and the source local increasing
conditions without any sibling order are proved invariant. That intrinsic
predicate is `HeapIncreasing`; the earlier sorted predicate is proved
equivalent to `HeapIncreasing` together with canonical sibling ordering.

`RootedNormalization.lean` recursively normalizes children and sorts them
by edge label using the independently supplied `ListSortByKey.lean`.
Global distinctness of the prescribed integer labels gives distinct
sibling edge keys. The normalization is proved equivalent to its input
under actual sibling permutations/subtree replacements, invariant under
the full unordered relation, canonical, and the identity on canonical
trees. `exists_unique_canonical` proves existence and uniqueness of the
canonical representative. No unordered-to-ordered equivalence is assumed.

`BinaryTreeSourceDomain.lean` proves that the first child of a canonical
nontrivial code is the unique child with smallest root-edge label.
Consequently the sorted rotation is exactly the source's least-edge
algorithm. The unrestricted source map is retained separately; only the
increasing classes are claimed to be in bijection with all increasing
binary targets.

`UnorderedBinaryBijection.lean` constructs the actual source quotient,
lifts normalization using its proved permutation invariance, and then
restricts by the intrinsic increasing condition. Composition with the
explicit rotation gives `unorderedPaperEquiv`, with the standard label
set $A=\{1,\ldots,2n-k-1\}$, and the named bijectivity statement
`phi_paper_bijective`. The source-level map is explicitly the rotation of
the normalized representative; its inverse is explicitly the unordered
class of the recursively attached tree. Separate edge/frozen label
preservation remains visible on the quotient.

The figure prose/caption error is S20. Under the source's own definition,
$\Phi(\mathfrak T_{4,8}^+)$ belongs to $\mathfrak B_{4,8}^+$ and has $15$
vertices. An element with parameter $15$ would instead have $29$ vertices.
The implementation proves this contradiction explicitly, rather than
changing the parameter convention to match the caption.

All six source modules pass actual-file direct Lean checking with
`autoImplicit=false` and no diagnostics, including the final unordered
quotient consumer. Retained direct evidence uses the corresponding module
names under `verification/`, ending in `-direct.log`. The sixteen probed
dependency closures contain only `propext`, `Classical.choice`, and
`Quot.sound` (the actual normalization-isomorphism proof needs only
`propext` and `Quot.sound`); evidence is
`binary-bijection-dependencies-axioms.log`. Final quotient closure evidence,
root Lake integration, and independent source-statement reconstruction are
recorded separately. Root integration passes, and the independent
reconstruction in `UnorderedBinaryStatements.lean` passes, with its scoped
review in `UNORDERED_BINARY_AUDIT.md`. C01 and the tangent-counting clause
of A19 are now proved by the separate finite-growth and formal-series
modules, with final consumer `TangentEnumeration.lean`.

All ten final quotient closure probes contain exactly the standard three;
their evidence is retained in `unordered-binary-bijection-axioms.log`.
