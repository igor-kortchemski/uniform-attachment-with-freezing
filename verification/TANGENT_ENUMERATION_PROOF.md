# Increasing-tree enumeration: proof record

Source scope: C01 and the tangent-counting clause of A19, source lines
869–875. The source identifies the cardinality of the unordered increasing
class with no active vertices as the odd derivative of the tangent at zero
and gives a Bernoulli-number formula. The class uses $n\geq1$ original
vertices and precisely the labels $1,\ldots,2n-1$.

The formal counting argument works with actual increasing full plane
binary trees. It uses the source-faithful unordered bijection already
proved for P01; it does not assume an enumeration of representatives or a
counting recurrence.

`FiniteFullBinaryTrees.lean` constructs finite candidate sets by vertex
count and label set, proves that every tree with those bounds belongs to
the candidate set, and obtains finite instances for the actual prescribed
classes. It proves an equivalence between the completely frozen binary
class and the corresponding source class through the established
unordered bijection. Candidate sets are only used as finite supersets;
their cardinalities are not asserted to count valid trees.

`FullBinaryActiveLeaves.lean` defines the actual finite type of active
leaves and proves that its cardinality equals the active-leaf count. A
marked active leaf can either be frozen with a new label or replaced by a
fork bearing that label and two active leaves. The latter operation
retains the ordered left and right branches. The proof establishes the
exact label and active-count changes and injectivity of the marked update.

`FullBinaryMaxLabel.lean` proves the inverse operation. In an increasing
tree with distinct labels, the largest label is either a frozen leaf or
a fork whose children are both active leaves. Erasing this largest label
therefore recovers one active leaf of the predecessor. Distinctness of the
full label multiset prevents competing occurrences in the two branches.

`IncreasingBinaryGrowth.lean` proves a genuine equivalence between pairs
consisting of a stage-$m$ tree, a marked active leaf and a choice of freezing
or splitting, and all stage-$(m+1)$ trees. A stage-$m$ tree has precisely
the labels $1,\ldots,m$. Both injectivity and surjectivity are proved using
the actual erasure operation. Finite instances are derived from proved
vertex-count bounds, not supplied as hypotheses.

`TreeGrowthPolynomial.lean` defines the finite weighted count

$$
Q_m(X)=\sum_{t}X^{\#\operatorname{activeLeaves}(t)},
$$

where the sum ranges over these actual stage-$m$ trees. The growth
equivalence and the two explicit active-count changes imply

$$
Q_0(X)=X,\qquad Q_{m+1}(X)=(1+X^2)Q_m'(X).
$$

The proof reindexes the finite sum through the proved growth equivalence.
It includes trees with zero active leaves; their empty marked-leaf type
contributes zero to the next stage. The constant coefficient counts exactly
the fully frozen trees, by an explicit subtype equivalence.

`TangentDerivativePolynomial.lean`, developed separately, proves that
this same polynomial recurrence evaluates to the actual iterated
derivative of the real tangent wherever the cosine is nonzero. Evaluation
at zero then identifies the constant coefficient with that derivative.
Consequently `source_fullyFrozen_card_tangent` states the actual source
cardinality identity

$$
\#\mathfrak T_{0,n}^{+}=\tan^{(2n-1)}(0),\qquad n\geq1.
$$

This is a substantive proof departure from the paper's cited external
tangent-number enumeration: the finite growth bijection and the polynomial
recurrence are reconstructed and proved directly. The paper's source
definitions, label convention, zero-active-vertex condition, positive
$n$ condition, and derivative order $2n-1$ were checked. The tangent
analytic realization is a separate proved dependency.

Current evidence: the finite-class, active-leaf, largest-label,
increasing-growth and final polynomial modules all pass actual-file direct
Lean checks with `autoImplicit=false` and zero diagnostics. Their logs are
retained under `verification/`, including
`tree-growth-polynomial-direct.log`. `TreeGrowthAxioms.lean` records the
closure probes. The thirteen source-copy probes pass and use only
`propext`, `Classical.choice` and `Quot.sound` (the fully frozen class
equivalence needs only `propext` and `Quot.sound`), as retained in
`tree-growth-source-axioms.log`. The ordinary imported-module closure
probe also passes: `tree-growth-axioms.log` records fourteen checked
closures with only those standard axioms. The separate root review of
these authored inputs is recorded in
`TANGENT_COMBINATORICS_INDEPENDENT_AUDIT.md`.

The Bernoulli-number equality

$$
\frac{4^n(4^n-1)|B_{2n}|}{2n}
$$

is now proved by the final consumer `TangentEnumeration.lean`. The
formal-series coefficient identity and its connection with the tangent
derivatives are supplied by the root-authored analytic modules.
`TangentBernoulliAlgebra.lean` proves the algebraic absolute-value step
from that explicit complex coefficient identity: the complex even-power
difference has norm $4^n(4^n-1)$, and the two consecutive factorials cancel.
This helper passes an actual-file direct check with zero diagnostics; it
does not assume the final Bernoulli formula. The final assembly discharges
its coefficient-identity premise with the separately proved formal-series
theorems. The polynomial representation alone would not complete C01;
the integrated proof includes all these additional dependencies.

The three algebraic helper source-copy closure probes also pass with only
`propext`, `Classical.choice` and `Quot.sound`; retained evidence is
`tangent-bernoulli-algebra-source-axioms.log`. The corresponding imported
probe file `TangentBernoulliAlgebraAxioms.lean` also passes, with evidence in
`tangent-bernoulli-algebra-axioms.log`.

The independent analytic/final-assembly review is recorded in
`TANGENT_ANALYTIC_AUDIT.md`. Its imported-module statement probe passes
nine reconstructed examples, including the exact source conjunction and
the boundary case $n=1$, and sixteen standard-axiom closures. Refreshed
root integration passes with 4,404 build jobs; the namespace-wide audit
passes 5,972 closures using only the standard three axioms. C01 and the
enumeration clause of A19 are therefore proved. This scoped status does
not claim complete coverage of the rest of the paper.
