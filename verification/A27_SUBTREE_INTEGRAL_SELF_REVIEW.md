# A27: the literal subtree expectation identities

This is the implementing reviewer's self-review. Source lines 961–969 use
nonnegative measurable tests, their degree-conditioned product, and the
explicit function $g_n$ involving the reindexed remaining children and
the ratio $\mathbb P(K>0)/\mathbb P(K=n+1)$.

`FirstChildConditionalIntegrals` proves finite-product integration for
arbitrary nonnegative measurable tests, including unbounded tests, using
extended integrals. The previously proved actual finite-child joint law
gives the conditional product identity. An unnormalized restricted-law
version is proved separately and remains valid on null degree events.

`FirstChildInductionIntegrals` defines the exact $g_n$, proves the actual
positive-degree probability, the successor degree-mass recurrence and the
normalizing-ratio identity. Its expectation equals the conditional product
of the remaining children, and the first-child factorization is proved.
The given positive-degree split law also proves the literal intermediate
expectation involving $f_1$ of the first child and $g_n$ of the remainder.

`FirstChildSourceInduction.source_induction_expectation_identities` supplies
all three source identities from the original conditional split and the
genuine first-child/remainder identities. It derives the fixed-point law;
no branching, finite-child product law or expectation estimate is an extra
premise. Positive mass is required only for degree events on which the
normalized conditional statement is used. The null case, including the
zero geometric parameter, is retained by the unnormalized theorem and the
already verified single-leaf branch of L05/T02.

The source expectation expressions are now checked. The implementation
derives them from the independently established finite-child joint law,
whose proof uses induction on measurable rectangles. It does not replace
that proof by the manuscript's order of conditional-expectation induction.
This proof-order departure is retained explicitly.

`A27SubtreeIntegralStatements.lean` checks three expanded source examples:
all three identities on arbitrary actual plane trees with the literal
one-based child indices and $g_n$; the actual positive-parameter limit law;
and the null one-child event for the genuine single-leaf law. Seven axiom
closures use only the three permitted standard axioms. Direct output is
`a27-subtree-integral-statements.log`; focused builds are
`first-child-conditional-integrals-build.log`,
`conditional-variance-coherent-iso-child-integrals-build.log` and
`source-variance-finite-ball-helpers-build.log`. Independent review of this
new proof-route scope has not yet been claimed.
