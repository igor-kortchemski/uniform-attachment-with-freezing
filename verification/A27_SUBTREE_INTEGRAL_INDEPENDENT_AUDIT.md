# A27 conditional subtree integrals: independent scoped audit

This audit independently reads source lines 961–969 and the frozen
`FirstChildConditionalIntegrals.lean`, `FirstChildInductionIntegrals.lean`,
and `FirstChildSourceInduction.lean`. The reviewer did not write these
three proof modules. Relevant semantic dependencies were also read:
`GeometricBranching`, `FirstChildFixedPoint`, `PlaneTree`, and
`PlaneTreeBranching`. This review concerns the new conditional-integral
scope of A27; it does not claim a new independent audit of every proof
used earlier for T02.

## Source statement reconstructed

Write $K$ for the number of children at the root, $\theta_j$ for child
$j$ with one-based indices, and $R$ for deleting the first child and
reindexing the remaining children. On $\{K>0\}$ the source assumes that
$\theta_1$ and $R$ are independent, each with the original tree law $\mu$.
For nonnegative measurable $f_1,\ldots,f_{n+1}$ it defines

$$
g_n(t)=\mathbf{1}_{\{K(t)=n\}}
\left(\prod_{j=1}^{n}f_{j+1}(\theta_j t)\right)
\frac{\mu(K>0)}{\mu(K=n+1)}.
$$

The three substantive identities are the conditional expectation of the
full child product expressed through $f_1(\theta_1)g_n(R)$ under $K>0$;
factorization of that expression as $\mu(f_1)\mu(g_n)$; and equality of
$\mu(g_n)$ to the remaining-child product expectation conditional on
$K=n$. The last identity uses the previously proved degree-mass
recurrence $\mu(K=n+1)=\mu(K=n)\mu(K>0)$. Normalized assertions require
the conditioning event to have positive mass.

## Statement and semantic comparison

`FirstChildStructure.source_induction_expectation_identities` gives all
three identities with one shared literal function
`sourceInductionIntegrand`, whose numerator is the actual
$\mu(K>0)$ and whose denominator is the actual $\mu(K=n+1)$. The function
uses the indicator of $K=n$, the remaining tests `f i.succ`, and the
children of the remainder with their indices shifted back to the first
position. The structure's zero-based index becomes `PlaneTree.child T
(i.val + 1)` in the actual plane-tree specialization. Thus the source's
one-based child indices, the deleted first child, and the degree event
are all retained.

The inputs are a probability law, the source conditional joint split
law, and genuine structural identities for a leaf and first-child
grafting. They do not include a branching conclusion, a moment estimate,
or a finite-child product law. The source wrapper derives the measure
fixed point from the split. For the actual tree carrier,
`eq_leaf_of_degree_zero` and `graft_child_dropFirst` prove the structural
premises; they are not probabilistic assumptions. The carrier is the
actual locally finite plane-tree space and allows infinite total trees.

The independent probe separately reconstructs the source split from
conditional `IndepFun` plus both original-law marginal equalities. This
checks that the joint-law input means precisely the paper's conditional
independence assertion, including the two marginal laws.

All tests have codomain $[0,\infty]$ and require only measurability. The
proof uses extended nonnegative integrals and finite product integration.
No boundedness or integrability hypothesis is added. In particular, the
result covers the source's nonnegative unbounded real-valued tests, and
also extended-valued tests. The source writes $n\geq1$; the formal
identities also hold at $n=0$ with the genuine empty product.

## Normalization and boundary cases

The positive event mass is required only for normalized conditional
statements. The successor degree mass proves that $\mu(K=n+1)>0$
implies both $\mu(K>0)>0$ and $\mu(K=n)>0$. Finiteness follows from the
probability-law assumption. `induction_normalizing_ratio` therefore
cancels a genuine nonzero finite denominator; no unconditional use of
$0/0$ is hidden.

The unnormalized `restrict_childrenLaw_of_fixedPoint` and
`lintegral_degree_children_product` have no positivity premise and cover
null events. At the source endpoint $p=0$, the actual law is concentrated
on the leaf and the one-child event is null. The independent probe checks
that the normalized constant-one integral on that null event is zero,
whereas its unconditional original-law integral is one. Thus the omitted
guard would give a false statement under Lean's totalized conditioning;
the implementation correctly retains the guard and the unnormalized
endpoint. This is a boundary convention, not a loss of the paper's
single-leaf conclusion.

## Proof route and verdict

The displayed source expressions and their exact normalization are
proved. The implementation first derives the actual finite-child joint
law by induction on measurable rectangles, then derives these integral
identities from that law. It therefore verifies their mathematical
content but does not check the manuscript's conditional-expectation
induction in its original order. This substantive proof-order departure
is explicitly recorded in the implementing self-review and must remain
in the coverage report. No circular dependence on the new integral
identities occurs in `GeometricBranching` or `FirstChildFixedPoint`.

No statement mismatch or extra unproved estimate was found in the
reviewed scope. The source's claimed branching property remains backed
by the earlier finite-child law and its actual plane-tree bridge.

## Current proof evidence

The independent expanded probe is
`verification/A27SubtreeIntegralIndependentStatements.lean`. It includes
five examples: all three literal source identities reconstructed from
conditional independence and its marginals; the actual normalizing
ratio and recurrence; the unnormalized arbitrary-test identity without
an event-positivity premise; the genuine positive-parameter T02 limit
law; and the null-event conditioning check. Its thirteen axiom closures
include the literal integrand, all three main identities, the finite
product theorem, the unnormalized laws, and the actual limit fixed point.
The fresh actual-file direct check passed with exit code zero and no
diagnostics in `/tmp/a27-subtree-integral-independent-statements2.log`.
The durable output is
`verification/a27-subtree-integral-independent-statements.log`. All
thirteen closures use only `propext`, `Classical.choice`, and `Quot.sound`.
The artifact builds for the frozen root modules are retained in
`verification/first-child-conditional-integrals-build.log`,
`verification/conditional-variance-coherent-iso-child-integrals-build.log`,
and `verification/source-variance-finite-ball-helpers-build.log`.
