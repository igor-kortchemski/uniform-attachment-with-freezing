# A60–A61 auxiliary Bernoulli coupling: independent audit

The reviewer did not author the `BernoulliPairCoupling` proof modules.
The source was read independently at lines 1870–1977, with the main
review focused on lines 1911–1977. The complete Kernel, Actual, Words,
Block, Separated, Thinning, ThinningBounds, Complete, Tails, Error,
Conclusions, and SourceChecks modules were read. Relevant actual
history increment and coalescence interfaces were also inspected.

## Source argument and exact indexing

For a block $(a,b]$, the source represents the first tracked height by
independent attachment-masked Bernoulli increments with probabilities
$p_i=\mathbf{1}_{x_i=1}/S_i$. It augments the same process by independent
coins with probabilities $q_i=\mathbf{1}_{x_i=1}/(S_i-1)$, dominates the
second height on the event that the two components remain separate,
and then thins the enlarged coins to parameters $p_i$. The expectation
of their discrepancy is

$$
\sum_{a<i\leq b}\frac{\mathbf{1}_{x_i=1}}{S_i(S_i-1)}.
$$

The formal transition index is $j=i-1$: it takes reverse phase $j+1$
to phase $j$. The actual parameter is therefore computed from $S_{j+1}$
and $x_{j+1}$. The recorded words run downwards from $b$ to $a+1$.
`sum_descending_eq_sum_Ico` proves the exact reindexing, so the finite
error over $j\in[a,b)$ is precisely the source sum over $i\in(a,b]$.
No attachment mask is lost at a freezing step.

At an attachment, the genuine positive population is at least two.
This proves that both parameters lie in the unit interval and that
$(1-p_i)q_i=p_i$. The boundary $S_i=2$ gives $p_i=1/2$, $q_i=1$ and is
included. On a freezing step both increments vanish and both
parameters are zero. No false division estimate is used there.

## Actual history and independence

The construction starts from the original reverse-history transition,
not from two independently sampled heights. `augmentLaw` leaves its
entire history marginal unchanged. Where the two roots are distinct
and the first actual increment is zero, the auxiliary coin is forced
to equal the second actual increment. Where that coin is unobserved
by the required formula, a fresh Bernoulli coin is drawn.

`augmentLaw_map_pair` proves the resulting exact product law using
the actual Bernoulli marginals, the genuine exclusivity of the two
increments before coalescence, and $(1-p)q=p$. Independence is a
conclusion of this calculation. It is not supplied as an extra
conditional-history assumption.

`coupledBlockLaw` iterates those genuine augmented transitions.
`coupledBlockLaw_map_history` retains the whole completed original
history, including every intermediate state. Genuine validity and
presence of the tracked vertices are propagated at each step.
`coupledBlockLaw_map_drivers` proves that the entire first word and
entire auxiliary word have their independent product law. Thus both
independence across phases and independence between the driver
families are joint assertions on one constructed probability space.

`coupledBlockLaw_increment_relations` identifies each recorded first
coordinate with the actual increment read from that completed common
history, and gives the actual second increment by the before-step
root-equality formula. The indices selecting this preceding phase
are proved through preservation of the previous history.

## Coalescence boundary and S24

Once the two roots have merged, they remain merged. On the event of
distinct roots at the bottom of the block, they must therefore have
been distinct before every step. The second actual height gain is
then at most the sum of the enlarged auxiliary coins, while the
first gain equals the first driver sum exactly. The separated-root
event is retained in the event inclusion; it is never declared
independent of the drivers or removed by conditional factorization.

The source prose saying that a first height increment precludes a
merge when the coalescence time is at most $i-1$ is false at the
current-step boundary. `source_current_merge_boundary` proves an
actual two-root counterexample: with one positive step, the first
height increases, the roots merge, and the recorded coalescence time
is zero, with probability $1/2$. S24 remains refuted.

The formal identity uses equality of the roots in the actual state
before the step. This gives the correct branch even for a merge
occurring during the current step. The proof consequently verifies
the repaired construction and final source estimate without
certifying the false prose.

## Monotone thinning on the same space

`completeLaw` is the product of the coupled history law with fresh
retention coins of probabilities $1-p_i$. It preserves the entire
original history marginal. Its three driver arrays have the proved
product law: the first word, enlarged word, and retention word are
jointly independent. The thinned word is $\widetilde Y_i=\xi_i R_i$,
where $(1-p_i)q_i=p_i$.

`completeLaw_map_first_thinned` proves that the first and thinned
words are independent copies of the original-parameter product law
on this same probability space. `completeLaw_thinning_le` proves the
coordinatewise monotonicity. These are constructions, rather than
an assumed existence of a coupling.

The tail gap is exactly the crossing-event probability. The sum
discrepancy is an integrable natural-valued variable, and its
expectation is exactly the finite sum of parameter differences.
The crossing event implies a positive discrepancy, whose probability
is at most this expectation. This is the literal source
crossing-event/expectation/Markov route, including all real thresholds.

## Actual product tails and uniform error

`actual_separated_tail_le` uses the actual common-history event
inclusion and the proved product driver law. The thinning estimate
then replaces the enlarged tail at the cost of the exact discrepancy
sum. The actual one-vertex gain is separately identified with the
first driver-sum tail. For two distinct initial roots, their initial
depths are zero, so the final product is exactly the product of their
two true marginal height tails.

`actual_pair_tail_le_product_add_errors` adds the actual coalescence
risk to the actual discrepancy sum. Its proof uses no earlier
supersolution pair-tail estimate. Coalescence and mismatch remain
two explicit error terms until their genuine finite estimates are
applied.

`auxiliaryError_eq_reciprocal_sum` is the exact source reciprocal
sum above. The parameter difference is bounded by twice the square
of the original parameter. Source near-origin population control
and the already proved uniform logarithmic interval estimate then
give a common error constant on a fixed-ratio block. The coalescence
sum is controlled by the same population lower bound.

`uniform_geometric_actual_pair_tail` proves one $L>0$, one
$0<\varepsilon<1$, and one eventual range of $n$ that work for every
admissible integer cut $a$, every genuine upper history, every pair
of distinct roots of that history, and every real threshold.
The window is $A_n\leq a$ and $aC\leq\varepsilon n$, and the error
is $L/a$. In particular $a=C^k$ gives the required uniform
$O(C^{-k})$. The epsilon window from the beginning of the source
proof is retained. This does not assert population control on every
block merely from $C^{k+1}\leq n$ alone.

## Verdict and evidence

The read proof route supplies the full actual history, all driver
arrays, and all retention coins on one space, proves their required
laws, and reaches the actual marginal product-tail bound with the
source reciprocal error. No hidden coupling, path-law, probability
estimate, survival-series, or independence premise was found.
S24 and the source's indexing conventions remain explicit.

The independently expanded probe is
`verification/A60A61BernoulliPairIndependentStatements.lean`, with
twelve examples and twenty axiom closures. It checks the actual
whole-history marginal, the three-array product law, actual phase
increments, separated-event domination, thinning, the exact crossing
event and discrepancy expectation, expanded reciprocal sum, actual
marginal product-tail inequality, uniform source quantifiers, and
the actual S24 counterexample. Its actual imported direct check passed
with exit code zero and no diagnostics in
`/tmp/a60-a61-bernoulli-pair-independent-statements1.log`. The durable
output is
`verification/a60-a61-bernoulli-pair-independent-statements.log`.
All twenty closures use only `propext`, `Classical.choice`, and
`Quot.sound`. The final imported consumer has parent artifact
PASS3943 in
`verification/component-actual-maximal-pair-conclusions-build.log`.
This scoped audit does not imply full-paper coverage or a publication
verdict.
