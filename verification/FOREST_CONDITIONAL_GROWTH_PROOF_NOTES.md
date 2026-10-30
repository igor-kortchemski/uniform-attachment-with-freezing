# The complete-forest conditional source argument

This authored correspondence covers manuscript A53, lines 1770–1788, and
its A47/A51/A52 inputs. Independent review is maintained separately by the
root. The actual forward tree measure is used throughout.

The new route ends in
`MainConditionalGoodChainForest.linear_conditional_goodChain_failure_bound_from_forest`.
It uses the literal near-origin limsup and bulk liminf assumptions, strict
survival through each source horizon, and $0<\eta<1$. It gives one constant
$\Delta>0$ for every block in the stated source window, with conditional
failure probability at most $\Delta/k^2$.

## Paper arguments actually checked

1. The earlier tree and the whole cut forest have the proved actual product
   law. Root exchangeability and uniform matching were derived from the
   original transition law. They are not extra source hypotheses.
2. The source tall count $N$, marked-root component maximum $M$, and inherited
   good mark are functions of the complete bare forest and earlier tree.
   Distinct-component conditional negative correlation, same-component marks,
   the exact conditional mean, and the conditional variance bound are checked.
3. `ConditionalRelativeChebyshev` proves the random-center conditional
   Chebyshev calculation by conditional expectation monotonicity and pull-out.
   `ForwardForestConditionalChebyshev` supplies all square integrability from
   the actual finite population bound. Its center is the actual conditional
   mean. No conditional estimate is assumed in the final theorem.
4. On the favorable event with old good count at least $b$, tall count at
   least $4a$, and component maximum at most a cap, the corrected mean is at
   least $3b$ for $a\ge3$. Conditional failure to double has probability at
   most $3M/b$.
5. `ForwardForestConditionalGrowth.real_inter_le_of_observed_condExp` explicitly
   integrates the conditional indicator over an event in the observation
   sigma algebra. The favorable event uses the whole past and bare forest.
   Its probability is bounded by the old-good event probability.
6. The two exceptional forest events factor from the old-good event by the
   actual $N,M$ independence law. Their union and the favorable contribution
   give the joint failure estimate.
7. Normalizing by the old-good event gives the actual conditional probability.
   A null conditioning event gives Mathlib's zero conditional measure; no
   positive-probability or lower-bound premise is introduced.
8. The exact two-prefix joint law transports this conditional probability to
   two prefixes of one terminal source tree. This step is about normalized
   conditional probabilities, and does not silently identify conditional
   expectation functions on two different carriers.
9. The proved source block-count and marked-root maximum tails and the scalar
   estimate for $k^3/2^k$ yield a uniform inverse-square bound. The final new
   proof calls the complete-forest route. It does not call the old tagged
   continuation growth bound or the old one-step conditional estimate.

## Corrections and finite conventions

The source's $S_a\le a$ is false because it omits the initial root (S08).
The checked bound is $S_a\le a+1$. Replacing the printed factor-four mean
step by a factor-three step gives $3M/b$ and, at the source thresholds,
$3k^3/2^k$. This preserves the required $O(k^{-2})$ order. The literal
half-mean Chebyshev coefficient four remains included in the relative
theorem at $\theta=1/2$. The repeated $N_k$ in the printed ratio must be
$\overline N_kN_k$, as already recorded in S08.

The finite source lower cutoff is

$$
\max\left(1,\left\lceil\frac{\log A_n}{\log C}\right\rceil\right).
$$

`GeometricChainPositiveCutoff` proves the exact positive-index predicate for
every $A_n>0$, including $A_n\le1$, and its eventual reduction to the ceiling
cutoff when $A_n\to\infty$. The new uniform theorem uses the exact cutoff.

S17 is preserved: marked roots are counted in the source maximum even after
they freeze, while genuine active tall descendants are used in $N$. Their
height zero permits the bare-forest observable identities for the
nonnegative source threshold. The condition $0<\eta<1$ and the proved
$f(c)>1$ provide that threshold condition. Root-clock loss still prevents
full activity/label reconstruction from bare stars; geometric reconstruction
is stated separately.

## Evidence and scope

The new generic Chebyshev, source conditional consumer, tower integration,
normalized growth and uniform-window modules have clean focused direct Lean
checks. The final root-controlled artifact build passes 3959 jobs
(`verification/main-conditional-good-chain-forest-build.log`). The authored
`ForestConditionalGrowthStatements.lean` probe passes three expanded examples
and seven queried closures, all with the three standard axioms
(`verification/forest-conditional-growth-statements.log`). Earlier source-interface reconstruction passes
eight examples and twenty-nine axiom queries, all using only `propext`,
`Classical.choice` and `Quot.sound`.

This document does not certify unrelated inventory obligations, whole-paper
coverage, a GitHub release, or a Palomar deposit.
