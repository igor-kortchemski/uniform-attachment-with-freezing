# A53: independent audit of the full-forest conditional growth route

The integrating reviewer reconstructed source lines 1770–1788, then read
`ConditionalRelativeChebyshev`, `ForwardForestConditionalChebyshev`,
`ForwardForestConditionalGrowth` and `MainConditionalGoodChainForest`.
The reviewer did not author these modules. The earlier independent
full-forest mean, variance and covariance audits supply their mathematical
inputs. Reviewer-authored generic invariant-average helpers retain their
separate provenance.

The new route uses the actual conditional expectation given the earlier
whole tree and complete bare forest. The random center and threshold are
measurable in that observation; all required integrability is proved.
Relative conditional Chebyshev is proved for a measurable random center,
then specialized to the actual good count. The source favorable event is
genuinely measurable in the observation: its $N$ and $M$ coordinates
descend to the complete bare quotient and equal the actual source counts.

The paper's $S_a\le a$ is false; the proof retains $S_a\le a+1$.
For $a\ge3$, $N\ge4a$ and old good count at least $b>0$ give a
conditional mean at least $3b$. The conditional probability of a next
count below $2b$ is at most $3M/b$. With $M\le k^3$ and $b=2^k$ this
gives $3k^3/2^k$, sufficient for the same uniform inverse-square order.
Thus the corrected constant and mean comparison are explicit, rather
than a hidden use of the printed factor-four claim.

The observed-event set integral of the actual conditional expectation is
the original joint event mass. Integrating the favorable bound and using
independence of the whole past from the forest statistics gives the
source failure decomposition. Normalization divides by the actual old
good-event mass; a null conditioning event has zero conditional measure
and satisfies the inequality separately. No conditional probability,
support property, independence estimate or growth estimate is assumed.

The terminal wrapper transports both old and next prefixes inside one
time-$n$ realization. The source consumer retains the literal near-origin
limsup and bulk liminf hypotheses, $\eta\in(0,1)$, and one common choice
of $C,\Delta,\varepsilon$ before the eventual row and every index in the
window. The exact finite positive-index cutoff is
$\max(1,\lceil\log A_n/\log C\rceil)$. Growth of $A_n$ supplies the
finite condition $a\ge3$ eventually. Previously proved $N/M$ tail bounds
and the explicit exponential-versus-polynomial comparison complete the
uniform $\Delta/k^2$ conclusion.

This verifies the source mean/variance/Chebyshev/tower strategy after
the stated finite corrections. The consumer calls no earlier tagged
growth or normalized one-step theorem; it reuses only generic prefix
transport and conditional normalization from that assembly. The
manuscript's separate erroneous initial good-chain base is retained
under A50 and is not certified by this one-step audit.

`ForestConditionalGrowthIndependentStatements.lean` reconstructs the
finite normalized step and the full original uniform-window consumer.
Its two examples and seven axiom closures pass with exit zero in
`forest-conditional-growth-independent-statements.log`, using only the
three permitted axioms. The authored probe has separate provenance:
three examples/seven closures. Artifact builds passed for the finite
route (3,849 jobs) and final consumer (3,959 jobs). Integration and
namespace-wide checks are recorded in the main report.
