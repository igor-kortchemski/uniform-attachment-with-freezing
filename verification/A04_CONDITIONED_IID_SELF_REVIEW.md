# A04 finite-survival-conditioned iid schedules: authored review

This proof implements source lines 342–343 and the stronger uniform-ratio
implication stated immediately before the iid example. It gives an explicit
existence coupling with the required conditional marginals. It does not
claim almost sure linear profiles under an arbitrary independent sampling
of the conditional rows.

## Exact source hypotheses and conclusion

The sign probability satisfies $1/2<p<1$ and the slope is $c=2p-1$.
For row $n$, the probability law is the actual infinite iid sign product
conditioned on the event $\tau>n$. The common survivor has the actual
same product law conditioned on $\tau=\infty$.

The implementation derives positive survival mass from the already proved
actual iid-walk extinction probability $(1-p)/p$. It is not added as a
hypothesis to the source-facing result. Every finite-conditioning event
therefore also has positive probability.

For any positive deterministic cutoff with $A_n\to\infty$ and
$A_n=o(\log n)$, the constructed rows satisfy both literal source
near-origin limsup and bulk liminf assumptions almost surely. In fact,
their complete global finite maximum over $A_n\leq i\leq n$ tends to
zero. The default-zero finite maximum is equivalent to the ordinary
maximum on every nonempty interval; the existing cutoff lemma proves
eventual nonemptiness under the stated cutoff assumptions.

## Generic nested-event construction

For decreasing measurable events $E_n$ with positive intersection mass,
let $E_\infty=\bigcap_n E_n$. Exact conditioning gives

$$
\mu(\,\cdot\mid E_n)
=a_n\mu(\,\cdot\mid E_\infty)
+(1-a_n)\mu(\,\cdot\mid E_n\setminus E_\infty),
\qquad
a_n=\frac{\mu(E_\infty)}{\mu(E_n)}.
$$

The formula is proved as an equality of measures from restriction and
scalar cancellation. If the residual event is null, its conditional law
is replaced by the genuine survivor probability law, and its coefficient
is proved zero. No zero measure is treated as a probability distribution.

The single probability space is

$$
[0,1]\times\Omega\times\Omega^{\mathbb N}
$$

with Lebesgue uniform measure on the first coordinate, the survivor
conditional law on the second, and the independent product of residual
probability laws on the third. The actual carrier uses the real line
restricted to $[0,1]$. Row $n$ uses the same complete survivor sample
when the common uniform variable is at most $a_n$, and its residual
coordinate otherwise.

The exact row law is proved by projection of the genuine product
measure and the threshold mixture, not assumed. Continuity of measure
from above proves $a_n\to1$. The shared uniform variable is strictly
less than one almost surely, so eventually every row is exactly the
same entire survivor sample. Equality is of whole schedules, including
every future sign, rather than equality only on one fixed prefix.

## Strong law and source assumptions

The actual iid strong-law drift passes to the survivor conditional law
by absolute continuity. One pathwise ratio limit and eventual equality
of entire schedules imply uniform ratios over any diverging lower
cutoff. The proof does not condition the sign variables and then assume
they remain iid.

`UniformTailRatio.sourceAssumptions` separately proves the stronger
uniform-ratio implication in the Introduction. The near-origin bound is
a direct restriction. For the bulk, $A_n/n\to0$ puts every fixed
macroscopic lower cutoff beyond $A_n$, and the uniform ratio lower
bound gives the source positive lower constant, allowed to depend on
the macroscopic fraction. Existing equivalences give the exact literal
finite-maximum limsup and finite-minimum liminf formulations.

The rows' actual conditioning proves survival through their own horizons
simultaneously almost surely. This supplies the original strict-survival
standing assumption needed by those equivalences. Individual conditional
rows are not assumed to survive forever. The common eventual survivor
and the dependence between rows are properties of the constructed
coupling only.

## Scope and proof evidence

Production modules are `IidLinearAssumptions`,
`ConditionalSurvivalCouplingMixture`, `ConditionalSurvivalCouplingUniform`,
`ConditionalSurvivalCoupling`, `IidLinearSurvivalSystem`,
`IidLinearConditionedRows`, and `IidLinearMaximumRatio`.
The final existence export is
`ForwardAnnealed.exists_conditioned_iid_linear_coupling`.

The deterministic assumptions module passed actual-file direct checking
with no diagnostics in a local log (not retained) and parent
artifact PASS3965. The generic mixture and uniform foundations passed
in local logs (not retained), with parent artifact PASS2598
in `verification/conditional-survival-coupling-foundations-build.log`.
The generic common coupling passed actual-file direct checking in
a local log (not retained), with parent artifact PASS3116
in `verification/conditional-survival-coupling-build.log`.
The actual survival system and finite-maximum equivalence passed in
local logs (not retained).

The final consumer passed actual-file direct checking with exit zero and
no diagnostics in a local log (not retained). Its parent
artifact passes 3,970 jobs in
`verification/iid-linear-conditioned-rows-build.log`.

`A04ConditionedIidStatements.lean` checks eight expanded statements and
fifteen transitive axiom closures. Its actual imported direct check passed
with exit zero and no diagnostics beyond the requested axiom output in
a local log (not retained). Durable output is
`verification/a04-conditioned-iid-author-statements.log`. Every closure
contains only `propext`, `Classical.choice`, and `Quot.sound`.
This is authored evidence; the parent coordinates the independent review.
No whole-paper or publication verdict is implied.

The subsequent parent independent review passes four expanded examples
and eleven closures in `a04-conditioned-iid-independent-statements.log`.
Its separate scope and verdict are in
`A04_CONDITIONED_IID_INDEPENDENT_AUDIT.md`. That review is not authored
by the implementing agent and does not change the explicit existence-
coupling interpretation or assert independence of conditional rows.
