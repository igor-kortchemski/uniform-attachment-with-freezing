# A87 scalar rate asymptotic and small-mean consequence

This is the author's scoped self-review of source lines 2326–2330,
`RateFunctionAsymptotics` and `BennettSmallMean`. It is not an independent
review of the conditional stochastic domination in that paragraph.

The rate is the exact source function $g(u)=(1+u)\log(1+u)-u$.
The ratio $g(u)/(u\log u)$ tends to one as $u$ tends to positive infinity;
the equivalent `IsEquivalent` statement is also proved. The proof uses
$\log(1+u)=\log u+\log(1+1/u)$ and elementary limits, without an assumed
asymptotic estimate or an extra positivity premise on the final ratio limit.
All nonzero denominator facts are supplied eventually on $u>1$.

The same exact rate satisfies $g(u)/u\to+\infty$. Thus, for every fixed
$\varepsilon>0$, $r g(\varepsilon/r)\to+\infty$ as $r\downarrow0$.
For any eventually positive deterministic mean $m_n=o(\log n)$, the source
scalar bound tends to zero:

$$
n\exp\left(-m_n g\left(\frac{\varepsilon\log n}{m_n}\right)\right)
\longrightarrow0.
$$

The proof eventually bounds it by $1/n$. It retains the arbitrary fixed
positive tolerance and the exact source normalization. It makes no claim
that the actual epidemic's conditional height distribution satisfies this
bound. The zero-mean stochastic case also remains separate: the literal
quotient expression at zero is not silently used to justify that branch.

Both modules pass actual-file direct compilation and focused artifact
builds (`capture-probability-rate-asymptotics-build.log`, 3,936 jobs;
`bennett-small-mean-build.log`, 2,291 jobs). The authored expanded probe
`RateFunctionAsymptoticsStatements.lean` reconstructs four exact statements
and queries five transitive axiom closures. Its current output is recorded
in `rate-function-asymptotics-statements.log`. Global integration evidence
is reported separately in the master report.

The remaining A87 obligations are actual conditional Bernoulli domination,
a repaired conditional Bennett/union estimate with correct indices and
vertex count, and its zero-mean branch. The previously proved forward
maximum result does not certify that alternative source construction.
