# Independent audit of the quantitative Poisson step

This review independently compares source lines 1805–1853 with
`PoissonSourcePolynomial`, `PoissonSourcePolynomialBound`,
`PoissonSourcePolynomialScale`, `PoissonSourcePolynomialChecks` and
`PoissonSourcePolynomialSlackChecks`, including the relevant definitions
in `PoissonLowerTail` and `RateFunction`. The reviewer did not author
those implementations. The new independent statement probe and the
derived small-margin reconstruction in that probe are authored checks,
not an independent review of their own proofs.

The corrected quantitative route has no missing mathematical premise.
The exact cubic tail conclusion is proved for every parameter stated in
the paper. Two auxiliary assertions in the printed derivation are false;
their counterexamples must remain in the source-correction record. The
all-margin scale theorem is explicitly repaired, as detailed below.

## Source meanings and quantifiers

The source function is exactly

$$
g(x)=(1+x)\log(1+x)-x.
$$

`bennettRate` implements this real expression. For the quantitative tail
step, $t>1$ ensures that its logarithm is evaluated at a positive number.
For the negative-slack counterexample, $1+x=1/2$ is also positive; the
counterexample does not exploit a totalized logarithm outside its usual
domain.

`LinearRegimeParameter` is exactly $0<c\leq1$.
`linearHeightFactor` is constructed from existence and uniqueness of the
source's solution $f(c)>1$, with its defining equation. In particular,

$$
g(f(c)-1)=\frac{2c}{c+1},\qquad
K=\frac{c+1}{2c},\qquad Kg(f(c)-1)=1.
$$

The probability is the actual Mathlib `poissonMeasure`, a probability
measure on the natural numbers with the usual singleton masses. The
strict event is literally ${k:\lambda t<k\}$; it is not replaced by a
weak tail. The independent probe reconstructs the first estimate for
arbitrary real $lambda>2$ and $t>1$, converting the rate to `NNReal`
without adding a hypothesis.

## Correct quantitative estimate and rounding

The strict witness is $k=\lfloor\lambda t\rfloor+1$, so
$\lambda t<k\leq\lambda t+1$ even at integral thresholds. The paper's
ceiling witness can lie outside the event, as already retained in S10.
The independent probe checks the integral threshold $\lambda=3$, $t=2$:
the strict witness is seven, whereas the ceiling is six.

The implementation starts from a proved integer log-factorial bound
derived from Mathlib's monotone Stirling sequence. It does not assume the
false real ceiling-factorial inequality. The rounding comparison gives

$$
\log\mathbb P(Z=k)\geq
-\lambda g(t-1)+\log\lambda-2\log(\lambda t+1)-1.
$$

Positivity of the actual singleton mass permits exponentiation. Its
inclusion in the strict tail yields the proved finite bound

$$
\mathbb P(Z>\lambda t)\geq
e^{-\lambda g(t-1)}\frac{\lambda}{e(\lambda t+1)^2}
\quad(\lambda>0,\ t>1).
$$

The exact source cubic conclusion then follows for **all** $\lambda>2$,
$t>1$:

$$
\mathbb P(Z>\lambda t)\geq
\frac{e^{-\lambda g(t-1)}}{(\lambda t)^3}.
$$

The proof genuinely covers both finite regimes. If $u=\lambda t\geq3$,
the explicit rounding prefactor dominates $u^{-3}$, using $e<3$ and a
polynomial inequality. If $2<u<3$, the actual mass at three belongs to
the tail. The proof establishes that this mass is at least $1/8$ for
$2\leq\lambda\leq3$, whereas the requested lower expression is at most
$u^{-3}\leq1/8$. There is no unreported large-rate or nonintegrality
assumption.

## Integer scale and all margins

For $\lambda=K\log C$, conversion to the source's logarithmic prefactor
uses the sufficient finite condition

$$
\log C\geq(Kt)^3.
$$

It is kept explicitly in the finite conversion theorem. It is stronger
than the source's displayed $\log C\geq Kt$ condition, but is supplied
when choosing a sufficiently large integer $C$, together with any fixed
lower logarithmic constraint and $\lambda>2$. It is not an additional
assumption on the final scale witness.

For $q=Kg(t-1)<1$, the proof uses
$C^{1-q}/(\log C)^4\to\infty$ to choose one integer $C>1$ satisfying
the complete chain

$$
\frac{6}{cC}\leq
\frac{e^{-K\log C\,g(t-1)}}{(\log C)^4}
\leq\mathbb P(Z>K\log C\,t).
$$

The exact printed exponent is supplied when $1<f(c)-\eta$.
`linear_source_rate_slack` derives the necessary strict rate inequality
from the characterized $f(c)$ and monotonicity on positive arguments.
The independent probe reconstructs the source's
$\delta=1-Kg(f(c)-1-\eta)\in(0,1)$ and both displayed scale
inequalities on this branch; it does not assume slack as a premise.

For every positive margin, including the full source interval
$\eta\in(0,1)$, the corrected theorem instead takes

$$
t=\max\left\{\frac{f(c)+1}{2},\ f(c)-\eta\right\}.
$$

The probe checks $1<t<f(c)$, $f(c)-\eta\leq t$ and the resulting
slack in $(0,1)$. The auxiliary exponential factor uses this safe $t$;
the probability on the right remains the original source $P(C)$ with
threshold $f(c)-\eta$. Monotonicity of the actual events transfers the
bound. This proves the needed all-margin lower bound, while visibly
changing the auxiliary exponent. It must not be described as a proof of
positive slack for the original exponent at every margin.

## Two actual counterexamples

The asserted inequality
$\lceil u\rceil!\leq u^3(u/e)^u$ for every $u\geq2$ is false.
At $u=21/10$, the right side is strictly below $3!=6$. The formal proof
uses a certified rational lower bound on $e$ and real-power monotonicity.
The independent probe combines it with
$\lambda=41/20>2$, $t=42/41>1$ and $\lambda t=21/10$, so this is
inside the paper's quantitative Poisson regime.

The claimed positive rate slack for every $\eta\in(0,1)$ is also
false. The implementation constructs an actual admissible $c$ from

$$
G=g(1/4),\qquad c=\frac{G}{2-G}.
$$

It proves $0<c\leq1$ and uses the defining uniqueness theorem to prove
$f(c)=5/4$. At $\eta=3/4\in(0,1)$, it then proves

$$
1-\frac{c+1}{2c}g(f(c)-1-\eta)<0.
$$

The argument compares $G\leq1/16$ with $g(-1/2)>1/8$ and uses the exact
normalization $KG=1$. This is an existence theorem with a constructed
witness, not a conditional inconsistency or an assumed value of $f$.

## Relation to the remaining source argument

The actual first-moment lower bound $5C^k$ and the uniform Bernoulli block
approximation were already proved through the repaired scalar tail route.
I inspected their relevant consumer signatures in `LinearBlockLowerTail`
and `MainLinearBlockCount`: they retain the original probability
threshold, use an unconditional random-root first-moment identity, and
do not assume the false factorial or all-margin slack assertions. The
new quantitative modules do not silently alter those hypotheses.

This review does not replace the separate audits of the actual forest
reconstruction, full uniform Poisson approximation, or random-root law.
The literal factorial assertion and the literal unrestricted rate-slack
assertion are refuted, not proved under extra hypotheses. They and S10
must remain visible in the inventory. The true cubic bound, exact
small-margin scale and corrected all-margin scale are proved separately.

## Imported proof evidence

The root artifact batch passes 4,142 jobs, including the five quantitative
modules: `ambient-positive-urn-poisson-reverse-build.log`.
The independently reconstructed probe
`A56PoissonPolynomialIndependentStatements.lean` passes its actual-import
check with exit zero and no diagnostics. It reconstructs ten statements,
including arbitrary real source rates, an integral threshold, the finite
rounding constraint, the full integer-scale witness, the source delta,
all-margin safe slack, the original probability threshold and both
counterexamples. Its fifteen axiom-closure queries all return exactly
`propext`, `Classical.choice` and `Quot.sound`. The durable output is
`a56-poisson-polynomial-independent-statements.log`.

Command: `lake env lean -DautoImplicit=false verification/A56PoissonPolynomialIndependentStatements.lean`.
No artifact files are written by this audit. No hidden premise, weakened
tail event or omitted parameter case was found in the corrected route.
