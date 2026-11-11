# A56: quantitative strict Poisson tails and the polynomial scale

This is the author's self-review, scoped to source lines 1835–1853 and
the closely related rate-slack claim at lines 1805–1811. Existing
first-moment, forest-identification, Poisson-approximation, and alternate
rate-slack proofs remain unchanged. The root owns coverage metadata and
artifact integration. No full-paper or publication completion is claimed.

## Correct strict-tail estimate

`poisson_strict_tail_rounding_lower` in `PoissonSourcePolynomial.lean` proves, for
the actual `poissonMeasure` with every positive rate $\lambda$ and $t>1$,

$$
\mathbb P(Z>\lambda t)
\geq e^{-\lambda g(t-1)}
\frac{\lambda}{e(\lambda t+1)^2}.
$$

The singleton is always $k=\lfloor\lambda t\rfloor+1$, so it belongs to
the strict event even at integral thresholds. The proof starts from the
already proved logarithmic factorial estimate. Writing $u=\lambda t$,
it uses $u<k\leq u+1$ and the elementary logarithm inequality to control
the entropy rounding loss:

$$
k\bigl(1+\log\lambda-\log k\bigr)
\geq
u\bigl(1+\log\lambda-\log u\bigr)-\log(k/\lambda).
$$

This gives the explicit lower log mass
$-\lambda g(t-1)+\log\lambda-2\log(u+1)-1$, then the displayed
probability bound. No factorial inequality, conditional law, Poisson
approximation estimate, or tail estimate is assumed as an extra premise.

## The exact printed cubic prefactor

`poisson_strict_tail_cubic_lower` in `PoissonSourcePolynomialBound.lean` proves
the exact quantitative inequality printed in the source for **all** its
stated parameters $\lambda>2$ and $t>1$:

$$
\mathbb P(Z>\lambda t)
\geq\frac{e^{-\lambda g(t-1)}}{(\lambda t)^3}.
$$

For $u\geq3$, the proved rounding prefactor is at least $u^{-3}$, using
$e<3$ and an explicit polynomial inequality. For $2<u<3$, the actual
mass at three is in the strict event. That mass is increasing for
$2\leq\lambda\leq3$ and is at least $1/8$, as proved through its exact
Poisson mass and logarithms. Meanwhile the desired lower expression is
at most $u^{-3}<1/8$ because $g(t-1)\geq0$. Thus small thresholds are
included rather than hidden in an eventual-large-parameter restriction.

The displayed cubic-tail inequality is valid, but this proof does not
certify the manuscript's ceiling-mass/factorial derivation.

## Polynomial logarithmic scale and source margins

`logarithmicPoisson_polynomial_lower` in `PoissonSourcePolynomialScale.lean`
uses the exact Poisson parameter $\lambda=K\log C$. The finite conversion
from $u^{-3}$ to $(\log C)^{-4}$ retains the sufficient condition
$\log C\geq(Kt)^3$. This condition is explicitly supplied when choosing
the sufficiently large integer $C$; it is not deduced merely from the
source's weaker displayed condition $\log C\geq Kt$.

The polynomial scale choice uses the installed theorem that
$e^{b x}/x^4\to\infty$ for $b>0$, applied with
$b=1-Kg(t-1)$. Consequently it proves that

$$
C\frac{e^{-Kg(t-1)\log C}}{(\log C)^4}\longrightarrow\infty.
$$

`exists_poisson_polynomial_scale` chooses one integer $C>1$ satisfying
an arbitrary fixed lower logarithmic constraint, the actual rate bound
$\lambda>2$, the rounding constraint, and the complete chain

$$
\frac{6}{cC}
\leq\frac{e^{-K\log C\,g(t-1)}}{(\log C)^4}
\leq\mathbb P(Z>K\log C\,t).
$$

For the source $K=(c+1)/(2c)$,
`linear_source_rate_slack` derives $Kg(t-1)<1$ from
$1<t<f(c)$ using the actual characterized height factor. It does not
take that estimate as a source-consumer premise.
`exists_linear_poisson_polynomial_scale` therefore gives the exact
printed exponent $g(f(c)-1-\eta)$ whenever the threshold satisfies the
source Poisson step's explicit requirement $1<f(c)-\eta$.

All margins remain covered by
`exists_linear_poisson_polynomial_scale_all_margins`. For arbitrary
$\eta>0$, it uses the visible safe threshold

$$
t=\max\left\{\frac{f(c)+1}{2},\ f(c)-\eta\right\}\in(1,f(c)).
$$

The polynomial exponential rate uses this $t$. The actual probability
on the right remains the original $P(C)$ with threshold $f(c)-\eta$;
event inclusion transfers the bound. This is the same safe-threshold
repair already used in the existing full-scope proof, now with a genuine
quantitative polynomial prefactor. It is a corrected statement for
large margins, not a silent assertion that the original exponent has
positive rate slack on that range.

## Additional false printed auxiliary claims

The existing S10 remains: $\lceil\lambda t\rceil$ may lie outside the
strict event. The new proof always uses the strict floor-plus-one cutoff.

`printed_real_ceiling_factorial_counterexample` in `PoissonSourcePolynomialChecks.lean`
also proves that the asserted real bound
$\lceil u\rceil!\leq u^3(u/e)^u$ for all $u\geq2$ is false.
At $u=21/10$, its right side is strictly below $3!=6$. The proof uses the
installed rational lower bound on $e$ and genuine real-power monotonicity.
The example is compatible with the stated Poisson regime:
$\lambda=41/20>2$, $t=42/41>1$, and $\lambda t=21/10$.

`printed_all_margin_rate_slack_counterexample` in `PoissonSourcePolynomialSlackChecks.lean`
constructs an actual $c\in(0,1]$ with characterized $f(c)=5/4$.
For $\eta=3/4\in(0,1)$, it proves

$$
1-\frac{c+1}{2c}g\bigl(f(c)-1-\eta\bigr)<0.
$$

Thus the source's assertion that this slack lies in $(0,1)$ for every
margin in $(0,1)$ is false. The error occurs when the threshold passes
below one, where the positive-argument monotonicity of $g$ does not
apply. This explains why the exact-exponent consumer is explicitly
scoped and the all-margin consumer explicitly changes the auxiliary
threshold. These finite source defects do not refute the main lower
height bound or the already proved actual first-moment conclusion.

## Current proof evidence and exact remaining integration

Three files have individual **actual-file** direct Lean PASS0 checks
with no diagnostics:

- `Freezing1/PoissonSourcePolynomial.lean`:
  a local log (not retained);
- `Freezing1/PoissonSourcePolynomialChecks.lean`:
  a local log (not retained);
- `Freezing1/PoissonSourcePolynomialSlackChecks.lean`:
  a local log (not retained).

`PoissonSourcePolynomialBound.lean` and
`PoissonSourcePolynomialScale.lean` initially passed a clearly labelled
temporary development check of their exact source bodies while the sole
artifact integrator was unavailable at model capacity. The child wrote
no oleans. The historical development output is
`verification/a56-poisson-polynomial-development-statements.log` and is
not being relabelled as imported-file verification.

After resumption, the root built the frozen dependency chain and ran the
actual imported file `verification/A56PoissonPolynomialStatements.lean`.
The root confirmed exit code zero for that real-file check (session
50089), with no diagnostics and all twelve permitted closures. Its
durable current output is
`verification/a56-poisson-polynomial-statements.log`. The probe contains
nine expanded examples and twelve axiom closures; all closures use only
`propext`, `Classical.choice`, and `Quot.sound`. This closes the previously
pending imported verification, separately from the earlier development
evidence. The root has assigned independent review to another worker;
that review is separate from this author's self-review.

Coverage metadata must retain the two new false auxiliary claims and the
original S10. No mathematical estimate premise remains unproved in the
corrected quantitative/all-margin route. These local checks alone are
not a final GitHub publication or Palomar validation.
