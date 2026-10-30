# Independent A41 birth-tail and random-mean review

The integrating agent reviewed source lines 1415–1429 independently of the
author of `UniformBirthTail`, `UniformBirthLogTail` and `UniformBirthMeanLimit`.
The actual birth law and random conditional mean are those audited in
`UNIFORM_BIRTH_REPRESENTATION_AUDIT.md`.

The logarithmic event is transformed exactly to $B<n^{1-\delta}2^\delta$.
Its integer strict CDF therefore uses the ceiling of this real threshold.
`auxiliary_log_birth_exact_CDF` retains the source denominator and numerator
at that actual integer cutoff; its eventual bound by the horizon follows
from the proved sublinear cutoff. The probability tends to zero for every
$\delta>0$, including the source range $0<\delta<1$. Birth zero causes no
logarithm problem: every actual birth is positive for positive horizons.

The mean-limit theorem assumes only positive rows and `BulkLowerBound`.
This is stronger than the source under its complete linear assumptions.
For a fixed fraction $e>0$, the true post-birth tail after $\lfloor en\rfloor$
is bounded by a constant from the bulk lower bound. Dividing by the universal
diverging height scale makes that error vanish. Births before this cutoff
have probability at most $\lfloor en\rfloor/n$. Sending $e$ to zero gives
convergence in probability. The proved deterministic bound
$0\le M_n/h_n^+\le1$ then supplies all real $L^p$, $p\ge1$.
No convergence of the mean is assumed in the theorem.

This fixed-fraction cutoff proof is a substantive departure from the
manuscript's harmonic/log-birth comparison. The logarithmic birth-tail
statement is checked separately, but the displayed harmonic upper estimate
is retained as unchecked. The false inclusive complement equality is
explicitly corrected by the strict post-birth identity (S21).

`UniformBirthMeanLimitStatements.lean` independently expands the actual
random-mean normalization in both the probability and all-real-power
statements, and the literal logarithmic event. Its check passes with five
transitive closures containing only the three permitted axioms in
`uniform-birth-mean-limit-statements.log`. This does not certify A42's
relative moment limit, which is being developed separately.
