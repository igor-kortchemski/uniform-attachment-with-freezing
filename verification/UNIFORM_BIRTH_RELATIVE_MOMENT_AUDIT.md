# Independent A42 conditional and relative moment review

The integrating agent independently read source lines 1430–1445 and the
new Bernoulli, Bennett-integral, conditional-moment, mean-escape and final
moment modules. The author of those modules is a different proof worker.

The variables remain on the explicit product of the actual uniform birth
law and independent unmasked Bernoulli array, with the attachment mask
inside the birth-truncated sum. `relativeMoment_condExp` and
`relativeTail_condExp` prove the actual conditional expectations with respect
to the birth sigma-algebra. No conditional-distribution or independence
premise is inserted into these conclusions.

The closed-threshold Bennett bound has exactly $g(u)$ in the exponent.
It follows from the strict Bernoulli estimates by approaching the threshold
from below. The conditional layer-cake identity uses the literal non-strict
tail, every positive real power and the correct factor $p$. The nonnegative
integrals remain extended-valued until finiteness is proved, including the
zero-mean initial row. Ordinary Bochner integration is used only with the
corresponding integrability theorem.

The missing domination behind the manuscript's “simple matter to check” is
supplied. For every fixed positive lower mean, the Bennett tail integral is
finite by an explicit integrable Gamma envelope, and it tends to zero as
the mean increases. On every positive actual row, $M_n\ge1/2$ almost surely.
The proved A41 normalization and $h_n^+\to\infty$ show that $M_n$ escapes
every bounded interval in probability. Splitting on a bounded-mean event
then proves the actual expected Bennett integral tends to zero. Rare small
means are controlled by the finite lower-mean envelope; no convergence of
an expectation is inferred solely from convergence in probability.

Fubini and the conditional bound give
$\mathbb E|Z_n/M_n-1|^p\to0$. The proved inequality $M_n\le h_n^+$ gives
the literal source centered-error moment inequality and
$\mathbb E|(Z_n-M_n)/h_n^+|^p\to0$. Adding the A41 mean error gives
$Z_n/h_n^+\to1$ in every source $L^p$. The exported moment conclusions
even hold for every positive real power where stated. The initial row is
retained explicitly: $Z_0=M_0=0$; it is not removed by an all-row positivity
assumption.

This checks the source's conditional Bennett/layer-cake strategy with its
domination step expanded. `UniformBirthRelativeMomentStatements.lean`
reconstructs the actual relative quotient, centered quotient, normalized sum
and expected Bennett integral. Its direct check passes with nine transitive
closures containing only the three permitted axioms in
`uniform-birth-relative-moment-statements.log`. The final transfer to the
uniform forward height/logarithm limit (A43) is a separate consumer.
