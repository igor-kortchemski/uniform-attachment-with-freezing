# A34: actual active-height tail integral and real-power tail asymptotic

This is the author's self-review of the new proof modules
`ExponentialMomentTail.lean` and `ActiveHeightTailIntegral.lean`. Independent
statement review and artifact integration belong to the integrating agent.
The source scope is lines 1258–1270 of
`attachement-uniforme-1-final.tex`, for every real $p\geq1$.

## Actual-law moment identity and the split at seven

The random quantity is the error $|H(U_n)/h_n^+-1|$ under the existing
`Forward.uniformActiveHeightLaw x n`. This law samples the actual forward
tree and then a uniform active vertex of that realised tree. The standing
source hypothesis is `PositiveThrough x n`, with $n\geq1$ wherever a
positive normalization is needed.

`activeHeight_moment_layercake` proves the literal real-integral identity

$$
\mathbb E\!\left[\left|\frac{H(U_n)}{h_n^+}-1\right|^p\right]
=p\int_0^\infty
 \mathbb P\!\left(\left|\frac{H(U_n)}{h_n^+}-1\right|\geq u\right)
 u^{p-1}\,du.
$$

The real weighted tail is measurable and integrable. Finiteness follows
from the genuine actual-height moment integrability and the extended-valued
Mathlib layer-cake identity. In particular, this is not an equality obtained
only by totalizing two divergent Bochner integrals.

`activeHeight_moment_le_split_seven` checks the source decomposition at
$u=7$. On the lower interval the probability is at most one, and the
explicit real-power integral gives $p\int_0^7u^{p-1}\,du=7^p$. On the upper
interval the already verified exact closed-threshold Bennett bound for
the actual height gives

$$
\mathbb E\!\left[\left|\frac{H(U_n)}{h_n^+}-1\right|^p\right]
\leq 7^p+2p\int_7^\infty e^{-h_n^+g(u)}u^{p-1}\,du.
$$

All integral decomposition and comparison steps have proved integrability
hypotheses. The use of open half-lines instead of closed endpoints has no
effect under Lebesgue measure.

## The numerical threshold and exact dilation

`exp_two_sub_one_le_seven` proves $e^2-1\leq7$ using the installed proved
exponential bound and rational arithmetic.
`self_le_bennettRate_of_seven` specializes the existing analytic rate
inequality to $u\geq7$. Therefore the Bennett tail is bounded by

$$
J_p(m)=\int_7^\infty e^{-mu}u^{p-1}\,du,
\qquad m=h_n^+>0.
$$

The exact positive-dilation theorem proves

$$
J_p(m)=m^{-p}\int_{7m}^\infty e^{-v}v^{p-1}\,dv.
$$

For $m>0$, the coefficient $m^{-p}$ is exactly $1/m^p$; the expanded source
probe checks that literal form. The proof uses Mathlib's actual
`integral_comp_mul_left_Ioi` theorem and real-power multiplication, rather
than postulating the change of variables.

## The real-power asymptotic and proof departure

For $q=p-1\geq0$ and $u\geq7$, the logarithmic inequality
$\log(u/7)\leq(u-7)/7$ yields

$$
u^q\leq7^q\exp\!\left(\frac{q(u-7)}7\right).
$$

If $m\geq2q/7$ and $m>0$, the integrand is consequently bounded by

$$
e^{-mu}u^q
\leq7^q e^{-7m/2} e^{-mu/2}.
$$

The remaining exponential integral is evaluated exactly. This gives the
explicit estimate

$$
0\leq J_p(m)\leq
2\,7^{p-1}\frac{e^{-7m}}m,
\qquad m>0,\quad m\geq\frac{2(p-1)}7.
$$

`exponentialMomentTail_isBigO` records the source's claimed
$J_p(m)=O(e^{-7m}/m)$ as $m\to\infty$.
`activeHeight_exponentialTail_isBigO` composes it with the previously
proved divergence of $h_n^+$ for the admissible triangular schedule rows.
`activeHeight_moment_le_source_tail_asymptotic` also supplies the resulting
explicit actual-height moment bound.

This is a substantive proof departure: the source's phrase “by an iterated
integration by parts” is not formalized literally. The logarithmic envelope
proves the same displayed estimate for every real $p\geq1$, including
noninteger exponents, without an integer-exponent or tail-estimate premise.
The layer-cake identity, split at seven, rate comparison, exact dilation,
and the claimed asymptotic themselves are checked.

## Uniform moments and the source Lp conclusion

The proved first-step contribution gives $h_n^+\geq1/2$. Monotonicity of
the Bennett density in its mean therefore gives the uniform actual-law
bound

$$
\mathbb E\!\left[\left|\frac{H(U_n)}{h_n^+}-1\right|^p\right]
\leq7^p+2p\int_7^\infty e^{-g(u)/2}u^{p-1}\,du.
$$

The constant on the right is finite for every real $p\geq1$, as established
by the proved Gamma-density comparison. It depends on $p$ alone. This
derives boundedness using the split-at-seven argument, independently of
the earlier alternative generic MGF moment estimate.

`activeHeightError_eLpNorm_le_source_integral` and
`uniformActiveHeight_tendsto_Lp_via_tail_integral` finish the actual
all-finite-real-$p$ conclusion using this new moment bound at exponent
$p+1$, the exact Bennett probability limit, cutoff, and Hölder. No moment
bound or height-tail estimate is a new premise. The $n=0$ row is irrelevant
to the limit and is not included in the positive-normalization inequalities.

## Proof evidence and coverage status

`ExponentialMomentTail.lean` passed the actual-file direct Lean check with
exit code zero and no diagnostics (a local log, not retained).
Its artifact build also passed in
`verification/labelled-coding-exponential-tail-build.log`.

The actual final consumer check for `ActiveHeightTailIntegral.lean` passed
with exit code zero and no diagnostics in
a local log (not retained). Its artifact build passed with
3832 jobs in `verification/active-height-tail-integral-build.log`.

The actual authored expanded probe
`verification/A34ActiveTailStatements.lean` also passed with exit code zero
and no diagnostics. It contains twelve examples and fourteen axiom
closures, all using only `propext`, `Classical.choice`, and `Quot.sound`.
The durable log is `verification/a34-active-tail-author-statements.log`,
also available in a local log (not retained). The two new proof
modules total 402 lines and contain no proof placeholders or new axioms.

The intended reconciliation is: A34's mathematical claims are proved for
all real $p\geq1$, with the logarithmic-envelope proof departure explicitly
retained. Literal repeated integration by parts is not being certified.
No unresolved mathematical statement remains in this corrected A34 scope.
