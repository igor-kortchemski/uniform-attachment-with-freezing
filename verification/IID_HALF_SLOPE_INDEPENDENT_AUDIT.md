# Independent audit of the auxiliary iid half-slope estimate

This checks the root-authored `IidHalfSlope` against source lines
2301–2305 and the unconditional harmonic expectation at lines 2310–2313.
The reviewer did not author the implementation. The separate reconstruction
probe and its elementary positive-index sum reindexing are authored
verification inputs.

The module proves the auxiliary iid assertion as stated. It does not
prove the coupling of reversed epidemic increments with an iid walk,
nor that conditioning on the future hazard event preserves any iid law.
Those A85 coupling and A86 localized reverse-time arguments remain
**open**.

## Exact random variables and all-time event

`iidSignLaw p` is the actual infinite product law of Boolean signs,
with positive sign probability $p$. The variables `failures i` are the
negative-sign indicators at positive index $i+1$. Their independence
and Bernoulli laws are proved from the genuine coordinate laws and the
injectivity of the index shift. No independence premise is added.

The event `good` is literally

$$
\left\{x:\ \forall n\geq0,\quad
\sum_{i=1}^{n}\xi_i(x)\geq\frac n2\right\},
$$

where $\xi_i=1$ for a true sign and $-1$ otherwise. Time zero is
included and automatically satisfies the inequality. Every later time
is controlled at once; this is not an eventual-time or finite-window
event. The event is measurable as a countable intersection.

With $p=1-\varepsilon$, the proved limit is exactly

$$
\mathbb P_{\varepsilon}\left(
\forall n\geq0,\ \sum_{i=1}^{n}\xi_i\geq n/2
\right)\longrightarrow1
\quad\text{as }\varepsilon\longrightarrow0.
$$

The parameter is in `unitInterval`; its neighborhood filter at zero
is the usual admissible one-sided small-probability limit. The
independent probe reindexes the sums to the source's explicit interval
$1\leq i\leq n$, checking that the unused index-zero coordinate has
not changed the event or sign probabilities.

## Uniform proof in place of the SLLN shortcut

The identity $Y_n=n-2B_n$ identifies failure of the half-slope bound
with $B_n>n/4$, where $B_n$ counts negative signs. For $\theta>0$ and

$$
\varepsilon(e^\theta-1)\leq\theta/8,
$$

the finite Bernoulli MGF and Chernoff estimate give
$\mathbb P(Y_n<n/2)\leq e^{-\theta n/8}$, including all natural $n$.
The complement of `good` is the countable union over positive times,
so its probability is at most

$$
\frac{q}{1-q},\qquad q=e^{-\theta/8}.
$$

For any error budget $\delta>0$, the proof chooses $R>0$ with
$e^{-R}<\min(1/2,\delta/2)$, sets $\theta=8R$, and then chooses
$\varepsilon_0=R/(e^{8R}-1)>0$. Every
$0\leq\varepsilon\leq\varepsilon_0$ satisfies the finite MGF
constraint and the all-time failure probability bound by $\delta$.
Thus the theorem controls all times uniformly as the parameter tends
to zero. The source's bare SLLN reference is replaced by an explicit
finite exponential estimate and a summable union bound.

## Harmonic expectation

The expectation uses the actual iid marginals and finite integrability:

$$
\mathbb E_{\varepsilon}\left[
\sum_{i=1}^{m}\frac2i\mathbf1_{\{\xi_i=-1\}}
\right]
=2\varepsilon\sum_{i=1}^{m}\frac1i.
$$

The formal positive index is $i+1$ before reindexing, so every
denominator is positive. The independent probe specializes to
$m=\lfloor n/2\rfloor$ and reconstructs both sides with the source's
interval sums. Empty sums are included.

This is an **unconditional** auxiliary expectation. The module does
not turn it into the source's expectation localized on a future SIR
event. It supplies neither an epidemic/reverse-walk coupling nor the
last-half-window reduction; those remain separate retained obligations.

## Proof evidence

The root artifact is current and passes 3,806 jobs in
`iid-half-slope-merge-boundary-build.log`. The actual-import probe
`IidHalfSlopeIndependentStatements.lean` passes with exit zero and no
diagnostics. It reconstructs four expanded source statements and proves
the positive-index reindexing lemma. Its eight closure queries all
return exactly `propext`, `Classical.choice` and `Quot.sound`. Current
output is `iid-half-slope-independent-statements.log`.

No artifact-writing build is performed by this audit. No mismatch was
found in the auxiliary iid statement or unconditional harmonic
expectation; the source coupling and localized reverse argument remain
open as specified above.
