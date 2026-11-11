# Independent A33 audit and the A34 bounded-moment clause

This review was performed by an agent other than the author of
`CanonicalActiveSampling.lean`, `UniformActiveBernoulli.lean`,
`UniformActiveBennett.lean`, and `UniformActiveMoments.lean`. It checks the
source proof at lines 1250–1260 and the A34 claim of uniform finite moments.
It does not certify the source's split at seven or its specific displayed
integral asymptotic. The root coverage record remains authoritative.

## Statement reconstruction

For a deterministic schedule $x$ and horizon $n$, the standing hypothesis
is `PositiveThrough x n`, equivalently $n<\tau(x)$. The sampled height has
the existing law `Forward.uniformActiveHeightLaw x n`. Its definition first
samples the actual original forward tree and then samples uniformly from
that realised tree's active vertex set. The fallback used by the total
kernel on absorbed states is proved irrelevant under this hypothesis.

The representation theorem is an equality of actual probability measures:

$$
H(U_n)\ \mathop{=}^{(d)}
 \sum_{i=1}^{n}Y_i\mathbf 1_{\{x_i=+1\}},
\qquad
\mathbb P(Y_i=1)=\frac1{S_i(x)},
$$

where the $Y_i$ are independent. They need not be identically distributed.
The formal carrier is `Fin n → ℕ`, with
`Measure.pi (fun i => bernoulliMeasure 1 0 (reciprocalParameter ... i))`.
Coordinate `i : Fin n` represents source time $i+1$; its parameter is
$1/S_{i+1}$. In particular, the raw Bernoulli coordinate is not replaced by
zero at freezing times. The deterministic attachment mask is applied only
inside the sum. Coordinate marginal laws and independence are proved from
the explicit finite product measure.

The canonical sampling bridge was checked as an affected dependency. It
uses the previously verified full forward/reverse state-law identity,
injectivity of actual chronological vertex coordinates, preservation of
active status and height, and almost-sure nonemptiness. It does not assume
a uniform-height identity as an additional premise. All active reverse
labels have source reverse birth horizon $n$; hence their proved individual
depth laws agree, and the uniform active-label mixture gives the required
height law.

## Exact concentration and probability limit

For every $n\geq1$ and real $u>0$, both the closed event and the source's
strict event satisfy the exact bound

$$
\mathbb P\!\left(\left|\frac{H(U_n)}{h_n^+}-1\right|\geq u\right)
 \leq 2\exp\bigl(-h_n^+g(u)\bigr),
\qquad
g(u)=(1+u)\log(1+u)-u.
$$

There is no replacement of $g(u)$ by $g(u/2)$ in the new A33 exports.
The generic closed-threshold bound is obtained from strict bounds below
$u$ and continuity of the rate. The actual-height theorem transports that
bound through the proved array-law identity, with exact mean
`truncatedMean ... n = heightScale x n`. Positivity of the mean follows
from the schedule hypothesis and $n\geq1$.

`uniformActiveHeight_closed_deviation_tendsto` permits a different schedule
in every row, with `∀ n, PositiveThrough (rows n) n`. The earlier proved
divergence of `heightScale` and strict positivity of $g(u)$ imply that the
displayed deviation probabilities tend to zero. This is the source's
convergence-in-probability statement for the varying actual height laws;
no common coupling or assumed height-tail estimate is required.

## Uniform moments and all finite real Lp limits

The new moment theorem concerns the actual height error, not only an
auxiliary Bernoulli variable. For every real $q\geq0$ and $n\geq1$ it gives

$$
\mathbb E\!\left[\left|\frac{H(U_n)}{h_n^+}-1\right|^q\right]
 \leq 2\left(\frac{q}{1/2}\right)^q
       \exp\!\left(\frac{e}{2}\right).
$$

This constant is finite and independent of both the horizon and the
schedule. The positive lower mean $h_n^+\geq1/2$ is proved, rather than
assumed: positivity through the first step forces an attachment with
post-step population two, and that first coordinate contributes mean
$1/2$. The generic centered exponential bounds then yield moments.
Integrability is also established, so no conclusion relies on a
totalized nonintegrable Bochner integral.

The source's claim that the errors are bounded in every finite real
$L^p$, $p\geq1$, is therefore checked. For convergence in $L^p$, the proof
uses the uniform bound at exponent $p+1$ and the actual probability-tail
limit, via a cutoff and Hölder. This makes the needed uniform
integrability explicit. The row $n=0$, where the normalizing mean is zero,
is excluded from finite-horizon bounds and harmless for the limit.

## Proof departure and obligations retained

A33's independent representation, exact Bennett concentration, and
convergence-in-probability route are checked. The bounded-moment clause of
A34 and the resulting all-finite-real-$p$ convergence are checked through
the independent-array exponential-moment route. This is a substantive
proof departure from the source's integration at threshold seven.

The following literal A34 arguments were not checked by this milestone
and must remain separate obligations:

- the displayed source active-height tail-integral identity in its chosen
  real-integral presentation;
- the split of that integral at $u=7$;
- the explicit specialization $7\geq e^2-1$ and $g(u)\geq u$ for $u\geq7$
  (the existing analytic theorem has threshold $e^2-1$);
- the displayed change of variables and estimate
  $O(\exp(-7h_n^+)/h_n^+)$;
- the claimed iterated integration-by-parts argument for all real
  $p\geq1$.

Generic fixed-array extended-valued layer-cake results already exist in
`UniformBirthRelativeMomentLaw.lean`; their presence does not by itself
certify those more specific active-height source calculations.

## Verification

The four root-authored modules have fresh built artifacts. Build evidence
includes `verification/active-sampling-forest-relabel-slots-build.log`,
`verification/uniform-active-bernoulli-build.log`,
`verification/active-bennett-topology-metrics-build.log`, and
`verification/active-moments-density-star-convention-build.log`.

The independent expanded probe
`verification/A33ActiveHeightStatements.lean` contains ten examples and
ten axiom closures. Its actual-file direct Lean check completed with exit
code zero and no diagnostics. Every closure uses only `propext`,
`Classical.choice`, and `Quot.sound`. The log is retained as
`verification/a33-active-height-independent-statements.log`, also available
in a local log (not retained).

No semantic mismatch was found in the audited A33 statements or the A34
bounded-moment clause. This conclusion does not close the retained
specific A34 integration arguments listed above.

Subsequent work note: those A34 obligations were open at the time of this
independent A33 review. The later author-owned proof milestone is recorded
in `verification/A34_TAIL_INTEGRAL_SELF_REVIEW.md`; this A33 audit does not
serve as independent certification of those later modules.
