# A37–A38: the corrected geometric proof of L08

This is the author's self-review of the new geometric proof, scoped to
source lines 1322–1378 and its L08 conclusion at lines 1311–1319. It is
separate from the existing Abel-summation proof, which remains unchanged.
The source and the whole-paper inventory have not changed. The root
maintains the coverage report and supplies artifact builds and independent
review.

`IntervalFreezingCounts` also makes both displayed finite count identities
literal: the attachment and freezing counts are actual Boolean filters
of $(a,b]$, their sum is $b-a$, and their signed difference is $S_b-S_a$.
It retains the freezing-count assertion separately from the already
proved attachment-only `EqProp9`.

## Mathematical construction

For integer $1\leq a<b$ and $1<\beta<C$ with $aC<b$, define

$$
\ell=\left\lceil\frac{\log a}{\log\beta}\right\rceil,
\qquad m=\left\lfloor\frac{\log b}{\log\beta}\right\rfloor,
\qquad q_k=\lfloor\beta^k\rfloor.
$$

`GeometricHeightBlocks` proves $\ell\leq m$ and
$a\leq q_\ell\leq q_m\leq b$, then proves the exact integer partition

$$
\sum_{a<i\leq b}f(i)
=\sum_{a<i\leq q_\ell}f(i)
+\sum_{k=\ell}^{m-1}\sum_{q_k<i\leq q_{k+1}}f(i)
+\sum_{q_m<i\leq b}f(i).
$$

Every summation index is an actual natural number. A geometric block
whose two integer cuts agree is empty and contributes zero. It is not
assumed to be nonempty. The number of indexed complete blocks satisfies

$$
\frac{\log(b/a)}{\log\beta}-2
\leq m-\ell\leq\frac{\log(b/a)}{\log\beta}.
$$

The actual reciprocal-population height sum `heightInterval` is proved
equal to this integer interval sum. The complete-block index $k$ here is
the source's complete-block index minus one.

## Finite estimates and exact rounding

`GeometricHeightBlockBounds` uses the existing proved interval count
identity and `EqProp9`, together with the actual endpoint ratio bounds.
The weak endpoint case, where a block has no integer point, is treated
explicitly. For $A\geq1$, $t\geq A$, $0\leq\eta<c$, and the true ratio
error at most $\eta$ throughout the integer block, it proves the printed
complete-block constants

$$
L=\frac{\frac{c+1}{2}\left(1-\frac1\beta-\frac{2}{\beta A}\right)-\eta}{c+\eta},
\qquad
U=\frac{\frac{c+1}{2}\left(\beta-1+\frac1A\right)+\beta\eta}{c-\eta}.
$$

The lower proof could use a smaller rounding loss, but retains the
source's valid loss of two to verify its exact $L$. The initial partial
block is at most $(\beta-1)/(c-\eta)$. The last partial block is at most
$(\beta-1+1/A)/(c-\eta)$. Thus the combined endpoint error is
$[2(\beta-1)+1/A]/(c-\eta)$; the additional $1/A$ is not dropped.

For $L\geq0$, the exact partition and block-count bounds yield

$$
\left(\frac{\log(b/a)}{\log\beta}-2\right)L
\leq H(a,b)
\leq\frac{\log(b/a)}{\log\beta}U
+\frac{2(\beta-1)+1/A}{c-\eta}.
$$

Here $H(a,b)$ is the actual reciprocal-population height sum, not an
auxiliary harmonic approximation. `GeometricHeightWindowBounds` divides
by the positive $\log(b/a)>\log C$ and supplies both normalized bounds.
It also proves the source's refined endpoint inequality
$2L\leq(c+1)c^{-1}(1-1/\beta-2/(\beta A))$ under the proved nonnegative
lower-constant condition.

## Passage to the source limits

`GeometricHeightEnvelopes` uses a small positive tolerance $t$ to control
both the ratio error and $1/A$. The actual rational formulas are
continuous at $t=0$, where their denominators are the positive $c$.
Mixed-error comparisons also control the literal source row error
$\eta_n(\varepsilon)$ when it is at most $t$.

The final geometric-ratio approximation uses the elementary inequalities

$$
1-\frac1\beta\leq\log\beta\leq\beta-1,
\qquad
\frac{\beta-1}{\log\beta}\leq\beta,
\qquad
\frac1\beta\leq\frac{1-1/\beta}{\log\beta}.
$$

They bound the upper and lower limiting errors by explicit constants
times $\beta-1$. This gives a uniform choice $1<\beta<C$ as close to one
as required. Continuity then chooses a positive error tolerance small
enough that the lower block constant is positive and both normalized
envelopes lie within the requested error of $(c+1)/(2c)$. The genuine
`NearOriginLinear` hypothesis supplies one outer cutoff and an eventual
uniform ratio bound. Finally $A_n\to\infty$ supplies $1/A_n\leq t$.

`GeometricHeight.eventually_source_lowerBlock_positive` explicitly
uses the actual finite maximum `nearOriginMaximum` as
$\eta_n(\varepsilon)$ and proves eventual positivity for each fixed
$\beta>1$. The source consumer has no extra geometric partition or
interval estimate as a premise. The final exports use the existing exact
`UniformLogIntervals` and `LogIntervalLimsup` types. The generic
quantified-estimate-to-finite-maximum/nested-limit conversion is reused;
the Abel estimates and their uniform theorem are not called.

The proof follows the manuscript's complete-block and boundary-block
strategy. It implements the limiting step through uniform tolerances and
continuous rational envelopes, rather than manipulating possibly
unbounded real-valued limsups without their eventual bounds. The literal
source `NearOriginLimsup` hypothesis is converted by the existing proved
equivalence, and the final conclusion has exactly the same finite
maximum, strict ratio window, and outer-limit order as L08.

The exact existing maximum is the supremum over all integer pairs in the
source window, with value zero when its finite index set is empty. Under
the paper's positive sublogarithmic cutoff hypothesis, the existing
`eventually_logIntervalPairs_nonempty` proves eventual nonemptiness for
each fixed positive outer cutoff. This evidence remains applicable
because the maximum, its pair set, and all cutoff definitions are
unchanged. The geometric estimate itself needs only the near-origin
condition and $A_n\to\infty$; it does not introduce the bulk lower bound
or sublogarithmic cutoff as new proof premises.

## False printed steps retained explicitly

`GeometricHeightSourceChecks` proves the following counterexamples.

- With $a=2,b=3,\beta=4$, the exact source indices are $\ell=1,m=0$.
  The first cut is $4>b$ and the last cut is $1<a$. The printed partition
  equality fails even for the actual all-attachment height sum. The
  restriction $1<\beta<C$, with $aC<b$, repairs the order of the cuts and
  still permits $\beta\downarrow1$.
- With $\beta=4/3,a=2,b=3,C=7/5$, the repaired ratio condition holds and
  $\ell=m=3$. The final interval has one actual attachment point, while
  $\beta^4-\beta^3=64/81<1$. Hence the printed comparison of the integer
  count with this real geometric length is false. The all-attachment
  population has actual ratio error at most $1/2<c=1$ on $[2,3]$.
- With $\beta=2,\ell=1,m=2,b=7$, the intermediate final-block denominator
  printed as $\beta^{\ell-1}$ produces the false numeric comparison
  $6\leq2$. The valid direct denominator for this final block is
  $\beta^m$. This is distinct from the fractional-cutoff count error.

These are finite proof defects, not counterexamples to L08. No false
printed step is counted as proved. The repaired endpoint term vanishes
under the original cutoff hypothesis, and the lower-constant sign needed
for multiplication by the block-count bound is explicitly supplied.

## Current verification

All seven production modules are frozen and individually passed fresh
actual-file direct Lean checks with exit code zero and no diagnostics:

- `GeometricHeightBlocks`: a local log (not retained);
- `GeometricHeightBlockBounds`: a local log (not retained);
- `GeometricHeightWindowBounds`: a local log (not retained);
- `GeometricHeightEnvelopes`: a local log (not retained);
- `GeometricHeightUniform`: a local log (not retained);
- `GeometricHeightSourceChecks`: a local log (not retained);
- `IntervalFreezingCounts`: a local log (not retained).

Each production module is below one thousand lines. Root artifact
evidence is retained in `verification/geometric-height-blocks-build.log`,
`verification/geometric-height-block-bounds-build.log`,
`verification/geometric-source-window-conditional-chebyshev-build.log`,
`verification/envelopes-chronological-exchangeability-build.log`, and
`verification/geometric-uniform-probability-embedding-build.log`.

The authored expanded probe
`verification/A37A38GeometricHeightStatements.lean` contains nine examples
and eighteen axiom closures. It expands the literal source finite maximum
and nested limits; both counts; the exact partition; printed complete-block
constants; corrected endpoint and normalized bounds; actual row-error
positivity; and two source counterexamples. The fresh actual-file check
passed with exit code zero and no diagnostics in
a local log (not retained). Its durable log is
`verification/a37-a38-geometric-height-author-statements.log`.
All eighteen closures use only `propext`, `Classical.choice`, and
`Quot.sound`. These authored checks remain self-review and do not replace
an available independent audit. No unresolved mathematical obligation
remains in the corrected geometric route just described; the false
literal printed steps remain refuted and explicitly recorded.
