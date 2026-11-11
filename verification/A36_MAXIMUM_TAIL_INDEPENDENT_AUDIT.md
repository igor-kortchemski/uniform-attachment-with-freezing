# Independent A36 uniform maximum-tail and moment audit

This review concerns the root-authored `MaximumUniformTail.lean`,
`TailIntegralSeven.lean`, and `MaximumTailMoments.lean`, against source
lines 1279–1285. The reviewer did not author those modules. The shared A34
analytic layer-cake and exponential-tail dependencies were authored by
this reviewer and have separately attributed evidence and root review;
this document does not relabel their authorship as independent review.

## Actual finite input and the retained source defect

The observable is the existing actual forward tree maximum
`Forward.treeHeight`, under the genuine `Forward.treeLaw x n`. The finite
input is derived from its previously proved MGF, not assumed as a new
maximum-tail hypothesis. It retains both actual correction factors:

$$
\mathbb P\!\left(\frac{H_n}{h_n^+}\geq C\right)
\leq\exp\!\left(\log(n+1)+\log C-h_n^+g(C-1)\right),
\qquad C\geq1.
$$

The $n+1$ term retains the true vertex-count bound, and the extra $\log C$
retains the one-child-edge factor in this direct forward MGF proof. The
normalization is positive under $n\geq1$ and $n<\tau$.

This is a corrected input to the asymptotic proof. It does not prove the
paper's false finite P03 upper bound with factor $n$. The existing actual-law
counterexample and S16 remain unchanged. No A36 conclusion is obtained by
silently promoting that false finite formula to a premise.

## One rank for all real thresholds

The proof constructs the finite constant $K=1+7/g(1)$, with $g(1)>0$, and
checks

$$
\log C\leq K g(C-1)\qquad\text{for every real }C\geq2.
$$

For $2\leq C\leq8$, use $g(C-1)\geq g(1)$ and $\log C\leq C-1\leq7$.
For $C>8$, the established threshold comparison gives
$g(C-1)\geq C-1\geq\log C$. These cover the boundary and unbounded range
without a threshold-dependent cutoff.

For admissible rows with $\log n/h_n^+\to0$, height-scale divergence gives
one sufficiently large rank for which

$$
\log(n+1)\leq\frac{g(1)}4h_n^+,
\qquad h_n^+\geq4K.
$$

The affected deterministic dependency
`eventually_log_nat_succ_le_mul_scale` was checked: it controls
$\log(n+1)$ from the actual hypothesis involving $\log n$, using
$\log(n+1)\leq2\log n$ eventually and the proved positivity/divergence of
the scale. It does not assume a tree estimate.

Those same two row conditions absorb both finite correction terms
simultaneously for every real $C\geq2$. The resulting theorem has the
required quantifier order

$$
\exists N\ \forall n\geq N\ \forall C\geq2,\qquad
\mathbb P\!\left(\frac{H_n}{h_n^+}\geq C\right)
\leq e^{-h_n^+g(C-1)/2}.
$$

The closed-threshold conclusion is stronger than the source's strict
threshold; the independent probe reconstructs the source's literal strict
version with the same rank. The standing model assumptions are exactly
admissible rows and $\log n/h_n^+\to0$.

## The actual maximum moment method

For $u>7$ and positive scale, nonnegativity of $H_n/h_n^+$ shows that
$|H_n/h_n^+-1|\geq u$ forces $H_n/h_n^+\geq u+1$. After the scale exceeds
one, the single uniform-threshold rank therefore gives

$$
\mathbb P\!\left(\left|\frac{H_n}{h_n^+}-1\right|\geq u\right)
\leq e^{-g(u)/2}\qquad\text{for every }u>7.
$$

Again, the rank is selected before $u$. Thus the bound may legitimately
be used throughout the tail integral on that row.

Actual moment integrability is proved separately for every row. The
genuine-support bound $H_n\leq n$ gives a finite bound on the absolute
normalized error, including the totalized zero-scale row. This prevents
the real integral calculation from relying on an unproved integrability
claim or a divergent Bochner integral.

The generic real layer-cake helper applies to that actual error. It splits
at seven, bounds the lower part by $7^p$, and bounds the upper part by the
established actual tail. For every real $p\geq1$, eventually

$$
\mathbb E\!\left[\left|\frac{H_n}{h_n^+}-1\right|^p\right]
\leq7^p+p\int_7^\infty e^{-g(u)/2}u^{p-1}\,du.
$$

The right-hand side is finite and depends only on $p$. No alternate MGF
moment estimate is assumed. The independent probe also reconstructs a
finite bound on the whole sequence by absorbing the finitely many initial
real moments into the eventual constant; integrability of those rows is
already proved.

The bound at exponent $p+1$ combines with the already proved actual
maximum probability limit and the generic cutoff/Hölder argument to
give all finite real $L^p$ limits. The existing T03 theorem is unchanged;
the new consumer checks the source's stated moment strategy. The
separately recorded A34 logarithmic-envelope replacement of repeated
integration by parts is retained.

## Verification and conclusion

Focused root builds passed in
`verification/forest-population-uniform-tail-build.log`,
`verification/tail-integral-seven-build.log`, and
`verification/maximum-tail-moments-build.log`.

The independent expanded probe is
`verification/A36MaximumTailIndependentStatements.lean`. It contains eight
examples and ten axiom closures, including the explicit same-rank strict
source bound and the derived whole-sequence moment bound. Its actual-file
direct check completed with exit code zero and no diagnostics. All ten
closures use only `propext`, `Classical.choice`, and `Quot.sound`. The
durable log is `verification/a36-maximum-tail-independent-statements.log`,
also available in a local log (not retained).

The subsequent production corollary requested from this reviewer lives
separately in `MaximumTailBoundedness.lean`; that addition is authored work,
not independent review of itself. It does not change the root-authored
modules audited here.

Separately attributed production evidence: `MaximumTailBoundedness.lean`
passed its actual-file direct check without diagnostics, and its artifact
build is recorded in `verification/maximum-tail-boundedness-build.log`.
The authored two-example/two-closure probe
`verification/A36AllRowsBoundednessStatements.lean` passed without
diagnostics; both closures use only the three permitted standard axioms.
Its durable log is
`verification/a36-all-rows-boundedness-author-statements.log`.

No semantic mismatch was found in the audited A36 statements or their
affected maximum-law dependencies. The corrected finite input is derived,
the threshold quantifiers are faithful, and the actual moment and all-real
$L^p$ conclusions follow through the claimed tail method. S16/P03 remains
explicitly refuted; this audit does not certify the false finite statement.
