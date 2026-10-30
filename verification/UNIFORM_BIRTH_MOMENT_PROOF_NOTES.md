# Random-birth moments and source proof correspondence

This is the author's scoped record for source A41–A43, lines 1415–1446 of
`attachement-uniforme-1-final.tex`. Independent review is recorded separately;
this file does not turn authored checks into independent review.

The objects are the independent product construction already identified with
the actual reverse tree's joint birth/height law in
`UniformBirthBernoulli.actualBirthHeightLaw_eq_auxiliary`. Its array coordinates
are the unmasked independent Bernoulli variables with parameter $1/S_i$ and
are independent of the birth coordinate. The attachment mask is inside the
birth-truncated sum. Actual uniform sampling includes active and frozen
vertices.

## Statements and boundary cases

`UniformBirthConditionalMoments` proves integrability of the conditional
relative moments and their actual conditional expectation given birth.
`relativeMoment_condExp_layercake` is the literal conditional layer-cake
identity for every real $q>0$; `relativeTail_condExp_bennett` is the closed-tail
Bennett inequality with the exact rate
$g(u)=(1+u)\log(1+u)-u$. Neither statement assumes a conditional distribution
or an unproved concentration estimate.

The zero-mean initial row is retained. For $n\ge1$, positivity of the actual
birth coordinate and the first attachment give $M_n\ge1/2$ almost surely.
The independent array and all conditional moments exist also at $n=0$;
asymptotic proofs discard that one initial index explicitly.

`UniformBirthMeanEscape` proves both $\mathbb P(M_n\le L)\to0$ for every fixed
$L$ and the source's expected Bennett integral limit. These follow from the
proved random-mean normalization and divergence of the deterministic height
scale. No order-$\log n$ or random-mean escape premise is added.

`BennettMomentIntegral` keeps the nonnegative integral extended-valued at zero
mean. For each $q,m>0$ it is finite, decreases with $m$, and tends to zero as
$m\to\infty$. The proof supplies an integrable Gamma envelope using
$g(u)\ge u-e^2$. The lower bound $M_n\ge1/2$ controls the rare small means;
convergence in probability of $M_n/h_n^+$ alone is not used as a moment bound.

`UniformBirthRelativeMomentLimit` integrates the exact conditional Bennett
bound to prove

$$
\mathbb E\left|\frac{Z_n}{M_n}-1\right|^q\longrightarrow0
$$

for every real $q>0$. The hypotheses are only positive rows and the source's
bulk lower bound, which are weaker than the full linear-regime hypotheses.
`UniformBirthMomentConclusions` supplies the ordinary real expectations,
the pointwise comparison of the centered height-scale error, and
$Z_n/h_n^+\to1$ in every real $L^p$, $p\ge1$.

`UniformBirthRealBennettIntegral` proves that the expected nonnegative Bennett
integral is finite on every positive row, that its real-valued version is
integrable, and that the literal real expectation upper bound and its limit
hold. Its use of `toReal` is backed by these finiteness proofs and the positive
mean characterization of `bennettMomentIntegral`.

## The retained harmonic calculation and S21

`UniformBirthHarmonicTail` proves the previously retained harmonic upper bound
from the near-origin and bulk assumptions. Its finite statement is uniform
over all birth indices $1\le B\le n$ with $B\ge A_n$.

S21 is necessary throughout: the actual complement sums over $B<i\le n$.
The inclusive source sum counts the birth summand twice; moreover its
harmonic comparison with $\log(n/B)$ fails at $B=n$. For the corrected strict
tail, `harmonicInterval_log_error` supplies exactly the required logarithmic
upper bound, including $B=n$. The final displayed normalized inequality
therefore holds with the corrected complement. No claim is made that the
printed inclusive equality or its inclusive intermediate estimate is true.

The already proved mean limit in `UniformBirthMeanLimit` uses a different
fixed-fraction cutoff argument, then sends that fraction to zero. The harmonic
proof is now checked separately; the stronger bulk-only route for the limit
remains a substantive proof departure.

## The source's final height argument

`UniformBirthSourceHeightLimit.linear_uniform_height_via_random_mean` combines
the genuine random-mean normalization with the already proved linear height
scale limit, then transports through the actual joint birth/height identity
and canonical uniform-sampling equivalence. Its conclusion is the original
uniform-height limit for all real $p\ge1$, with constant $(c+1)/(2c)$ and the
literal source assumptions. This certifies the source A43 random-mean route
in addition to the earlier forward proof.

## Evidence scope

The direct Lean checks and root-controlled dependency builds are recorded in
the corresponding `uniform-birth-*-build.log` files. The authored expanded-type
and transitive-axiom probe is `UniformBirthMomentStatements.lean`; input
closures are in `uniform-birth-relative-moment-inputs.log`. These local checks
do not constitute a whole-paper omission scan, a Comparator report, or a
Palomar deposit verification.

The final authored probe passed with six expanded examples and nineteen
transitive closures, each using only `propext`, `Classical.choice` and
`Quot.sound`. The ten input closures use the same three permitted axioms.
All direct module checks in this group passed without diagnostics; the
`uniform-birth-*-direct.log` files preserve their outputs. The independent
root audit and root-controlled builds remain separate evidence.
