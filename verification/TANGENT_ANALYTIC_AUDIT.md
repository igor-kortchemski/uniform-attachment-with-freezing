# C01 analytic and final-assembly audit

The reviewer independently read the root-authored
`TangentDerivativePolynomial.lean`, `TangentFormalSeries.lean`,
`TangentFormalDerivatives.lean`, `TangentBernoulliSeries.lean` and
`TangentEnumeration.lean` against C01 at source lines 869–875.

This is an independent review of those analytic modules and the final
assembly. The reviewer authored the earlier unordered-tree representation
and combinatorial counting modules and `TangentBernoulliAlgebra.lean`;
those inputs are explicitly not independently audited here. They require
the separate root review. Their precise proved interfaces were checked as
inputs to the final assembly.

The source requires, for $n\geq1$, the actual increasing unordered tree
class with $n$ frozen vertices, no active vertices, and integer label set
$\{1,\ldots,2n-1\}$. The reconstructed final statement uses exactly
`Nat.card (UnorderedIncreasingClass 0 n (Finset.Icc 1 (2*n-1)))`, rather
than the cardinality of an arbitrary sequence or auxiliary family. The
two real equalities are

$$
\#\mathfrak T_{0,n}^{+}
=\frac{4^n(4^n-1)|B_{2n}|}{2n}
=\tan^{(2n-1)}(0).
$$

The domain has original size $n$ and binary target size $2n-1$. The
enumeration does not use the erroneous figure parameter $15$ for the
image of an eight-vertex source tree. The source convention $n\geq1$ is
retained explicitly; it is not silently extended to $n=0$ using truncated
natural subtraction or totalized division.

The following argument components were checked.

1. The rational polynomials start at $P_0(X)=X$ and satisfy
   $P_{m+1}(X)=(1+X^2)P_m'(X)$. Their analytic realization is proved for
   every real point with nonzero cosine. The inductive proof obtains
   equality on a neighborhood using continuity of the cosine before
   taking derivatives. It therefore does not use an equality at a single
   point to identify derivatives. At zero, the cosine is one, so the
   theorem identifies $P_m(0)$ with the actual iterated derivative of the
   real tangent.

2. The complex formal series is explicitly
   $T=i(2/(\exp(2iX)+1)-1)$. Its inverse is legitimate: the denominator
   has constant coefficient two. The proof establishes $T(0)=0$ and the
   positive-sign equation $T'=1+T^2$. These facts are proved from the
   exponential series and its derivative, rather than assumed from the
   name of the definition.

3. Polynomial evaluation into the formal power-series algebra and the
   formal derivation chain rule imply $D^mT=P_m(T)$. Applying the constant
   coefficient and the proved identity $T(0)=0$ gives $P_m(0)$. The
   installed Mathlib theorem `constantCoeff_iterate_derivative` supplies
   exactly $m!\,[X^m]T$; no factorial is omitted. This bridges formal
   coefficients to actual real derivatives through the same polynomials.
   No analytic convergence of the complex series is assumed or needed.

4. Mathlib's `bernoulliPowerSeries` has coefficient $B_m/m!$ and satisfies
   $B(X)(\exp X-1)=X$. The reviewed proof rescales at $2i$ and $4i$,
   uses $\exp(4iX)=\exp(2iX)^2$, and cancels the nonzero series
   $\exp(2iX)-1$. Nonzeroness is proved from its first coefficient $2i$;
   the proof does not treat its zero constant coefficient as invertible.
   It obtains

   $$
   XT=B(2iX)-B(4iX)-iX.
   $$

5. Taking coefficient $m+1$ gives the stated Bernoulli coefficient for
   $m>0$, with the correction term $-iX$ absent precisely because
   $m+1\neq1$. The final specialization uses $m=2n-1>0$ and proves
   $m+1=2n$. Thus the Bernoulli index is $2n$, its factorial is $(2n)!$,
   and the derivative-to-coefficient factor is $(2n-1)!$.

6. The final assembly supplies the complex coefficient identity to the
   separately authored absolute-value algebra helper. Nonnegativity of
   the derivative comes from the earlier finite tree count, whose proof
   does not use Bernoulli numbers. There is consequently no circular use
   of the Bernoulli formula to establish its sign. The helper returns the
   absolute value of the real coercion of the rational $B_{2n}$, with
   exactly the factor $4^n(4^n-1)/(2n)$.

7. `source_fullyFrozen_card_formula` contains both source equalities and
   has only the positive-size hypothesis. The coefficient identity,
   analytic realization, growth equivalence and enumeration are proved
   dependencies, not extra hypotheses of this final statement.

This reconstructs the paper's externally cited tangent enumeration with
an explicit finite-growth proof plus formal Bernoulli-series algebra.
The audit checks the mathematical sequence identified in the source as
OEIS A000182 through its exact derivative and Bernoulli formulas; it does
not separately certify external OEIS database metadata.

The source review found no semantic mismatch. The imported-module direct
check of `TangentEnumerationStatements.lean` passes with
`autoImplicit=false`: nine independently reconstructed statements,
including the explicit boundary case $n=1$ with cardinality one, and
sixteen closure probes. Every probed closure contains exactly `propext`,
`Classical.choice` and `Quot.sound`. Evidence is retained in
`tangent-enumeration-statements.log`.

The later cosmetic proof change in `tangentExponential_square` was also
reviewed: it replaces a generic congruence/ring step by the explicit
complex scalar identity $2i+2i=4i$. No definition or theorem type changes.
Refreshed root artifact integration passes with 4,404 build jobs, and the
namespace-wide audit passes 5,972 standard-axiom closures. The independent
analytic and final-statement audit is complete. The complementary root
review is `TANGENT_COMBINATORICS_INDEPENDENT_AUDIT.md`. This scoped conclusion
does not assert complete coverage of the whole paper or a completed
publication candidate.
