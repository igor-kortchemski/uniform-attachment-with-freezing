# A36: uniform maximum tail and the source moment method

This is the implementing reviewer's self-review of `MaximumUniformTail`,
`TailIntegralSeven` and `MaximumTailMoments`, for source lines 1279–1285.
The existing T03 statement and its original proof have separate independent
review; that review is not relabelled as independent review of this new route.

The actual tree maximum is used throughout. The finite Chernoff estimate
retains both the true vertex-count factor and the child's extra edge:

$$
\mathbb P(H_n/h_n^+\ge C)
\le\exp\!\left(\log(n+1)+\log C-h_n^+g(C-1)\right).
$$

This does not assert the false finite P03 upper bound. A single explicit
constant $K=1+7/g(1)$ satisfies $\log C\le K g(C-1)$ for all $C\ge2$.
For $2\le C\le8$, monotonicity gives $g(C-1)\ge g(1)>0$; for $C\ge8$,
the proved threshold comparison gives $g(C-1)\ge C-1\ge\log C$.

Height-scale divergence and $\log n/h_n^+\to0$ imply, eventually,
$h_n^+\ge4K$ and $\log(n+1)\le h_n^+g(1)/4$. These same two conditions
work for every $C\ge2$, proving the source's exact half-rate bound, even
with a closed threshold. The rank is selected before quantifying $C$.

For $u>7$, nonnegativity of the maximum means
$|H_n/h_n^+-1|\ge u$ forces $H_n/h_n^+\ge u+1$. Once $h_n^+\ge1$, the
uniform bound is therefore at most $e^{-g(u)/2}$. The generic real layer-cake
helper splits the moment at 7 and gives the constant

$$
7^p+p\int_7^\infty e^{-g(u)/2}u^{p-1}\,du.
$$

It is finite and depends only on the real exponent $p\ge1$. Actual moment
integrability is proved separately from finite height $H_n\le n$; it is
not inferred by totalizing a divergent integral. The higher-moment bound
at $p+1$, probability convergence and Hölder/truncation then prove the
actual all-real-$p$ maximum limit. No earlier MGF moment bound is assumed.

This checks the source's uniform-threshold assertion and its tail-integral
moment method. The finite correction is absorbed explicitly instead of
using the false printed finite P03 bound. The source's phrase “same method
as (I)” now has an actual maximum-law consumer; A34's separately recorded
logarithmic-envelope departure remains unchanged.

Focused builds pass in `forest-population-uniform-tail-build.log`,
`tail-integral-seven-build.log` and `maximum-tail-moments-build.log`.
`A36MaximumTailStatements.lean` checks three expanded source statements,
including the literal strict tail and its quantifier order, with eight
closures using only `propext`, `Classical.choice`, and `Quot.sound`; output
is in `a36-maximum-tail-statements.log`. Full integration is recorded in
the main report separately.
