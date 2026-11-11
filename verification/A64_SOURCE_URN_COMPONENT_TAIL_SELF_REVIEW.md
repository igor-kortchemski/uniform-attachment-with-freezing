# A64: actual component maximum through the infinite positive urn

This is the author's self-review, scoped to source lines 2016–2019 and
the A63 extension concentration inequality they use. The earlier finite
exponential-moment proof of L11 remains unchanged. This increment checks
the source infinite-urn route, with the existing S11 and S17 distinctions
retained explicitly. Root integration and independent review are separate
from this authored evidence.

## Exact scalar conversion

Let $a=C^k$, $b=C^{k+1}$, and let $K>0$ be the single constant from the
proved A63 source budgets. It controls the complete infinite square sum
$D=\delta_{a,b}$ and the finite maximum $E=\varepsilon_{a,b}$ by $K/a$.
The source cap $S_a\leq a+1$ is also supplied. For $a\geq1$, $k\geq1$,
and the genuine positive populations, `source_urn_exponent_lower` proves
the finite inequality

$$
\frac{k^2}{16K}
\leq
\frac{(k^4/4)S_a^{-1}}{D+k^2\max(D,E)}.
$$

Every denominator is proved positive. In particular, the actual infinite
square budget is positive because its first reciprocal-square term is
positive; no totalized $0/0$ convention is used. The factor $16$ is
explicit: $a+1\leq2a$ and $1+k^2\leq2k^2$ supply the two rounding
losses when converting the exact maximal exponent.

The initial reciprocal bound and the elementary population cap at $b$
give

$$
\frac{S_b}{S_a}\leq K(C+1).
$$

Thus the corrected marked-root deviation threshold obeys

$$
1+(1+k^2)\frac{S_b}{S_a}
\leq 1+(1+k^2)K(C+1)\leq k^3
$$

for every sufficiently large $k$, using one constant independent of the
block or component. The extra initial one is retained until this cubic
domination step. It is not silently dropped from the source's marked
count.

## Genuine endpoint concentration

`positiveExtension_urn_cubic_tail_le` applies the A63 infinite maximal
inequality at $t=k^2$, then transfers its bound to the actual finite urn
endpoint. It proves the tail for $U_b+1$, so it remains valid for the
source's marked-root component convention:

$$
\mathbb P(U_b+1>k^3)\leq2\exp\left(-\frac{k^2}{16K}\right).
$$

`positiveExtension_component_cubic_tail_le` pushes this result to the
actual tree continuation, conditional on any genuine lower-cut phase
state and any root active at that cut. The only probabilistic identity
used in the transfer is the already proved exact component-urn endpoint
law. A tail estimate or `HasPathLaws` is not assumed. A63 supplies the
canonical infinite urn and proves all of its finite path laws before
the maximal theorem is invoked.

`uniform_positiveExtension_component_parameters` constructs the common
$K$, the budget bounds, $k\geq1$, and the cubic marked-root threshold
from the literal source hypotheses. It does not put these estimates into
the final theorem as additional premises. The auxiliary eventual index
lemma uses $A_n\to\infty$ to force every permitted block index above
the one fixed scalar threshold. Consequently the final eventual horizon
works for every $k$ in the entire source window.

## Actual roots and the source union bound

`Forward.positiveExtension_continuation_maximum_tail_le` proves the
conditional union over the actual initial active set. Prefix preservation
shows that this set is exactly the terminal state's set of cut roots.
Taking the supremum over these roots therefore gives a genuine finite
union. Each root has the same verified upper bound; independence of
components is neither assumed nor used.

The number of roots is exactly the actual initial population, by the
phase-count identity. The subsequent past-state mixture gives the
literal source prefactor

$$
\mathbb P(M_{a,b}>k^3)
\leq S_a\,2\exp\left(-\frac{k^2}{16K}\right).
$$

The source count is independently retained as an almost-sure identity
of the actual terminal cut-root set with $S_a$. Roots which later froze
are still present in this cut-root set, and each is counted once in the
marked component. The union is not over a fictitious independent family
or an abstract number of components.

The pure scalar lemma
`eventually_geometric_exp_square_le_inv_sq` proves

$$
(C^k+1)\,2e^{-\beta k^2}\leq k^{-2}
$$

for every sufficiently large $k$ and every fixed $\beta>0$. It compares
the exponent $k\log C-\beta k^2$ with $-k$ and uses the installed limit
$k^2e^{-k}\to0$. Together with $S_a\leq a+1$, this closes the actual
source union bound.

## Exact final source statement and scope

`linear_geometric_componentMaximum_tail_via_positiveExtension` uses the
actual Algorithm 1 law at time $C^{k+1}$ and the existing
`Forward.componentMaximum`, including the marked-root convention. It
proves, with the literal near-origin limsup, bulk liminf, positive
diverging cutoff, and strict survival through the horizon,

$$
\text{eventually for every }n\text{ and every }k\text{ with }
A_n\leq C^k\leq n/C,
\qquad\mathbb P(M_k^n>k^3)\leq k^{-2}.
$$

The real upper cutoff is converted to the exact integer endpoint
$C^{k+1}\leq n$. Constants and eventual indices do not depend on $n$,
$k$, the lower-cut state, or the chosen component. The only result reused
from the older finite-moment-tail module is pure geometric cutoff
bookkeeping. Its finite moment/concentration estimates and its L11
conclusion are not called.

S17 remains a correction to the printed marked-root interpretation:
the source's direct urn identification is valid for true active counts,
while its marked count can be one larger. The new proof explicitly
absorbs that one before using the cubic threshold. S11 also remains:
the arbitrary-process formulation conditioning only on current occupancy
is not certified. The canonical urn used here has proved full path laws.
The corrected source route has no extra unproved concentration premise.

## Current evidence

The three frozen production modules have actual-file direct Lean PASS0
checks with no diagnostics:

- `SourceUrnComponentTailScalar`:
  a local log (not retained);
- `SourceUrnComponentTail`:
  a local log (not retained);
- `SourceUrnComponentMaximum`:
  a local log (not retained).

Separate parent artifact evidence is retained in
`verification/pair-coupling-source-urn-first-selection-build.log`
(PASS3868), `verification/source-urn-tail-first-selection-law-build.log`
(PASS3802), and `verification/source-urn-component-maximum-build.log`
(PASS3880).

The authored expanded probe is
`verification/A64SourceUrnComponentTailStatements.lean`: eight examples
and twelve axiom closures. It checks the finite scalar rate, the
marked-root component, the exact source-root prefactor, actual root
counts, the uniform urn-law bound, and the literal final source window
with the maximum fully expanded. Its fresh actual imported-file check
passed with exit code zero and no diagnostics in
a local log (not retained). Durable current
output is `verification/a64-source-urn-component-tail-author-statements.log`.
All twelve closures use only `propext`, `Classical.choice`, and
`Quot.sound`. The root independently reviewed the three modules and
source and reconstructed three examples/eight permitted closures in
`verification/a64-source-urn-independent-statements.log`; that independent
evidence is separate from this self-review. No obligation remains in the
corrected A64 route described here. A63's separately stronger joint
original-component-path identity is not inferred from these endpoint
and union results. Local proof checks are not final publication or
Palomar verification.
