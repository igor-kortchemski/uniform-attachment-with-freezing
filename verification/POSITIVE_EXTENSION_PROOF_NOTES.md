# The positive infinite extension in A63

This authored source correspondence concerns manuscript lines 2011–2015.
It is a continuation of the forest/conditional-moment work, with separate
verification provenance. Independent review and release build evidence must
be recorded separately.

## Exact construction and original process

`ForwardPositiveExtension.positiveExtension` retains every original sign
through the finite endpoint $b$, then uses only positive signs. Its population
agrees with the original $S_i$ for $i\le b$ and satisfies

$$
S^{\mathrm{ext}}_{b+j}=S_b+j.
$$

Under positivity of the retained finite schedule, the extension is positive
at every time and has infinite extinction time. The complete finite-history
law of the original process is unchanged, not merely a population marginal.
Actual finite continuation laws are unchanged as well. A root active at the
lower cut starts its genuine descendant-component urn with one ball.

`SignedUrnPositiveExtension` shifts time by $a$. It identifies the source
initial population $S_a$, every retained signed increment through $b-a$, and
the subsequent all-positive increments. Its original component endpoint law
is proved to be the corresponding shifted urn law.

## Infinite urn and actual path-law evidence

`SignedUrnPositiveExtensionPath` constructs an infinite integer process by
Ionescu–Tulcea using the signed urn's actual two-point kernels. Its complete
record over every finite interval has exactly `SignedUrn.pathLaw`.
The proof splits the genuine trajectory law at the first new transition,
uses prefix preservation, then inducts on the record length.

The resulting `HasPathLaws` is a proved conclusion. It is not assumed when
the concentration estimate is applied. The endpoint marginal is also proved
to equal the finite urn continuation. Under the source positive population
and signed increments, every occupancy is a nonnegative integer no larger
than the population, simultaneously at every time.

`SignedUrnPositiveExtensionMaximal` applies the existing checked maximal
theorem to this constructed process. It then identifies the original finite
urn endpoint, and finally the component in the actual original tree
continuation. No hypothetical independent component family or path-law
premise occurs in those final source consumers.

The separate S11 issue remains: these results do not prove that the weaker
paper wording conditioning only on the current occupancy is sufficient for
an arbitrary process. This constructed process has the genuine Markov path
law, which is what the verified concentration theorem uses.

## Exact delta and epsilon

The complete infinite square budget is proved to equal

$$
\delta_{a,b}=
\sum_{a<i\le b}\frac{1}{S_i^2}
+\sum_{j\ge1}\frac{1}{(S_b+j)^2}.
$$

The positive tail is summable and at most $1/S_b$. This is proved by a direct
reciprocal telescoping inequality, including all finite partial sums.
For $a<b$, the maximum reciprocal of the infinite extension is exactly

$$
\varepsilon_{a,b}=\max_{a<i\le b}\frac{1}{S_i}.
$$

The positive tail cannot increase this maximum, because the finite interval
already includes $S_b$. No unproved tail-max or summability estimate is
inserted into the source concentration display.

`SignedUrnPositiveExtensionBounds.linear_positiveExtension_source_budgets`
uses the literal near-origin limsup and bulk liminf hypotheses, the original
diverging cutoff, and strict survival through the source horizon. In the
exact geometric window it gives one constant $K>0$ such that the initial
reciprocal, epsilon and delta are all at most $K/C^k$. It also retains the
true initial-root population cap $S_{C^k}\le C^k+1$.

## Marked roots and retained scope

S17 is preserved. The genuine active descendant count is the urn occupancy.
The source permanently marks each distinguished root as active even after
its freezing, so its displayed component count is at most the true count
plus one. The final actual-tree tail theorem includes this extra one in the
threshold. It does not assert that the marked count itself follows the urn.

The original true-component version of the display at line 2014 is checked
for every nonnegative deviation parameter, including $t=k^2$. Its marked-root
version has the explicit extra one. The later scalar conversion and union
bound at lines 2016–2019 remain a separate source-route obligation (A64);
the previously proved L11 endpoint-moment alternative is not being relabelled
as a check of those later paper steps.

## Current proof evidence and remaining release checks

- `ForwardPositiveExtension` and `SignedUrnPositiveExtension` have clean direct
  Lean checks, with logs in `verification/forward-positive-extension-direct.log`
  and `verification/signed-urn-positive-extension-direct.log`.
- `SignedUrnPositiveExtensionPath` has a clean direct Lean check in
  `verification/signed-urn-positive-extension-path-direct.log`.
- The Bounds and Maximal modules, together with all these source definitions,
  pass a combined source-only Lean check with no diagnostic. This respects
  the single-root rule for all artifact-writing builds.
- `verification/PositiveExtensionStatements.lean` reconstructs seven expanded
  source interfaces and queries twenty-one proof closures. The reproducible
  source-only check passes. One closure is axiom-free; the others use only
  `propext`, `Classical.choice` and `Quot.sound`.
- Run `python3 verification/check_positive_extension_sources.py` to reproduce
  that kernel check without writing an olean. Exact source hashes are recorded
  in `verification/positive-extension-source-snapshot.json`; diagnostics and
  closure output are in `verification/positive-extension-source-statements.log`.

The root agent became unavailable at model capacity before generating the
last dependency artifacts. Separate-module artifact/import verification,
global integration, and independent review of this A63 increment remain
pending. A future root-controlled build should target
`Freezing1.SignedUrnPositiveExtensionMaximal`, then check the ordinary expanded
probe and refresh the project's global coverage and axiom audits. This source
evidence alone does not certify a GitHub publication candidate or Palomar
deposit, and no whole-paper coverage claim is made.
