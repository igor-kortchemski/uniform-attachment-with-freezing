# A63 positive extension: independent scoped audit

This independent review reads source lines 2011–2015 and the frozen
`ForwardPositiveExtension`, `SignedUrnPositiveExtension`,
`SignedUrnPositiveExtensionPath`, `SignedUrnPositiveExtensionBounds`, and
`SignedUrnPositiveExtensionMaximal`. The reviewer did not author these
modules. Relevant definitions and consumers in `SignedUrnInfinite`,
`ForwardComponentPopulation`, and `ForwardComponentContinuation` were
also inspected. This audit is separate from the implementing notes in
`POSITIVE_EXTENSION_PROOF_NOTES.md`.

## Source content reconstructed

For a finite block from $a=C^k$ to $b=C^{k+1}$, the source starts the urn
at $U_0=1$, takes its initial population to be $S_a$, retains every signed
population increment through $b-a$, and then continues with positive
increments. Its two concentration budgets are

$$
\delta_{a,b}=
\sum_{a<i\leq b}\frac{1}{S_i^2}
+\sum_{j\geq1}\frac{1}{(S_b+j)^2},
\qquad
\varepsilon_{a,b}=\max_{a<i\leq b}\frac{1}{S_i}.
$$

It applies the infinite urn maximal inequality with $t=k^2$ to bound the
finite endpoint, then asserts uniform bounds of order $C^{-k}$ for the
initial reciprocal and both budgets in the window
$A_n\leq C^k\leq n/C$. The following scalar conversion and union bound
at lines 2016–2019 belong to A64, not this review.

## The actual retained process and the canonical urn

`positiveExtension x b` retains every original sign through $b$ and sets
every later sign to positive. The population agrees with the original at
every retained time, and satisfies $S^{\mathrm{ext}}_{b+j}=S_b+j$.
Positivity through $b$ proves positivity of the extension at every time.

The preservation result is stronger than equality of endpoint laws:
`Forward.fullLaw_prefix_positiveExtension` proves equality of the complete
joint tree-history prefix laws on all times $0,\ldots,b$. Actual tree
continuation laws through the retained endpoint are also unchanged.
Thus the extension does not silently resample or replace the original
finite tree process.

The shifted population is exactly
$Z_i=S^{\mathrm{ext}}_{a+i}$, with $Z_0=S_a$ and
$Z_{b-a+j}=S_b+j$. All its increments are proved to be the original
signed increments before the cutoff and $+1$ afterwards. This is not
an assumed sequence of approximate populations.

The infinite urn law is constructed by Ionescu–Tulcea from the genuine
signed-urn transition kernels. `urn_traj_map_record` proves its complete
finite record law by induction, using prefix preservation and the first
new transition. `infiniteUrnLaw_hasPathLaws` is therefore a conclusion,
not a concentration hypothesis inserted into the final result. The
constructed occupancies are simultaneously nonnegative integers bounded
by the positive population at every time. In particular, totalized
kernel behaviour on invalid occupancies is not used in this application.

The original finite component is identified at its endpoint by exact
pushforward of the actual tree continuation, conditional on any genuine
phase state and any root active at the lower cut. Its initial true
component population is one. That endpoint law equals the endpoint law
of the constructed infinite urn. This is sufficient to transfer the
maximal bound to the actual original component without a path-law
assumption or an assumed probability estimate.

The scope distinction is retained: complete tree-prefix preservation and
complete canonical-urn path laws are proved separately. The final
application uses exact component endpoint equality. These declarations
do not separately export equality of the entire original component
occupancy path with the canonical urn path, and this audit does not
infer such a joint identity merely from endpoint marginals.

Subsequently the reviewer authored the separate
`ForwardComponentUrnPath`/`Infinite`/`Positive`/`Maximal` bridge, proving
the complete actual component record laws and their positive-extension
`HasPathLaws` directly from the original tree kernels. That later work
is documented in `A63_JOINT_COMPONENT_PATH_SELF_REVIEW.md` and has a
separate parent-coordinated independent review. It closes the additional
joint-process obligation without changing the scope or provenance of
the present independent endpoint audit.

## Exact budgets and concentration constants

`positiveExtension_square_budget_eq` gives exactly the displayed
$\delta_{a,b}$. The finite sum uses $(a,b]$: $S_a$ is excluded and $S_b$
is included. The infinite part begins at $S_b+1$, so the boundary is
neither duplicated nor omitted. The tail is proved summable and at most
$1/S_b$ by an explicit reciprocal telescoping inequality for every finite
partial sum. There is no extra summability premise in the final source
application.

For $a<b$, `positiveExtension_maximum_eq_sourceEpsilon` proves that the
maximum reciprocal on the whole infinite extension is exactly the
source's finite maximum. The finite block already contains $S_b$, and
the later reciprocals are at most $1/S_b$. The proof establishes both
directions, with a nonempty finite maximum and positive bounded
reciprocals; it does not rely on an arbitrary value of an unbounded
real supremum.

`positiveExtension_infinite_maximal` applies the already verified
Markov-path urn inequality to the constructed law and supplies every
required hypothesis. The probability event is the infinite-time
deviation at some $i\geq1$, the threshold is $t/S_a$, and the exponential
bound has exactly the source numerator $(t^2/4)/S_a$ and denominator
$\delta+t\max(\delta,\varepsilon)$. The finite endpoint's upper
deviation is a subset of this absolute-deviation event. Specializing
$t=k^2$ retains the printed $k^4/4$ numerator.

## Actual active counts and marked roots

`componentPopulation` counts genuinely active descendants in the actual
component, including a distinguished root only while that root is active.
This true count is the urn occupancy. The source permanently treats its
marked root as active even after freezing. That marked count is the
cardinality of the actual active-descendant set with the root inserted.
It is at most the true count plus one.

The final actual-process result retains this correction explicitly:
the marked-component threshold is
$1+(1+t)S_b/S_a$, rather than $(1+t)S_b/S_a$. No declaration asserts that
the marked count follows the urn. S17 therefore remains correctly
recorded; the uncorrected marked interpretation of the printed endpoint
display is not certified. The true active-count version of that display
is proved exactly.

## Uniform source window and quantifier order

`linear_positiveExtension_source_budgets` takes the literal near-origin
limsup, bulk liminf, positive diverging cutoff, and survival through the
original horizon. It derives the needed linear population lower bound;
that bound is not added as a final source premise. The real upper
window condition $C^k\leq n/C$ is converted to the exact integer endpoint
$C^{k+1}\leq n$. For $C\geq2$, the finite interval is strictly nonempty.

One positive constant $K$ works for every sufficiently large $n$ and
every $k$ in the entire displayed window. It controls $1/S_{C^k}$,
$\varepsilon_{C^k,C^{k+1}}$, and the complete infinite
$\delta_{C^k,C^{k+1}}$ by $K/C^k$. It also proves the source cap
$S_{C^k}\leq C^k+1$. Neither $K$ nor the eventual horizon is chosen
separately for each block or component. The independent probe expands
the finite maximum and both pieces of the infinite square sum in this
uniform conclusion, rather than checking only their opaque aliases.

## Verdict and retained scope

No hidden estimate, unproved `HasPathLaws`, index shift, normalization
mismatch, or uniformity loss was found in the reviewed A63 conclusions.
The positive infinite-extension argument is now implemented with a
genuine urn law, exact original endpoint transfer, and the source's
explicit budgets. It is not merely a relabelling of the earlier finite
moment route.

The separate S11 remains: these results do not show that a completely
arbitrary process conditioned only on its current occupancy satisfies the
same maximal theorem. The constructed process has the stronger full
Markov path laws, as proved. The original marked-root formula needs its
already recorded correction. A64's subsequent scalar conversion and
forest union bound are outside this audit. No full-paper or publication
verdict is implied.

## Current proof evidence

The exact imported dependency chain through
`SignedUrnPositiveExtensionMaximal` has parent artifact PASS4142 in
`verification/ambient-positive-urn-poisson-reverse-build.log`.
The independent expanded probe is
`verification/A63PositiveExtensionIndependentStatements.lean`: ten
examples and sixteen axiom closures, including full tree-prefix law,
genuine full urn path law, original endpoint, expanded delta and epsilon,
infinite concentration, the marked-root $+1$ at $t=k^2$, and the literal
uniform source window. Its fresh actual-file direct check passed with
exit code zero and no diagnostics in
`/tmp/a63-positive-extension-independent-statements2.log`. The durable
output is `verification/a63-positive-extension-independent-statements.log`.
All sixteen closures use only `propext`, `Classical.choice`, and
`Quot.sound`. The implementing source-only check is not substituted for
this imported-file review.
