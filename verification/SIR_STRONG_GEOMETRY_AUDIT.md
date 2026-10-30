# Independent review of strong-regime SIR geometry

Date: 29 October 2026. Source: `attachement-uniforme-1-final.tex`, lines
2095–2104 and 2241–2330, SHA-256
`88953dd87165a14b0e643c5b3d0075d8ce5ec39cdcfc0c25d313570fc3ab00df`.
This scoped milestone review reuses the unchanged paper inventory. The
reviewer did not implement the random-environment transfer or the terminal
maximum proof. The plane graph transport, implemented by this reviewer, is
identified separately below.

## Reconstructed conclusion

Under the sole rate hypothesis $n\lambda_n\to\infty$, the actual stopped
embedded infection tree satisfies, for every $\varepsilon>0$,

$$
\Pr\left(\left|\frac{\operatorname{Height}(\mathscr T^n)}{\log n}-e\right|
\ge\varepsilon\right)\longrightarrow0.
$$

The exact-type probe in `SIRStrongGeometryStatements.lean` expands the law as
`CountableMarkovChain.fullLaw (treeKernel (rate n)) (initialTreeState n)`.
The observation is the maximum address length over all terminal vertices
at event $2n+1$. `SIRAbsorption` proves this horizon is terminal and the whole
state is held afterwards. The valid plane support has exactly the present
Ulam–Harris addresses, so this maximum is the tree height. Frozen vertices
are retained. The source ratio $\lambda_n/(1/n)\to\infty$ is checked, as is
the constant per-pair rate one. No survival condition, monotonicity of rates,
or assumed estimate is added to the theorem.

The same probe checks the actual uniform-vertex height and conditional
independent-pair distance at both time $n$ and the terminal time $2n+1$,
with limits $1$ and $2$. The time-$n$ conclusions are intermediate results;
the terminal statements separately reconstruct the exact T07.II.b sampling
conclusions. The pair law draws both vertices from the same tree, includes
its frozen vertices and the diagonal, and uses the parent graph's distance.

## Dependencies and proof correspondence

The changed dependencies reviewed are the complete count-prefix transport,
the deterministic profile uniformization and averaging, the chronological
observations, the late attachment charge, the forward cut maximum, and the
terminal-prefix marginal identity.

The profile transfer does not assume that deterministic asymptotics hold
uniformly over arbitrary schedules. It proves the required finite uniform
criterion by contradiction: insert increasingly accurate bad rows at
distinct observation indices and fill the remaining rows with a verified
balanced schedule. This gives one admissible triangular array to which T04
applies. The actual adaptive word law then averages a bounded conditional
error probability. Its bad-word probability is controlled by the proved
full count-prefix projection and relative startup estimates down to
$\lceil\log\log n\rceil$. No independence of adaptive infection signs is
assumed. The height factor at $c=1$ is exactly one, the distance factor is
two, and the maximum factor is $e$.

The chronological vertex map is bijective on the actual support. Its height
identity and the independent conditional uniform laws are inspected in the
implementation. The separate `ForwardPlaneDistance` graph transport maps
walks both ways and therefore preserves distances. That bridge received
self-review here, not an independent authorship claim.

For the late phase, a true forward harmonic potential bounds the expected
future reciprocal population cost and actual pre-birth attachment charge.
The small infection-probability restriction is measurable at the starting
time; the future is integrated by its proved conditional Markov law. This
avoids conditioning on a future extinction event. The full post-$n$ charge
is $o(\log n)$ in probability. The word-to-count comparison uses the
transition from $j$ to $j+1$, with the matching post-birth reciprocal bounded
by the pre-birth charge. Only steps before the actual first zero enter.

The cut-height exponential estimate applies through the extinction step,
including equality at extinction. Words extinct before the cut have zero
cut height. Averaging its tail against the genuine terminal adaptive word
law proves the maximum extra height above time $n$ is $o(\log n)$.
The deterministic lower and upper bounds are the earlier truncated maximum
and that maximum plus the cut maximum. The exact truncated-maximum marginal
uses longer-word projectivity and explicitly handles extinction before the
cut. The final union bound combines this with the actual time-$n$ maximum.

For terminal sampling, the proof compares the true conditional uniform
measures along the same original forward history. Old vertices retain their
heights and distances. The difference of event probabilities is at most
the removed vertex fraction for one sample and twice that fraction for two
independent samples. Exact feasible-word count identities bound the fraction
added after time $n$ by $2\delta$ when $U_n\le\delta n$. The actual
probability of the complementary word event tends to zero. Averaging the
comparison costs at most $4\delta$; then $\delta$ decreases to zero. Exact
longer-word projectivity identifies the earlier observations with the true
time-$n$ laws. No equality of joint laws is inferred from separate marginals.

This verifies all three T07.II.b conclusions for the embedded model. The
source's reversed-walk domination and shifted reciprocal identity remain
unchecked obligations. The forward exponential-sum argument replaces the
printed conditional Bennett argument. Proving the conclusion by this route
does not certify those manuscript arguments.

## Evidence and remaining scope

`verification/main-sir-strong-maximum-build.log` passes the affected 4,174-job
Lake target. The expanded default build passes 4,271 jobs, and the global
axiom audit checks all 4,695 namespace declarations. The independent command
`lake env lean -DautoImplicit=false verification/SIRStrongGeometryStatements.lean`
passes. Its retained log, `sir-strong-geometry-statements.log`, contains the
seventeen requested axiom closures; each uses only `propext`,
`Classical.choice`, and `Quot.sound`.

The physical static independent exponential-clock/Poisson-process history
identification remains open. Finite-rate geometric height/distance mixtures
and every other unresolved inventory row remain
separate obligations at this review milestone. No whole-paper completion,
Comparator pass, independent kernel replay or Palomar acceptance is claimed.
