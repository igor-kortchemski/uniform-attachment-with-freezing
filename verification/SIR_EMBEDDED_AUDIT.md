# Independent audit of the embedded SIR local conclusions

Date: 29 October 2026. Scope: T06.I–II and affected dependencies, source
`attachement-uniforme-1-final.tex`, lines 2023–2072, SHA-256
`88953dd87165a14b0e643c5b3d0075d8ce5ec39cdcfc0c25d313570fc3ab00df`.
This is a scoped statement review after implementation, not a declaration of
complete paper coverage. The source and whole-paper scope are unchanged.

The reviewed implementations are `MainSIREmbedded.lean`,
`SIRStrongLocalNonTightness.lean`, `MainSIRLocalLimit.lean` and their affected
count, infection-tree, sign-word, terminal-horizon, frozen-ball, recursive
root-degree and geometric-law interfaces. The independently reconstructed
statement examples are in `SIRLocalLimitStatements.lean`.

## Statement match

| Obligation | Reviewed formal conclusion | Finding |
| --- | --- | --- |
| T06.I | Under the exact source ratio $\lambda_n/(\lambda/n)\to1$, $\lambda>0$, the actual embedded terminal-tree probability measures converge weakly in the established local plane-tree topology to the concrete iid geometric Bienaymé law. | Pass for the constructed embedded model. No survival condition and no assumption $\lambda>1$ is added. The source Poisson-process identification is still open. |
| Geometric parameter | The attachment probability is $p=\lambda/(1+\lambda)$; Mathlib's `geometricMeasure` is supplied its complementary success parameter $1/(1+\lambda)$. | Pass. The statement probe expands the concrete iid offspring law and verifies the complement identity. |
| T06.II | Under the exact source ratio $\lambda_n/(1/n)\to\infty$, the embedded terminal-tree measures are not tight on the same local plane-tree carrier. | Pass for the constructed embedded model. The hypothesis is on $n\lambda_n$, with no monotonicity, survival or unscaled-rate divergence assumption. |
| Stronger degree conclusion | For every fixed $d\in\mathbb N$, the probability that terminal root offspring count is at most $d$ tends to zero. | Pass. The statement probe expands the actual full-path pushforward at $2n+1$, and also checks constant per-pair intensity one as an example. |
| Terminal object | `embeddedTerminalTreeLaw` reads the actual full infection-tree history at $2n+1$. | Pass. Actual absorption and holding the entire state at that horizon have been proved; replacing the random extinction horizon by this deterministic horizon is justified. Time $n$ is not substituted for the terminal object. |

The ratio-to-scaled-rate lemmas use only eventual positivity of the population
size and the source's positive limiting $\lambda$. A rate may be zero at any
finite collection of small population sizes. The underlying limiting theorem
also has a valid zero-limit boundary, without using a ratio with zero
denominator; the source-ratio wrapper retains $\lambda>0$.

The formal carrier is the already established canonical space of locally
finite rooted plane trees, with actual chronological child ordering. Root
degree is a continuous coordinate in that topology. No separate forgetful
map to another labelled or unlabelled tree carrier is proved by these new
exports. The root-degree obstruction is independent of child ordering, but
transferring it to another formal carrier still requires its matching degree
and topology interface.

## Dependency checks and paper arguments

1. `treeFullLaw` is a genuine measure constructed from the explicit finite
   infection/recovery kernel. Its active-set cardinality projects, along the
   entire path, to `countsFullLaw`. Those path identities are proved, not
   hypotheses of the advertised conclusions. The valid initial population is
   one infectious root plus $n$ susceptible individuals.
2. The zero-susceptible infection event has probability zero. The count and
   tree processes are held after infectious extinction. Legal transition
   invariants and the deterministic $2n+1$ absorption bound are used at the
   actual terminal horizon.
3. The finite-word comparison retains the actual adaptive infection
   probability $\lambda_n U/(1+\lambda_n U)$. Susceptible bounds give the
   general-rate fixed-prefix comparison. There is no silent replacement of
   $\lambda_n$ by $\lambda/n$.
4. In T06.I, finite-state event comparison is uniform over events for each
   fixed prefix. Actual frozen finite balls persist under all supported later
   updates. The cylinder-error inequality transfers the verified iid-sign
   limit to the finite-population terminal law, including paths with finite
   extinction. The concrete iid geometric offspring law is identified using
   the previously proved T02 interface.
5. In T06.II, every fixed early prefix approaches the genuine all-attachment
   recursive process. The root stays active in that process, and the proved
   bounded-degree estimate makes its root degree escape. Every supported SIR
   update preserves old vertices, so terminal root child count dominates any
   earlier prefix count. The graph-to-plane root-degree identity is proved
   from the actual parent and adjacency structure.
6. Compact subsets of the local plane-tree space have bounded root degree,
   by continuity of the degree map. The resulting degree escape contradicts
   tightness. This argument uses actual terminal laws and requires no
   subsequence selection or new Skorokhod realization.

These are proof departures from the printed proof. The T06.I proof uses
finite-prefix event bounds and persistent frozen balls instead of asserting
that the absorbed infectious count equals an unrestricted random walk after
hitting zero. That printed unrestricted-walk assertion is not certified.
The T06.II proof uses the stronger root-degree obstruction instead of the
printed Prokhorov/Skorokhod subsequence argument. The bypassed literal
arguments remain recorded in the source inventory; the new proofs do not
retroactively validate them.

## Physical process boundary

The source defines independent exponential infectious periods and independent
Poisson contacts between individual pairs. The new embedded kernel chooses an
active infector or recovering individual uniformly, and correctly realizes
attachment/freezing dynamics with that choice. Defining this kernel does not
prove that the independent continuous-time construction induces it.

The finite independent exponential-clock race results check a meaningful part
of A65: grouped clock minima and the rational event-type probabilities for
positive rates and nonempty infectious/contact families. They do not yet
prove uniform responsible-individual selection independent of event kind,
empty/zero-rate clock disabling, or the memoryless/thinning argument along the
entire epidemic history. Thus the physical infection-tree process in the
source is not yet identified with `treeFullLaw`; A65 and the physical part of
A66 remain open. T06.I–II should be reported as proved for the genuine embedded
model, with that bridge explicit, rather than as fully closed source results.

## Current proof evidence

- Root Lake builds succeeded for `MainSIREmbedded` and
  `SIRStrongLocalNonTightness`; see `main-sir-embedded-build.log` and
  `sir-strong-susceptible-build.log`.
- The independent statement probe passes the direct command
  `lake env lean -DautoImplicit=false verification/SIRLocalLimitStatements.lean`
  without diagnostics other than its requested axiom output. The retained
  evidence is `sir-local-limit-statements.log`.
- Twenty probed closures, including the actual kernels and full tree law,
  terminal absorption, finite-prefix mixtures, geometric local limit, both
  exact ratio wrappers and the stronger degree/non-tightness results, use
  only `propext`, `Classical.choice` and `Quot.sound`.

This scoped audit does not resolve the physical-process bridge, T07, generic
alternative tree carriers, unchecked bypassed paper arguments, or publication
validation. Those obligations remain in the full coverage record.
