# Independent review of the source contact protocol and limit transfers

Date: 29 October 2026. Source: `attachement-uniforme-1-final.tex`, lines
2026–2046 and the statements at 2047–2104, unchanged SHA-256
`88953dd87165a14b0e643c5b3d0075d8ce5ec39cdcfc0c25d313570fc3ab00df`.
The reviewer authored none of the physical clock, Poisson or transfer
modules. This review reuses the independently checked embedded main-result
interfaces and the unchanged source inventory.

The inputs are independent recovery lifetimes and entire directed contact
paths, indexed by each source's infection age. A contact path is represented
by its positive strictly increasing divergent arrival sequence. Its count
is proved to count exactly the points at or before the observation time,
and its first coordinate is the actual first positive-count time. Poisson
counting marginals imply the exponential first-delay law; an exponential
contact law is not assumed. Coordinate maps preserve the source's joint
independence, including independence from recovery periods.

The static construction samples one original finite clock array. Its full
event history and conditional residual product are proved by induction on
finite event words, retaining untouched coordinates for individuals not yet
infected. The reference word process and the original array have equal
whole-history laws. Exact source/recipient sums and the bijection from
active individual labels to tree addresses identify the existing tree
kernel. The proof does not assume an embedded transition law or conditional
memorylessness after an arbitrary history.

`poissonFullContactRun` is a separate deterministic protocol that consults
the next point of each whole live contact path at the current infection age.
Recovery delays remain the original lifetimes. The future-live-clock
invariant proves its entire frame history equals the static-array history
on positive delays. Positivity follows almost surely from the proved joint
array law. Loss of susceptibility is permanent; recovered individuals stay
removed. This justifies discarding contacts that cannot infect and counting
only infection/recovery events as in the source. Absolute event time is the
source infection time plus its fixed delay. The formalization uses the
source-age contact construction; it does not assert an additional calendar-
time strong Markov theorem.

The resulting equalities concern the complete genealogy, the literal
susceptible/infectious label counts, absorption of the entire frame by
$2n+1$, and the terminal tree law. `SIRPoissonStatements.lean` reconstructs
the actual next-point tree/count/terminal statements with the process
marginals expanded. Its twelve axiom closures use only `propext`,
`Classical.choice` and `Quot.sound`.

`PoissonSIRData` bundles exactly measurable independent process coordinates,
rate-one recovery laws and Poisson counting marginals. There is no estimate,
survival assumption or desired history-law identity inside the bundle.
`SIRPhysicalLimits` and `SIRPhysicalFiniteLimits` supply the proved law
identities internally. Source data is required only eventually, and the
source rate asymptotics imply eventual positive intensity. The transfers
therefore impose no uniform positivity, rate monotonicity or restriction
on finitely many initial indices. Local non-tightness transfers through
bounded-degree escape rather than an unjustified inference about changing
finitely many measures.

Terminal uniform laws bind the actual whole physical tree law with its
all-vertex sampling kernel. The distance kernel draws two independent
vertices conditional on that same tree, including the diagonal and frozen
vertices. Normalization is exactly by $\log n$. The finite-rate weak targets
use the same concrete geometric Bienaymé survival event as the embedded
limits. The path carrier's simultaneous uncapped stopped-path identity is
also supplied, so the fluid transfer concerns all nonnegative real times.

`SIRPhysicalSourceStatements.lean` independently expands the source-data
bundle and reconstructs representative local, fluid, finite-rate sampling,
non-tightness and maximum conclusions. Reused embedded fidelity findings
are in `SIR_EMBEDDED_AUDIT.md`, `SIR_FLUID_MIXTURE_AUDIT.md`,
`SIR_STRONG_GEOMETRY_AUDIT.md` and `SIR_FINITE_MAIN_WEAK_AUDIT.md`. The last
review explicitly separates its author's geometric inputs from the final
weak assembly independently reviewed there.

The standalone rate-zero model requires a no-arrival carrier and is still
separate. Existence of the supplied Poisson process law is not constructed;
it is source input, rather than an extra convergence premise. No whole-paper
coverage, successful Comparator or official Palomar verification is claimed.
