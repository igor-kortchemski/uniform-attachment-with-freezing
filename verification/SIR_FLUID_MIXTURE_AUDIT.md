# Independent audit of the embedded T07.I.a fluid path limit

Reviewed source: `attachement-uniforme-1-final.tex`, lines 2080–2087.
Reviewed main modules: `MainSIRFluidMixture.lean`, `MainSIRFluid.lean`,
`SIRGeometricSurvivalPath.lean`, and `SIRPathSpace.lean`. The review also
checked the relevant exported interfaces and arguments in
`SIRStoppedFluidTransfer.lean`, `SIREarlyExtinction.lean`,
`PlaneFiniteExtinction.lean`, and the concrete geometric Bienaymé construction.

## Exact statement alignment

The source assumes $\lambda_n\sim\lambda/n$ with $\lambda>1$ and asserts weak
convergence of the entire stopped infectious-count path, for uniform
convergence on compact subsets of nonnegative time, to

$$
\left(\max\{2-2g_\lambda(t)-t,0\}\,\mathbf 1_A\right)_{t\geq0}.
$$

Here $A$ is one survival event of a Bienaymé process with geometric offspring
parameter $1/(1+\lambda)$. It is the same event at every observation time.

| Requirement | Implemented interface | Audit finding |
| --- | --- | --- |
| Literal source rate ratio | `embedded_sir_fluid_limit_of_source_ratio` | Exact ratio $\lambda_n/(\lambda/n)\to1$, with no rate monotonicity assumption. |
| Equivalent scaled rate | `embedded_sir_fluid_limit` | Assumes only $n\lambda_n\to\lambda$ and $\lambda>1$. The ratio wrapper proves the implication, ignoring only the irrelevant index $n=0$. |
| Actual stopped count law | `populationPathLaw` | Pushforward of the verified absorbing `countsFullLaw`; no unstopped count law is substituted. |
| Entire path carrier | `PopulationPath` | Contains all real-valued functions on nonnegative time, including the actual step paths. It is not restricted to continuous paths. |
| Required topology | `populationPath_tendsto_iff_on_compacts` | Exact equivalence with uniform convergence on every compact time set. |
| Exact floor-scaled path | `scaledPopulationPath_ae` | Simultaneously for all times, the encoded path equals $I^n_{\lfloor nt\rfloor}/n$ almost surely. |
| One shared random event | `geometricSurvivalPath` | The entire path is selected once from the positive profile or zero path according to one tree's survival. |
| Concrete Bienaymé survival | `geometricSurvivalPathLaw` | The source probability space is an actual iid offspring-field construction and pruning map, not an unnamed Bernoulli variable alone. |
| Derived survival weight | `geometric_sir_survival_real` and `countsFullLaw_early_survival_eventually` | The weight $1-1/\lambda$ is proved from the geometric tree and from the actual early stopped count process. It is not a premise of the main theorem. |

The source geometric convention agrees exactly: `geometricBienaymeLaw p`
uses `geometricMeasure (unitInterval.symm p)`, and
$p=\lambda/(1+\lambda)$ gives geometric parameter $1/(1+\lambda)$ on the
nonnegative integers. `FiniteVertices` refers to the complete Ulam–Harris
tree. Its proved equivalence with bounded height identifies its complement
with an arbitrarily deep, nonextinct tree.

## Path carrier, measurability and stopping

`PopulationPath` is the uniform-convergence-on-windows space for the compact
windows $[0,m]$, $m\in\mathbb N$. These windows cover nonnegative time, are
directed by inclusion, and contain every compact time set. The exported
topology equivalence therefore has precisely the source's local uniform
meaning. The theorem asserts weak convergence of probability measures on
that whole path space, not only marginal or finite-dimensional convergence.

The path encoding reads finitely many count coordinates through event
$2n+1$ and caps subsequent indices at that horizon. This is a measurability
construction, not a truncation of the asserted random path: the actual count
law is already proved absorbed and held by $2n+1$.
`scaledPopulationPath_ae` proves equality to the uncapped floor-indexed
stopped path for every nonnegative real time on one common full-measure set.
The finite-word domain is countable, so its map into the Borel path carrier
is measurable even though no separability of the space of all functions is
assumed.

## Mixture and proof arguments checked

The numeric mixture law is the pushforward of a Bernoulli law by the map
that chooses the complete positive profile or the complete zero path.
`MainSIRFluidMixture` compares bounded continuous tests on the whole path
carrier. Continuity at the two candidate paths gives one common compact
window and tolerance for each test. The two-stage stopped-fluid estimate
uses a single early gate $I^n_{\lfloor\delta n\rfloor}>0$ for the entire path
on that window. Its bad-event probability tends to zero, and the gate's
probability is independently proved close to $1-1/\lambda$.

The order of limits is retained: first $n\to\infty$ and then
$\delta\downarrow0$. For each test and error tolerance, the proof chooses
one sufficiently small fixed $\delta$ for both the fluid approximation and
the survival-weight estimate. It does not assume a survival estimate or
select a different Bernoulli event at each time. The bounded-test comparison
then yields weak path-law convergence.

`SIRGeometricSurvivalPath` takes the actual geometric Bienaymé tree and maps
it to the positive profile exactly on the event of infinitely many vertices.
The independently proved tree survival probability identifies this path law
with the numeric two-point mixture. `MainSIRFluid` rewrites the numeric limit
using that equality. No coupling between each finite epidemic and a fixed
limiting Bienaymé tree is claimed or needed for this weak-law statement.

The stopping transfer uses the actual coupled stopped marginal, and the
profile is cut off by the positive part after its first positive extinction
time. This addresses the stopped-at-zero issue identified in the earlier SIR
audit. It does not replace the stopped count by a natural-valued unstopped
chain or leave the shared gate as a theorem hypothesis.

## Verdict and remaining scope

No blocking statement mismatch was found for T07.I.a **for the explicit
embedded SIR count chain**. The statement has the source parameter,
unconditional law, one concrete shared survival event, actual stopped path
and full local uniform path topology.

The physical Poisson-contact epidemic identification A65 remains separate.
Until its finite-history bridge is proved, this audit does not certify that
the paper's independently constructed continuous-time epidemic has been
identified with this embedded law. It also does not certify T07.I.b,
T07.II, or a joint height/distance theorem.

`verification/SIRMainFluidStatements.lean` contains independent expanded
statement probes, including the literal source ratio, actual entire-path
topology, one shared geometric-tree event, derived survival weight, uncapped
stopped path values, and the concrete rate sequence $\lambda_n=2/n$.
Its actual-file direct command
`lake env lean -DautoImplicit=false verification/SIRMainFluidStatements.lean`
passes with no diagnostics, captured in a local log (not retained).
The independent axiom check is captured separately in
a local log (not retained); all five printed closures use only
`propext`, `Classical.choice`, and `Quot.sound`.
