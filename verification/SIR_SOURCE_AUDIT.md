# Independent SIR source and interface audit

Date: 29 October 2026. Source: `attachement-uniforme-1-final.tex`, lines
2023–2330, SHA-256
`88953dd87165a14b0e643c5b3d0075d8ce5ec39cdcfc0c25d313570fc3ab00df`.
This review applies the local statement-audit and architecture skills. It is
independent of the new count/tree kernel implementation. The manuscript and
the declared whole-paper scope are unchanged, so the existing inventory is
reused; A65–A87 remain obligations until actual proved exports cover them.

## Exact main targets

| Source result | Premises and limit | Required meaning |
| --- | --- | --- |
| T06.I, lines 2047–2054 | Nonnegative rates with $n\lambda_n\to\lambda$, $\lambda>0$. The complete terminal infection tree converges locally in law to the geometric Bienaymé tree with offspring mass $\frac1{1+\lambda}(\frac\lambda{1+\lambda})^k$. | Use the actual epidemic tree, including finite extinction. The tree at deterministic time $n$ is not the advertised terminal object. |
| T06.II, same theorem | $n\lambda_n\to\infty$. The terminal-tree laws are not tight in the locally finite local topology. | The hypothesis does not require $\lambda_n\to\infty$. Non-tightness must refer to the same tree space as the claimed local convergence. |
| T07.I.a, lines 2080–2087 | $n\lambda_n\to\lambda>1$. On the uniform-on-compacts path topology, $I^n_{\lfloor nt\rfloor}/n$ converges in law to $\max(2-2g_\lambda(t)-t,0)\mathbf1_A$. | One shared event $A$ is survival of the geometric Bienaymé process of mean $\lambda$; its extinction probability is $1/\lambda$. Both that probability and its relation to the concrete tree construction require proofs. |
| T07.I.b | Same premise and shared $A$. Terminal-tree uniform height divided by $\log n$ has limit $\lambda/(\lambda-1)\mathbf1_A$; independent conditional uniform-pair distance has limit $2\lambda/(\lambda-1)\mathbf1_A$. | Uniform over all terminal vertices, with two samples independent conditional on the same random tree. They are not independent unconditionally. |
| T07.II.a, lines 2095–2101 | $n\lambda_n\to\infty$. $I^n_{\lfloor nt\rfloor}/n$ converges in probability uniformly on $[0,2]$ to $\min(t,2-t)$. | Uniform path convergence is stronger than convergence of finitely many coordinates. The stopped process remains zero after extinction. |
| T07.II.b | Same strong-infection premise. Terminal uniform height, conditional independent-pair distance and maximum height, divided by $\log n$, tend in probability to $1$, $2$ and $e$. | The maximum result requires control after time $n$; it does not follow merely from the time-$n$ height theorem. |

The parameters $n\lambda_n\to\lambda$ and $n\lambda_n\to\infty$ are convenient
exact replacements for the source asymptotic notation. Rates should be
nonnegative from the definition of a Poisson intensity. Positivity for every
small population size need not be added to the asymptotic theorems.

The approximating infectious paths are step functions. A space of continuous
functions would exclude those approximants. A formal statement must use a
path carrier admitting those functions with the topology of uniform
convergence on compact intervals, or an equivalent explicit supremum-norm
convergence statement. Product topology alone would weaken T07.

## Actual embedded dynamics and stopping

For $u$ susceptible and $i>0$ infectious individuals, the active clocks have
total infection rate $\lambda_nui$ and recovery rate $i$. Their event-type
probabilities are therefore $\lambda_nu/(1+\lambda_nu)$ and
$1/(1+\lambda_nu)$. Conditional on either event type, the responsible
infectious individual is uniform among the $i$ infectious individuals; in
an infection, the recipient is uniform among the $u$ susceptible individuals.
The independence and memorylessness argument yielding these statements is
part of A65, not a consequence of defining a Markov kernel with those weights.
Repeated contacts with already infected/removed individuals do not count as
steps and need to be excluded or thinned correctly in that bridge.

The stopped count chain has natural-number coordinates and is held once
$I=0$. Its complete path is not an unrestricted nearest-neighbour random
walk. The literal unrestricted-walk convergence at lines 2058–2070 is false
after a limiting path hits zero. Valid repair routes are:

1. Couple the stopped count chain with the simple walk stopped at zero.
2. Couple potential signs before absorption, and compare the actual trees only
   along legal nonabsorbed portions; treat finite extinction explicitly.

No failure of T06.I follows from that proof defect. If the limit walk becomes
extinct at a finite time, an exact prefix coupling through that time gives
an exact equality of the absorbed terminal trees. On surviving paths, the
proved frozen-ball stability can control every later horizon, including the
random SIR terminal horizon.

The finite population starts with $n+1$ individuals. There are at most $n$
infection events and $n+1$ recoveries, so the stopped history is absorbed by
step $2n+1$. Thus the actual terminal tree can equivalently be read at this
deterministic horizon, after proving the absorption and tree-holding laws.
Reading the tree merely at time $n$ would miss the second half of a major
epidemic.

The auxiliary unstopped infectious count must be integer-valued. While its
susceptible coordinate remains nonnegative, recoveries after hitting zero make
the unstopped infectious count negative. A natural-number subtraction would
silently absorb or truncate it and invalidate the source identity
$\widetilde I_k=2(n-\widetilde U_k)-k+1$. The stopped identity instead uses the
stopped clock, or is restricted to the pre-extinction interval.

The current `SIRCounts.lean` interface was read without modifying it.
`Counts.LegalNext` correctly describes infection/recovery before absorption
and holding after absorption. The zero-susceptible infection guard in
`countsStep` is a legitimate totalization only because the future stochastic
kernel must prove zero probability of that impossible infection.
`Counts.Valid`, susceptible bounds, potential decrement and absorption by
$2n+1$ are genuine structural invariants. The current positive-infectious
count identity must not be applied at extinction without an additional final
recovery or stopped-clock argument.

## Source proof defects and corrections

### S18 — the printed global-maximum drift criterion is false

At lines 2162–2176, the asserted implication uses the maximum over the entire
future horizon on the right of the drift inequality. Adding the missing
initial-value assumption noted in S13 is insufficient to repair it.

Take the deterministic family $X^n_k=k$, horizon $t=1$ and constant $C=1$.
It starts at zero. Every increment is $1$ and its squared increment is $1$.
The printed bound holds for every $n\ge1$ and $k\le n$ because

$$
1\le\frac{1+\max_{0\le j\le n}|X^n_j|}{n}=\frac{1+n}{n}.
$$

Nevertheless,

$$
\frac{\max_{0\le k\le n}|X^n_k|}{n}=1,
$$

so the advertised convergence to zero fails. The numerical deterministic
specialization is formalized in `Freezing1/SIRSourceChecks.lean`; it does not
assert unproved conditional-expectation identities. A corrected stochastic
Grönwall statement needs an adapted/current-time bound such as a maximum over
$j\le k$, an initial error tending to zero after division by $n$, and a
parameter-perturbation term for $n\lambda_n-\lambda$. The actual Lipschitz
drift calculation is capable of supplying that stronger local bound, so this
does not refute the stated fluid-limit theorem.

### S19 — hitting zero is different from reaching negative integers

The extinction argument at line 2158 changes from reaching zero to reaching
the negative integers for an ordinary walk starting at one. For attachment
probability $p=\lambda/(1+\lambda)$ with $\lambda>1$, the probability of
hitting zero is $1/\lambda$, while hitting $-1$ has probability
$1/\lambda^2$. Only the first equals the geometric Bienaymé extinction
probability. The source event should be hitting zero/nonpositive integers.
The displayed earlier probabilities $\Pr(Y_1=1)$ for a walk starting at one
with increments $\pm1$ also need their existing indexing correction: use
$\Pr(Y_1-Y_0=1)$ or $\Pr(Y_1=2)$.

These walk hitting-probability formulas are mathematical audit findings here;
their Lean verification remains an obligation. They are not claimed proved
by the numerical Grönwall module.

### Existing S13 — asymptotic rate is substituted by an equality

The actual susceptible drift is
$-\lambda_nU/(1+\lambda_nU)$, not
$-(\lambda/n)U/(1+(\lambda/n)U)$. Under only $n\lambda_n\to\lambda$ the
additional deterministic drift error tends to zero but need not be $O(1/n)$.
The fluid proof must retain this error and show its accumulated contribution,
after division by $n$, is $o(1)$. A Lipschitz estimate gives the relevant
$|n\lambda_n-\lambda|$ control on valid states with $0\le U\le n$.

### Existing S14 — reversed indices and conditioning

With the source definitions
$\widehat X_j=-X_{\tau-j+1}$ and
$\widehat S_j=I_{\tau-j}$, a forward indicator $\mathbf1_{\{X_i=1\}}$
becomes $\mathbf1_{\{\widehat X_{\tau-i+1}=-1\}}$. The printed reversed sum
uses the index $\tau-i$ instead. The equality is false literally. For example,
take increments $(+1,-1,-1)$, infectious counts $(1,2,1,0)$, $\tau=3$ and the
cutoff $n=1$. The printed forward sum is $1/2$, while its claimed reverse sum
is zero. A correctly pre-step-indexed attachment sum uses $X_{i+1}$ with
denominator $I_i$ and then has the advertised reversed index.

Even after correcting indices, a bound on forward transition probabilities
does not establish iid domination after reading increments backward from a
random extinction time and conditioning on a future event. That coupling
must be proved or replaced. A new route must not certify the bypassed reverse
coupling as checked.

### Further checks to retain

- The Bernoulli variables in A87 have varying parameters. They can be
  independent, but are not identically distributed in general.
- The source's terminal uniform-vertex truncation argument A77 must identify
  actual membership in a forward truncation. A reverse birth-time law cannot
  be silently substituted. The precise error coefficient in the displayed
  $1-\varepsilon+o(1)$ estimate must be derived or handled by reparameterizing
  an $O(\varepsilon)$ bound.
- The source Skorokhod passage does not by itself establish T04's full
  near-origin uniform assumptions on the random triangular array. A78/A81
  need the actual logarithmic-cutoff slope estimates and the survival-event
  restriction where applicable.
- Source fluid shape facts in A70–A72 and the Lambert-$W$ formula remain
  separate obligations even if another proof bypasses Lambert $W$.

## Feasible dependency order

1. Establish the finite count kernel, whole history, legal support, deterministic
   absorption bound and terminal-tree law. Couple it with the actual
   attachment/freezing tree transitions. The clock-race/Poisson bridge remains
   explicit A65 unless independently proved.
2. Prove early fixed-prefix parameter bounds for general rates, and construct
   actual prefix couplings to the iid model. The early stochastic state is
   stopped at zero; no unrestricted-walk equality is claimed.
3. Transfer frozen finite balls to the actual terminal horizons and apply
   T02. This is a direct route to T06.I including finite extinction.
4. For T06.II, consider proving the stronger root-degree divergence in
   probability. Every fixed prefix approaches the all-attachment model;
   recursive-tree root degrees grow with the prefix length; terminal degree
   dominates prefix degree. This avoids an unnecessary general Prokhorov
   subsequence argument, but must be recorded as a proof departure.
5. Build the integer-valued unstopped count process and corrected martingale/
   Grönwall fluid estimate with the actual $n\lambda_n$ perturbation. Prove
   the early extinction probability and one shared limiting survival mixture.
6. Apply the proved T04 results only after actual all-vertex sampling,
   early-slope and random-horizon truncation hypotheses are established.
7. Resolve or replace the late reverse-time argument before claiming the
   T07.II maximum-height limit. Neither T04 at time $n$ nor the forward
   transition bound alone closes this part.

The inventory phase above did not mark any SIR main theorem complete. Later
implemented results and their exact scope are recorded below. There is no new
Comparator or Palomar evidence, and proof completion is not inferred from the
inventory alone.

## New actual-clock foundation for A65

`Freezing1/SIRExponentialRace.lean` now proves a genuine nonempty finite
independent exponential-clock minimum law, rather than assuming the aggregate
rate. `earliestClock_law` identifies the pushforward of the actual finite
product of `expMeasure (rate i)` measures with `expMeasure (sum rates)`.
`exponential_race_left` and `exponential_race_right` compute strict winner
probabilities from the product of two actual exponential measures by density
integration and survival functions.

Consequently, `individualClock_race` derives both SIR event probabilities from
the independent contact clock family indexed by `Fin I × Fin U`, with each
contact rate $r>0$, and the recovery family indexed by `Fin I`, with each
recovery rate one, for $I,U>0$. The two grouped minima have their actual joint
product exponential law, with rates $rUI$ and $I$. The displayed rational SIR
event probabilities follow by cancellation. Positive-rate and nonempty-index
premises are necessary to describe these real-valued exponential clocks;
there is no attempt to use an exponential distribution of rate zero as a
probability measure.

The final direct check of this module passes. At that milestone these exports
proved a meaningful part of A65, without certifying the complete embedded
infection-tree law. The finite winner and residual-clock obligations were
subsequently advanced as recorded below; the whole epidemic-history bridge
remains distinct.

`SIRSourceChecks.lean` also passes its final direct check. Three axiom closures
for its numerical counterexample use only `propext`, `Classical.choice`, and
`Quot.sound`. Root integration and any new full-project checks are separate.

## T06.II: implemented stronger root-degree obstruction

`PlaneRecursiveRootDegree.lean` and `SIRStrongLocalNonTightness.lean` pass their
actual-file direct Lean checks without diagnostics. The latter proves
`SIR.embeddedTerminalTreeLaw_not_tight` for the genuine embedded terminal tree
law at the proved terminal event horizon $2n+1$. Its only rate hypothesis is
$n\lambda_n\longrightarrow+\infty$; the rates are nonnegative and need not
form a monotone sequence.

The proof deliberately strengthens the source's non-tightness conclusion:
for each fixed integer $d$, the probability that the terminal root has at most
$d$ children tends to zero. This proof departure checks the following actual
dependencies rather than assuming the desired infection-tree law:

- The verified all-attachment forward process retains the active root. Its
  already proved active-and-bounded-degree bound therefore yields escape of
  its graph root degree.
- The chronological plane projection has exactly that root child count.
  `Forward.ValidAt.toPlaneState_rootDegree` proves the deterministic equality
  from the actual valid graph and parent structure.
- `SIR.treeFullLaw_plane_events_tendsto_strong` in `SIRTreeWordMixture.lean` compares each
  fixed embedded SIR prefix with the actual all-attachment plane chain,
  uniformly over state events.
- Every supported embedded SIR update preserves the vertex set or adds a
  vertex. Consequently terminal root child count dominates the count at any
  earlier prefix, with the comparison taken at $2n+1$, not at $n$.
- Plane-tree degree is continuous for the established local topology.
  Compact sets have bounded degree, which contradicts the resulting escape
  of terminal degree in probability.

Thus T06.II is proved for the explicit embedded chain without an additional
survival, fairness or non-starvation premise. The positive-rate whole-contact-history identification is now proved by
the separate A65 construction recorded below; it is not inferred merely by
relabelling this kernel theorem. The zero-contact protocol is now proved separately by the root's
optional/no-arrival carrier and recorded in `SIR_ZERO_RATE_AUDIT.md`.

## A65: exact individual winners and residual clock law

`SIRExponentialWinner.lean` passes its final actual-file direct check with no
diagnostics. For any finite family of independent positive-rate exponential
clocks it proves the designated strict-winner probability $r_i/\sum_j r_j$,
including the singleton family. A strict winner exists almost surely, and all
pairwise ties have probability zero. These facts are derived from the actual
clock product by splitting one coordinate from the remaining clocks.

For the existing `individualClockLaw`, the new exports prove the exact joint
weights

$$
\mathbb P(\text{infection by }j)
=\frac{1}{I}\frac{rU}{1+rU},
\qquad
\mathbb P(\text{recovery of }j)
=\frac{1}{I}\frac{1}{1+rU}.
$$

The selected infectious individual is uniform and independent of event kind;
this is proved as factorization of actual event intersections. The susceptible
recipient is uniform given an infection by a fixed individual. An almost-sure
comparison identifies the winner-based event kinds with the aggregate-minimum
comparisons used in `SIRExponentialRace.lean`. For $r>0$, the winner formulas
permit $U=0$; a separate `disabledContactClockLaw` samples only positive-rate
recovery clocks for the zero-contact-rate case. It never treats a nonempty
family of rate-zero exponential clocks as probability measures.

`SIRExponentialMemoryless.lean` also passes its final actual-file direct check
without diagnostics. It proves single-clock and finite-product memorylessness
as restricted-pushforward measure equalities, with their actual survival
coefficients. Its principal race export gives the following exact joint law.
For a finite nonempty family with rates $r_j>0$, let $R=\sum_j r_j$, let $W_i$
be the strict-winner event for clock $i$, and let

$$
\Phi_i(t)=\left(\min_j t_j,
             (t_j-\min_k t_k)_{j\ne i}\right).
$$

Then the implemented theorem proves

$$
(\Phi_i)_*\left(\left.\bigotimes_j\mathrm{Exp}(r_j)\right|_{W_i}\right)
=\frac{r_i}{R}\left(\mathrm{Exp}(R)\otimes
               \bigotimes_{j\ne i}\mathrm{Exp}(r_j)\right).
$$

The remaining product may be empty, so singleton races are covered. The proof
uses the genuine designated-clock split, finite-product tail memorylessness,
Fubini on measurable rectangles, and an actual exponential-density identity.
It assumes no conditional memorylessness or winner factorization as a
premise.

Six winner-module axiom closures in a local log (not retained)
use only `propext`, `Classical.choice`, and `Quot.sound`. The residual-module
axiom check is recorded separately in
a local log (not retained).

## A65: completed positive-rate original-history identification

Authorship note: the clock-history and physical-limit modules described from
this section onward were authored by this agent. The checks recorded here
are author self-review, not an independent audit. Root-owned independent
source/statement review and artifact/global trust checks are separate.

The full history bridge for positive contact rates is now proved, rather
than postulated as a conditional independence or embedded-law hypothesis.
`SIRClockPrefixLaw.lean` proves the joint event-word mass and residual product
of the same original static clock array after every finite history. Its
coordinate injection retains only nonwinning live or previously unused
slots, and the deterministic aging and activation identities are checked
pointwise. `SIRClockWordKernel.lean` then proves the entire original event-word
path law: every finite prefix is recovered from the last reversed word by
list dropping. `SIRClockTreeProjection.lean` sums actual contact recipients
and transports uniform labelled actors through the valid chronological
address injection. `SIRClockTreeFullLaw.lean` composes these results to prove
the original static-array complete tree history is exactly `treeFullLaw`.

The original Poisson input is also explicit. `SIRPoissonFirstArrival.lean`
defines actual simple, positive, divergent arrival paths and their counting
functions. Poisson one-time count marginals yield the exponential first-delay
law, using the exact event that the count is zero. Independent measurable
whole-contact paths and exponential recovery periods therefore give the joint
`preassignedClockLaw` in `SIRPoissonClockArray.lean`; exponential contact
first delays are a conclusion, not a new source premise.

`SIRPoissonFullContacts.lean` defines a genuine whole-arrival-path protocol.
At each current infection age, it recomputes the next actual contact point
from the entire original arrival sequence. The proved future-live-clock
invariant shows that a still-live pair has not passed its first point. Its
complete frame path consequently equals the static-array run on positive
arrays. The separate `SIRFirstContactIrrelevance.lean` checks decreasing
susceptibility, permanent removal and the ineffectiveness of later contacts
when the first was ineffective.

`SIRPoissonFullContactLaw.lean` passes its actual-file direct Lean check with
zero diagnostics (a local log, not retained). It proves
`independent_poisson_fullContact_tree_fullLaw` and
`independent_poisson_fullContact_counts_fullLaw` for the genuine next-point
protocol. The latter uses the literal susceptible and active label counts.
It also proves almost-sure finite absorption of the entire physical clock
frame by event $2n+1$, and
`independent_poisson_fullContact_terminal_tree_law` identifies the actual
terminal shape with `embeddedTerminalTreeLaw`. The input assumptions are a
probability space, independent measurable recovery and whole-contact path
coordinates, recovery marginal $\mathrm{Exp}(1)$, the source Poisson count
marginals, and $r>0$. No conditional memorylessness, history law, survival or
extra fairness assumption is supplied.

This verifies and expands the paper's informal "by construction" A65 argument.
Contact paths are indexed by the source's infection age and activated at its
infection time; actual calendar event times are proved to be source infection
time plus the fixed first-contact/recovery delay. No separate construction
with globally running calendar-time Poisson processes or strong-Markov
identification at a random infection time is asserted here. The theorem is
stated for given independent process data, as in the source model setup.

The root has now proved $r=0$ separately on a carrier containing a genuine
empty contact process. `SIRPhysicalZeroRate.lean` identifies its complete
physical tree/count histories and actual positive exponential recovery time.
Independent review and literal-count/A66 composition probes are recorded in
`SIR_ZERO_RATE_AUDIT.md`. The existing positive-rate history remains on its
original arrival-path carrier; no transport for arbitrary positive-rate
optional-path laws is silently asserted by the zero-branch audit. The main source rate limits with
positive finite limit, or divergent scaled rate, have eventually positive
rates, so this edge case does not obstruct transporting those asymptotic
results. Expanded complete-history statements and axiom probes are maintained
in `verification/SIRClockTreeFullLawStatements.lean` and
`verification/SIRPoissonFullContactStatements.lean`; root artifact integration
and global axiom replay remain separately recorded proof evidence.

## Source-facing physical main-limit wrappers

`SIRPhysicalLaws.lean` and `SIRPhysicalLimits.lean` pass their actual-file
direct Lean checks without diagnostics. The observable laws are defined by
the genuine whole-contact protocol. The proved law identities, rather than a
new equality premise, transport T06.I/II, T07.I.a and all four strong-regime
T07.II conclusions. Physical susceptible and infectious counts are the
literal label-set cardinalities. Terminal heights and distances use the
whole tree at the proved terminal horizon; conditionally uniform sampling
includes frozen vertices and the pair diagonal.

Only eventual source process data assumptions are required. Positivity is
derived eventually from the exact source rate ratio, so finitely many zero
rates do not introduce an extra asymptotic hypothesis. Invalid or zero-rate
early indices may be extended arbitrarily for the purposes of these limit
laws; the complete zero-rate process carrier remains separately recorded.
The fluid path target retains the same concrete geometric survival event at
every observation time. Expanded source-data and whole-path examples are
maintained in `verification/SIRPhysicalLimitStatements.lean`.


`SIRPhysicalFiniteLimits.lean` also passes its actual-file direct Lean check
without diagnostics. Its exact source-ratio wrappers prove the actual
complete-terminal physical height and distance weak limits in T07.I.b.height and T07.I.b.distance.
The normalized laws are explicitly the conditional uniform-sample laws
pushed forward by division by $\log n$, and their targets use the same
concrete geometric-survival scalar law at $\lambda/(\lambda-1)$ and
$2\lambda/(\lambda-1)$. Source assumptions remain eventual; positivity is
derived. No survival-conditioning or process-law identity is inserted as a
new hypothesis. Expanded normalization and source-limit statements are in
`verification/SIRPhysicalFiniteLimitStatements.lean`.
