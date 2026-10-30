# A85: exact reverse-coupling obligation and current progress

This is an authored investigation/proof record for source lines
2287–2305. The source and scope are unchanged. The genuine weak coupling
claim remains **open**; the results below do not certify it through the
already proved forward-budget alternative.

## Exact remaining assertion

`SIRReverseCouplingFormulation.SourceReverseIidCoupling` records the
actual source requirement as a joint probability law with two marginals:
the complete stopped `countsFullLaw rate n` and the genuine infinite iid
sign law with negative-sign probability $\varepsilon$.

The first extinction index is the root's total measurable
`boundedExtinctionIndex`, which is proved to be the genuine first zero
under the actual law. The source gate retains its exact integer-time
meaning:

$$
\mathcal A^n_\varepsilon=
\left\{H:\forall k\in\mathbb N,\quad
3n/2\leq k\leq2n\ \Longrightarrow\ p(U_k)\leq\varepsilon\right\},
\qquad p(u)=\frac{ru}{1+ru}.
$$

On this gate and for
$1\leq j\leq\min(\lfloor n/2\rfloor,\tau-n)$, a reversed negative
increment must imply a negative auxiliary sign. Reversed negativity is
read from the actual birth transition between counts at $\tau-j$ and
$\tau-j+1$. All these events and the random-index evaluations are proved
measurable. On the genuine pre-extinction support, this is exactly
$-X_{\tau-j+1}=-1$.

The auxiliary signs need only have their iid marginal **unconditionally**.
They may be correlated with the epidemic and with $\mathcal A^n_\varepsilon$.
The formulation adds no independence from that event, no conditional iid
property and no conditional reverse-transition bound. A counterexample to
one of those stronger properties would not refute the source claim as
needed by the subsequent expectation argument.

`SIRReverseCouplingNecessary` proves the necessary unconditional bound

$$
\mathbb P(\mathcal A^n_\varepsilon,\ j\text{ in the window},\
\widehat X_j=-1)\leq\varepsilon
$$

from an explicit coupling hypothesis. This is a necessary-condition
helper, not a proof that the coupling exists. It follows by transporting
the joint marginals and using the actual iid coordinate mass.

## A positive-probability gap in window inheritance

The source gate controls forward hazards starting at $3n/2$. Its reversed
window can start earlier, at $\tau-\lfloor n/2\rfloor$. These are not
the same cutoff. The root's separate half-window reduction supplies a
fluid argument for a remainder; it does not make this exact finite
inheritance automatic.

`SIRReverseCouplingWord` uses the genuine feasible SIR word

$$
n=6,\qquad (+,+,+,-,-,-,+,-,-).
$$

Its complete susceptible/infectious count sequence is proved to be

$$
(6,1),(5,2),(4,3),(3,4),(3,3),(3,2),(3,1),(2,2),(2,1),(2,0).
$$

The first extinction is nine; afterwards the actual stopped counts hold.
The word has strictly positive atom probability for every positive rate.
A general positive-atom lemma is proved from the actual adaptive word
recurrence and positivity of all susceptible prefixes.

`SIRReverseCouplingWindowGap` transfers that atom through the exact
whole-prefix pushforward to the actual complete count-history law. Legal
absorption then gives a **positive-probability actual-law event** with
the displayed prefix and holding after time nine.

Take $\varepsilon=p(2)$. Every source-gate hazard at times nine through
twelve is $p(2)$, so the gate holds. But the reversed index $j=3$ belongs
to its stated window, since
$\min(\lfloor6/2\rfloor,9-6)=3$. It uses the infection at forward
step seven, whose pre-step susceptible count at time six is three.
Thus its relevant forward hazard is $p(3)>p(2)$ for every positive rate.
For example, at rate $1/100$, the two hazards are $1/51$ and $3/103$.

`SIRReverseCouplingSourceGap` expresses the same event with the exact
source gate and the genuine first-extinction index. It proves that the
late gate does **not** imply an almost-sure bound by $\varepsilon$ on
all the forward hazards appearing in the displayed reverse window.
This is a formal counterexample to that stronger window-inheritance
shortcut. It is **not** a counterexample to the weaker source coupling:
positive probability of a reversed negative increment can coexist with
its unconditional probability being at most $\varepsilon$.

## Remaining mathematics and viable routes

The unresolved assertion is existence of the actual joint law in
`SourceReverseIidCoupling`, not its measurability or a missing support
condition. Padding the reversed-birth indicators by zero off the gate
and outside the random window gives a finite Boolean vector. Existence
of the required iid domination would follow from a proved stochastic
domination of that vector by a Bernoulli-$\varepsilon$ product vector,
together with a genuine coupling construction. Bounds on single
coordinates alone do not establish that multivariate statement.

A faithful corrected route could instead use a buffered forward cutoff
and an additional proved fluid good event, with its error probability
retained explicitly. That would repair the window mismatch. It would
still require a genuine reverse-vector domination theorem; forward
predictable infection probabilities alone are not a proof of it.

Finite floating-point discovery tests explored complete actual SIR word
probabilities and a finite monotone transport/max-flow condition. They
found no obstruction on the tested even sizes up to twenty and the rate
grid $10^{-4},10^{-3},10^{-2},3\cdot10^{-2},10^{-1},3\cdot10^{-1},1,3$.
These checks have tolerances and are **not Lean proof evidence**. They do
not justify a generic domination theorem or a completion claim. The
development scripts are `/tmp/check_sir_reverse.py` and
`/tmp/check_sir_reverse_flow.py`; the latter uses the exact finite Markov
recurrence but floating-point probabilities and capacities.

## Current files and evidence boundary

- `SIRReverseCouplingWord.lean`: frozen actual direct PASS0;
- `SIRReverseCouplingFormulation.lean`: frozen actual direct PASS0;
- `SIRReverseCouplingWindowGap.lean`: frozen and built;
- `SIRReverseCouplingNecessary.lean`: frozen and built;
- `SIRReverseCouplingSourceGap.lean`: frozen actual direct PASS0 and built;
  no mathematical coupling-existence claim is made.

All five artifacts are globally integrated in the root's 4,570-job build
and 7,703-closure milestone. The actual-import probe
`SIRReverseCouplingProgressStatements.lean` passes five expanded examples
and ten closures, all exactly the three permitted axioms, in
`sir-reverse-coupling-progress-statements.log`. No worker
artifact writes, toolchain change, source change, conditional-domination
premise, or upload is involved. A85 and the future-conditioned coupling
part of S14 remain open.

The next proof target is a genuine one-susceptible base case with arbitrary
initial infectious population. If $p=r/(1+r)$ and $q=1-p$, its first
infection time has truncated geometric masses. A reversed birth at
$j\leq m$ has mass $q^2$ times the last-negative-position mass of a
length-$m$ iid Bernoulli-$p$ word. Thinning that actual iid last position
and allocating residual mass to infection times zero, one and two gives
a viable noncausal coupling. The full stopped-kernel marginal and exact
iid marginal must both be proved; neither is assumed. The extension to
multiple susceptible individuals and the source gate remains open.

Work stopped at the user's request on 2026-10-30. The genuine actual-law
and iid last-negative foundations are now frozen and built. Newer
first-time and joint-marginal source drafts, their precise evidence
boundary, and the unwritten domination/history wrapper are recorded in
`A85_ONE_SUSCEPTIBLE_HANDOVER.md`. A85/A86 remain open.
