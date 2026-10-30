# Entire contact paths and the static epidemic: proof record

Date: 29 October 2026. Implemented modules:
`SIRFirstContactIrrelevance.lean` and `SIRPoissonFullContacts.lean`.
Source scope: the physical SIR contact/recovery model and the embedded-tree
identification at lines 2026–2042 (A65/A66). The model inputs are given
independent Poisson processes in canonical arrival coordinates and
exponential recovery periods, with strictly positive contact rate. This
record concerns the deterministic contact protocol; the independent-array
law and the static full-history law are separate proved dependencies.

The entire arrival sequence of each directed contact process is retained.
At infection age $t$, its actual next point is

$$
\operatorname{next}(a,t)=a_{N_a(t)}>t,
$$

where $N_a(t)$ is the proved counting function. If $t<a_0$, the next point
is exactly $a_0$. The full protocol recomputes these next points after each
step for every live directed pair. Recovery slots retain the same original
infectious period. Event ages are converted to absolute times using the
source's recorded infection time. No contact path or recovery period is
resampled.

The source counts only infections and recoveries as steps. An inactive
source or nonsusceptible recipient therefore contributes no live contact
slot. This discards no possible later infection:

- Every labelled population update decreases the susceptible set, and the
  actual entire static-run susceptible history is proved antitone.
- If an active source's contact finds a susceptible recipient, the update
  immediately removes that recipient from susceptibility. If it finds a
  nonsusceptible recipient, the recipient remains nonsusceptible.
- A recovered source is outside both the susceptible and active sets, and
  every subsequent population update preserves that removed status.
- For a chronologically ordered arrival path, the two conditions for an
  effective contact are decreasing in infection age: the age is smaller
  than the recovery period, and the recipient is still susceptible. If
  the first contact is ineffective, every later directed contact is
  ineffective. This includes recovery before the first contact.

The key pointwise bridge uses the existing deterministic `FutureLiveClocks`
invariant. On a positive first-delay array, every currently live first
contact is still strictly in the future. Its source infection age is
therefore less than its first arrival. The actual next point recomputed
from the entire path equals that same first arrival on every live slot.

`firstLiveClock_congr_on_live` proves that the selected event depends only
on live-slot values. `clockFrameStep_congr_on_live` then proves equality of
the updated population, absolute event time, and all source infection
times. Induction gives the exact entire-history identity

$$
\operatorname{poissonFullContactRun}(n,a)
=\operatorname{preassignedRun}
\bigl(n,\operatorname{firstArrivalArray}(a)\bigr).
$$

This is `poissonFullContactRun_eq_preassigned`. Its sole pathwise premise is
positivity of every first-contact/recovery delay. It is a comparison with
the explicit full-arrival next-point protocol, rather than a silent
definition of a physical process to be the first-delay array. Strict race
ties are totalized by holding on both sides; their probability-zero
property belongs to the already proved positive-rate race laws.

The comparison assumes no Markov kernel, exponential residual conclusion,
or conditional independence of future events. Its probabilistic consumer
uses the derived independent-array pushforward and the independently proved
static full-history law. Construction of a Poisson process law from scratch,
or conversion of an unrelated counting-path carrier to a measurable arrival
enumeration, is not asserted. The source rate-zero boundary remains
separate because a never-contacting path has no finite first arrival.

Both actual source files pass direct checking with `autoImplicit=false`
and no diagnostics. Retained evidence is
`sir-first-contact-irrelevance-direct.log` and
`sir-poisson-full-contacts-direct.log`. The five irrelevance closure probes
contain exactly `propext`, `Classical.choice`, and `Quot.sound`; evidence is
retained in `sir-first-contact-irrelevance-axioms.log`. Root integration and
independent statement reconstruction are recorded separately. All four
complete-protocol closure probes contain exactly the standard three;
evidence is retained in `sir-poisson-full-contacts-axioms.log`.
