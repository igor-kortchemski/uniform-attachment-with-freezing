# Poisson first-contact bridge: proof record

Date: 29 October 2026. Source scope: the independent homogeneous contact
processes and infectious periods in the SIR model at source line 2026,
and their connection to the physical clock construction in A65/A66.
Implemented first-arrival core: `SIRPoissonFirstArrival.lean`. This is an
implementation record; the independent source-statement audit is separate.

The positive-rate contact path is represented by a sequence
$a_0<a_1<\cdots$ with $a_0>0$ and $a_j\to\infty$. This is the canonical
arrival-sequence representation of a positive, simple, locally finite
counting path with infinitely many arrivals. Its actual count at real time
$t$ is

$$
N_a(t)=\min\{j\ge0:t<a_j\}.
$$

Finiteness of this minimum follows from divergence. The implementation
proves measurability of every count coordinate and the pointwise
characterization

$$
a_j\le t\quad\Longleftrightarrow\quad j<N_a(t).
$$

In particular,

$$
N_a(t)=0\quad\Longleftrightarrow\quad t<a_0,
\qquad
\{t:N_a(t)>0\}=[a_0,\infty).
$$

Thus the coordinate called `first` is the counting process's actual first
contact time, including the value at the jump. It is not merely a proposed
exponential random variable detached from a counting path.

For a probability law $\nu$ on these paths, `HasPoissonCounts nu r` states
only the exact Poisson counting marginal used from the given process:
$N(t)$ has distribution $\operatorname{Poisson}(rt)$ for each $t\ge0$.
It does not assume an exponential first-arrival law. For $r>0$, the
zero-count probability and the pointwise characterization imply

$$
\Pr_\nu(a_0>t)=\Pr_\nu(N(t)=0)=e^{-rt},\qquad t\ge0.
$$

For negative $t$ the tail is one by positivity of the first arrival.
Equality of the real cumulative distribution functions then proves
`nu.map first = expMeasure r`.

This theorem applies to a given actual Poisson process law in canonical
arrival coordinates. It does not construct a Poisson process law from
scratch, nor prove existence of a measurable arrival enumeration for an
arbitrarily supplied counting-process carrier. The full Poisson independent
increment law is stronger than the marginal assumption used here. A source
model supplied with that full law therefore satisfies the needed marginal
assumption, but the implementation does not define marginal assumptions
alone to mean the complete Poisson process law.

The rate-zero contact process is outside this finite first-arrival carrier:
its first contact would be at infinity. That source boundary remains
separate. The source's independent Poisson processes and recovery periods
are random model data; no embedded-chain or conditional race law is assumed
in the first-arrival result.

`SIRPoissonClockArray.lean` supplies the exact independent-array endpoint.
The underlying random coordinates contain a real recovery lifetime in
each recovery slot and an entire arrival path in each directed-contact
slot. Its assumptions on the given actual probability space are:

- every such coordinate is measurable;
- the family of full coordinates is independent;
- each recovery coordinate has exponential law of rate one;
- each contact-coordinate law has the Poisson counting marginals above.

Coordinate maps take a recovery period unchanged and a contact path to its
proved actual first contact. Independence is preserved under these
measurable maps. The finite-family joint-map theorem and the proved
individual laws yield exactly

$$
\mu\circ(\text{first-contact/recovery array})^{-1}
=\bigotimes_c\operatorname{Exp}(r_c),
\qquad
r_c=\begin{cases}1&\text{recovery},\\r&\text{contact}.\end{cases}
$$

The right side is the existing `preassignedClockLaw r n`. This is the
export `independent_firstArrivalArray_law`; no equality to that clock law
is assumed. The array includes unused self-contact slots. If the source
model excludes self contacts, those slots can be supplied as independent
dummy processes; valid live contact slots never have equal source and
target. The later static-array history transport is a separate proof.

The core passes direct Lean checking with `autoImplicit=false` and no
diagnostics; retained evidence is `sir-poisson-first-arrival-direct.log`.
Its four probed closures contain exactly `propext`, `Classical.choice`, and
`Quot.sound`; evidence is retained in
`sir-poisson-first-arrival-axioms.log`. The array module also passes direct
checking without diagnostics; evidence is retained in
`sir-poisson-clock-array-direct.log`. Both array closure probes contain
exactly the standard three, with retained evidence in
`sir-poisson-clock-array-axioms.log`.
