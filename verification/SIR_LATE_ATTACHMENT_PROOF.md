# Forward late attachment budget and logarithmic remainder

Date: 29 October 2026. Implemented files: `SIRLateAttachmentBudget.lean` and
`SIRLateAttachmentSum.lean`. Source scope: the late reciprocal-attachment
conclusion in A82/A86, together with the alternate route past A84/A85.
The literal reversed identities and iid domination arguments remain separate
unchecked or corrected source obligations. This is an implementation proof
record, not an independent statement audit.

The actual pre-birth charge is

$$
q(c,d)=\frac{\mathbf1_{\{d.U<c.U\}}}{c.I}.
$$

It detects susceptible consumption on the actual transition $c\to d$.
The implementation includes zero susceptible and absorbed infectious states;
the charge is zero on held and recovery steps. Its genuine kernel mean is

$$
\int q(c,d)\,P(c,\mathrm d d)
=\frac{p(c.U)}{c.I},\qquad
p(u)=\frac{\lambda_n u}{1+\lambda_n u}.
$$

For any starting state with $p(c.U)\le\varepsilon<1/2$, the proved harmonic
drift and the true accumulated-cost potential give, at every future horizon
$K$,

$$
\mathbb E_c\sum_{j<K}q(C_j,C_{j+1})
\le\frac{\varepsilon}{1-2\varepsilon}\,H_{c.I}.
$$

Here $H_i$ is the harmonic number. The potential is accumulated charge plus
$\varepsilon H_I/(1-2\varepsilon)$. It is checked directly against the actual
transition kernel and then iterated under its constructed full law. No
conditional-expectation, independence, or survival conclusion is assumed.

For the real SIR history, the exact joint prefix/future law is used to
integrate this budget after a deterministic observation time. Restriction to
$p(U_a)\le\varepsilon$ is measurable from the prefix at time $a$; the future
then has the proved original Markov law from its actual last state. On valid
histories, $I_a\le n+1$, so the harmonic budget is at most
$\varepsilon H_{n+1}/(1-2\varepsilon)$. Markov's inequality gives a charge tail
bound plus the price of $p(U_a)\ge\varepsilon$.

Taking $a=\lfloor3n/2\rfloor$, A83 makes that price tend to zero. The elementary
bound $H_{n+1}\le3\log n$ eventually, followed by
$\varepsilon\downarrow0$, proves that every future-horizon charge divided by
$\log n$ tends to zero in probability.

The middle interval from $n$ to $\lfloor3n/2\rfloor$ is treated directly.
On the genuine strong-fluid good event, $I_k\ge n/4$ throughout that interval.
Every legal transition satisfies

$$
\frac n4 q(C_k,C_{k+1})\le U_k-U_{k+1}.
$$

Telescoping gives a middle charge at most $4U_n/n$, which tends to zero in
probability by the proved actual susceptible bound. Exact finite-sum
splitting then controls the whole post-$n$ charge through the deterministic
terminal horizon $2n+1$:

$$
\Pr\left(\eta\log n\le\sum_{j=n}^{2n}q(C_j,C_{j+1})\right)\longrightarrow0,
\qquad \eta>0.
$$

The charged transition is $j\to j+1$. Its attachment indicator therefore
corresponds to the next increment $X_{j+1}$, rather than certifying the printed
shifted source identity. Charges vanish after actual absorption. The proved
legal-transition comparison

$$
\frac{\mathbf1_{\{d.U<c.U\}}}{d.I}\le q(c,d)
$$

also supplies domination of the post-birth reciprocal used by the actual
height scale. The remaining formal tree/schedule identification and maximum
height transfer require their own interfaces; they are not asserted by the
budget alone.

This is a substantive proof departure replacing the source's
future-conditioned reversal and iid walk domination. It does not certify
those bypassed arguments or the false reversed index identity. It retains
the general per-pair rate and uses the actual stopped law throughout. The
physical Poisson-process bridge and the remaining height theorem dependencies
are separate.

The expected-budget direct check passes without diagnostics; its five probed
closures use exactly `propext`, `Classical.choice`, and `Quot.sound`.
Evidence is retained in `sir-late-attachment-budget-direct.log` and
`sir-late-attachment-budget-axioms.log`. The sum module also passes its final standalone direct check without
diagnostics; evidence is retained in `sir-late-attachment-sum-direct.log`.
Its ten probed axiom closures contain exactly the standard three, with
evidence in `sir-late-attachment-sum-axioms.log`. Root Lake integration is
recorded separately.
