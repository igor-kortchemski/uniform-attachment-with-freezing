# Finite-rate terminal sampling capture: proof record

Date: 29 October 2026. Source scope: the near-terminal prefix and uniform
sample capture argument at lines 2199–2203 of
`attachement-uniforme-1-final.tex` (A77 and the sampling dependency of
T07.I.b). Implemented core: `SIRFiniteRateCapture.lean`. This is an
implementation proof record; independent statement reconstruction and the
height/distance transfer are separate.

Write $t_0$ for the unique positive zero of the proved infectious fluid
profile $h_\lambda$, with $\lambda>1$. The actual varying rates satisfy
$n\lambda_n\to\lambda$. For every fixed $s\in(t_0,2]$, the actual stopped
count law satisfies

$$
\Pr(I^n_{\lfloor ns\rfloor}>0)\longrightarrow0.
$$

Indeed, on actual survival through this observation, the constructed
stopped/unstopped coupling identifies the infectious count with the
auxiliary integer count. Its fluid limit is strictly negative at $s$.
Uniform auxiliary convergence, the proved Lipschitz profile bound, and the
floor error give a contradiction outside an event of vanishing probability.
No assumption about the actual extinction time is used.

Susceptible counts decrease by at most one per legal step and are held
after absorption. Therefore, for every fixed $t\in[0,t_0)$ and tolerance
$\eta>t_0-t$,

$$
\Pr\left(U^n_{\lfloor nt\rfloor}-U^n_{2n+1}\ge\eta n\right)
\longrightarrow0.
$$

Choose $s>t_0$ with $s-t<\eta$ and $s<2$. If the process has died by
$\lfloor ns\rfloor$, all subsequent susceptible counts equal that value,
and the remaining difference is bounded by
$\lfloor ns\rfloor-\lfloor nt\rfloor\le(s-t)n+1$.
This controls late births unconditionally, including histories with early
extinction.

For a fixed $t\in(0,t_0)$, retain the same early gate
$G_n=\{I^n_{\lfloor\delta n\rfloor}>0\}$ at every observation.
If $0<\delta<h_\lambda(t)/8$, the proved gated stopped-fluid approximation
implies

$$
\Pr\left(G_n\cap\{I^n_{\lfloor nt\rfloor}=0\}\right)\longrightarrow0.
$$

The actual count identity at an alive prefix gives

$$
\lfloor nt\rfloor
\le2\left(n+1-U^n_{\lfloor nt\rfloor}\right).
$$

Consequently any fixed $b<t/2$ is eventually a lower bound, after division
by $n$, for the number of prefix vertices on the gated good event. For
$t>t_0/2$, the common choice $b=t_0/8$ works uniformly in how near $t$ is to
$t_0$. The combined export `countsFullLaw_gated_capture_tendsto` controls
the union of the late-birth and small-prefix events on that one gate.
Its small-$\delta$ condition can be included in the finite minimum of
conditions required by the separate finite-rate random-environment proof.

This is a direct count-law replacement for the printed appeal to the
uniform-birth lemma and the unquantified near-terminal truncation. It keeps
the actual terminal horizon $2n+1$, handles absorption before the prefix,
and does not infer terminal susceptible final-size convergence from
infectious-path convergence alone. The physical contact-process bridge and
the terminal height/distance laws remain separate obligations.

The further module `SIRFiniteRateSamplingCapture.lean` gives the direct
unconditional relative-loss statement. If
$t_0/2<t<t_0$ and $t_0-t<\eta t_0/8$, then

$$
\Pr\left(U^n_{\lfloor nt\rfloor}-U^n_{2n+1}
\ge\eta\left(n+1-U^n_{2n+1}\right)\right)\longrightarrow0.
$$

For the surviving gate, the terminal vertex count is at least the prefix
count, so apply the preceding bound with absolute tolerance $\eta t_0/8$.
If the gate is false and $\delta<t$, absorption gives equality of the prefix
and terminal counts. Their positive vertex count makes the relative-loss
event impossible. The corollary chooses such a positive $\delta$ internally;
its final event has no gate premise. An explicit parameter-selection lemma
allows choosing $t$ arbitrarily close to $t_0$ for any positive tolerance.

This establishes the required near-terminal capture, with cutoff chosen
according to the desired tolerance. It does not certify the printed claim
with exactly the same $\varepsilon$ as both a time offset and a probability
error coefficient.

Both modules pass direct checking without diagnostics; retained evidence is
`sir-finite-rate-capture-direct.log` and
`sir-finite-rate-sampling-capture-direct.log`. The seven core closure probes
are retained in `sir-finite-rate-capture-axioms.log`: six contain exactly
`propext`, `Classical.choice`, and `Quot.sound`, while the elementary alive
prefix-card bound uses only `propext` and `Quot.sound`. Both final corollary
closure probes contain exactly the standard three, with retained evidence
in `sir-finite-rate-sampling-capture-axioms.log`. Root Lake integration and
independent statement reconstruction are recorded separately.
