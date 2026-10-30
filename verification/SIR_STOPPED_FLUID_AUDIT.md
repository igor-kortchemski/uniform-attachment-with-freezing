# Stopped fluid transfer: scope and proof departure

Date: 29 October 2026. Implemented file: `Freezing1/SIRStoppedFluidTransfer.lean`.
Source dependencies: A70–A73 and T07.I.a. This file proves a transfer needed
for the main result, not the final survival-mixture limit.

For the actual joint stopped/unstopped Markov law, write $I_k$ for the stopped
infectious count and $\widetilde I_k$ for the unrestricted integer coordinate.
Let $h_\lambda(t)=2-2g_\lambda(t)-t$ and
$h_\lambda^+(t)=\max(h_\lambda(t),0)$. For every $\lambda>0$, general
nonnegative rates satisfying $n\lambda_n\to\lambda$, natural compact horizon
$m$, error $\varepsilon>0$ and fixed $0<\delta<\varepsilon/4$, the proved
conclusion is

$$
\Pr\left(\exists t\in[0,m]:\left|\frac{I_{\lfloor nt\rfloor}}n-
\mathbf1_{\{I_{\lfloor\delta n\rfloor}>0\}}h_\lambda^+(t)\right|
\ge\varepsilon\right)\longrightarrow0.
$$

One early survival indicator is shared by every observation time. The formal
`gated_stopped_real_fluid_two_stage` states the order explicitly: first
$n\to\infty$, then $\delta\to0$ from above. The real-time error event is
proved Borel measurable by its dependence on finitely many observations.
Natural horizons cover every bounded nonnegative real time interval.

The probability of this early survival indicator is not assumed or proved by
the transfer file. The companion `SIREarlyExtinction.lean` now proves its
required two-stage probability limit, as recorded below. The companion `SIRGeometricSurvivalPath.lean` now identifies the concrete
geometric Bienaymé survival event with the same mixture law. The companion
`MainSIRFluid.lean` supplies the embedded weak path-law conclusion with that
exact source event; the transfer alone is not that final weak-convergence
statement.

The proof uses the actual `SIRStoppedCoupling.fullLaw` and its proved complete
marginals. Agreement includes the first extinct state. If the true auxiliary
fluid error is at most $\eta$ through horizon $N$ and the observation index is
$a>0$, the stopped error with the shared gate is bounded by

$$
\frac{a+1}{n}+\left(1+\frac Na\right)\eta.
$$

On a failed early gate, the stopped path is zero after $a$, and before $a$
its infectious count is at most $a+1$. On a successful gate, the actual and
auxiliary coordinates agree up to and including first extinction $j>a$.
At that point the profile is within $\eta$ of zero. Concavity and
$h_\lambda(0)=0$ give the proved secant inequality

$$
j\,h_\lambda(k/n)\le k\,h_\lambda(j/n),\qquad j\le k.
$$

Consequently the positive part after extinction is at most $(N/a)\eta$.
The actual auxiliary uniform fluid theorem supplies the error probability;
no conditional drift, noise convergence or stopped convergence is assumed.
Taking $a=\lfloor\delta n\rfloor$ gives the announced order of limits.
The derivative formula proves a global Lipschitz bound one for $h_\lambda$,
which controls the $1/n$ rounding error for the actual step paths.

This is a substantive proof departure. It uses a concavity secant bound
instead of selecting compact positive minima before the positive zero and
negative-profile windows after it. The source positivity/unique-positive-zero
claims remain proved in `SIRFluidProfile.lean`, but that window argument is
bypassed here. The false printed global future-maximum drift criterion is not
used or certified. All rate perturbations retain $|n\lambda_n-\lambda|$.

The standalone direct check passes without diagnostics. Eight relevant axiom
closures contain only `propext`, `Classical.choice` and `Quot.sound`; retained
evidence is `sir-stopped-fluid-transfer-direct.log` and
`sir-stopped-fluid-transfer-axioms.log`. Root Lake integration is a separate
recorded check. The physical exponential/Poisson process bridge remains a
separate obligation.

## Exact early gate probability: companion milestone

`SIREarlyExtinction.lean` proves the formerly missing probability estimate
from the actual stopped law, for general nonnegative rates with
$n\lambda_n\to\lambda>1$. For every $\varepsilon>0$ there is
$\delta_0>0$ such that every fixed $0<\delta<\delta_0$ satisfies, eventually
as $n\to\infty$,

$$
\left|\Pr(I^n_{\lfloor\delta n\rfloor}=0)-\frac1\lambda\right|<\varepsilon.
$$

The complementary early survival probability is correspondingly
$1-1/\lambda$, in the same order of limits. Both are also exported using the
right-neighborhood filter $\delta\to0$ from above.

The lower bound first fixes a finite prefix, uses the actual finite-prefix
SIR-to-absorbed-walk convergence, and then lets the prefix length grow. The
proved iid absorbed-walk extinction probability tends to $1/\lambda$.
Actual extinction-event monotonicity transfers this lower bound to
$\lfloor\delta n\rfloor$. The upper bound chooses a constant
$1/\lambda<r<1$ and takes
$\delta_0=(r\lambda-1)/(2r\lambda)$. Retaining the exact susceptible lower
bound makes $r\lambda_n(n-\lfloor\delta n\rfloor)\ge1$ eventually, so the
actual kernel superharmonic estimate bounds early extinction by $r$.
No limiting survival probability or stochastic domination is assumed.

The corrected event is hitting infectious zero in the absorbed walk. The
source argument about reaching strictly negative integers is not used or
certified. The proof bypasses optional stopping and an infinite-time walk
coupling. Its eight probed closures use only the standard three axioms, and
the standalone direct check passes without diagnostics; evidence is retained
in `sir-early-extinction-direct.log` and `sir-early-extinction-axioms.log`.
The concrete Bienaymé survival-event identification is now supplied by
`SIRGeometricSurvivalPath.geometricSurvivalPathLaw_eq_fluidMixtureLaw`. The
embedded weak path-law mixture is proved in the companion module below.


## Embedded weak path-law mixture

`MainSIRFluidMixture.lean` now proves actual probability-measure weak
convergence

$$
\operatorname{Law}\left(\left(I^n_{\lfloor nt\rfloor}/n\right)_{t\ge0}\right)
\Longrightarrow
\left(1-\frac1\lambda\right)\delta_{h_\lambda^+}
+\frac1\lambda\delta_0
$$

for the genuine stopped embedded count process, under the general rate
hypothesis $n\lambda_n\to\lambda>1$. The literal source-ratio wrapper is also
proved. The path carrier contains the actual step functions and has the
proved topology of uniform convergence on compact subsets of nonnegative
times. Its path laws are genuine measurable pushforwards. Capping the stored
observations at $2n+1$ is proved almost surely equal to the actual entire
stopped step path by the deterministic absorption bound.

For each bounded continuous real test function, continuity at the zero path
and the positive profile gives one common finite time window and a positive
path tolerance. The true shared-gate estimate controls the test-function
error outside one measurable bad event; boundedness pays at most
$2\lVert F\rVert$ times its probability on that event. The derived two-stage
early gate probability then gives the desired two-atom expectation. The
formal weak-convergence criterion for probability measures completes the
proof. No global uniform continuity, separability, Polish-space assumption,
Skorokhod realization, assumed gate limit or assumed noise convergence is
added.

This module proves the numerical two-path mixture for the constructed
embedded model. `SIRGeometricSurvivalPath.lean` separately identifies it with
the path selected by survival of the actual iid geometric offspring tree,
and `MainSIRFluid.embedded_sir_fluid_limit` composes the two statements. The
independent physical Poisson epidemic is not yet identified with that kernel;
that remains separate from the weak-convergence proof. Its direct check passes without diagnostics;
retained evidence is `main-sir-fluid-mixture-direct.log`. All eight probed
axiom closures contain only the standard three, with evidence in
`main-sir-fluid-mixture-axioms.log`. Root Lake integration is recorded
separately.
