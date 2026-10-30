# Independent audit of the strong-infection stopped fluid limit

Date: 29 October 2026. Scope: T07.II.a, A79's absolute fluid conclusion and
A80; source `attachement-uniforme-1-final.tex`, lines 2095–2101 and 2216–2239,
SHA-256 `88953dd87165a14b0e643c5b3d0075d8ce5ec39cdcfc0c25d313570fc3ab00df`.
The source and declared whole-paper scope are unchanged. This is a scoped
milestone review; it does not reconcile or close the full inventory.

The reviewed implementation is `Freezing1/SIRStrongCounts.lean`, with its
actual `SIRCountLaw` and `SIRCounts` dependencies. Independently reconstructed
statements and boundary examples are in `SIRStrongCountsStatements.lean`.

## Exact statement reconstruction

For arbitrary nonnegative per-pair rates satisfying
$n\lambda_n\to+\infty$, every $\varepsilon>0$ satisfies

$$
\Pr\left(\exists t\in[0,2]:
\left|\frac{I^n_{\lfloor nt\rfloor}}n-\min(t,2-t)\right|
\ge\varepsilon\right)\longrightarrow0.
$$

Here the law is the actual full stopped chain `countsFullLaw (rate n) n`,
starting with $n$ susceptible individuals and one infectious root. The
independent statement probe expands it as
`CountableMarkovChain.fullLaw (countsKernel (rate n)) (initialCounts n)`.
The source ratio premise $\lambda_n/(1/n)\to+\infty$ is also checked directly
through its proved equivalence to the scaled premise. There is no assumption
$\lambda_n\to\infty$, no monotonicity of the rate sequence, and no conditioning
on survival. The constant per-pair rate one is checked as an example.

| Item checked | Finding |
| --- | --- |
| Time interval and time change | Actual real times $t\in[0,2]$, with $\lfloor nt\rfloor$, not a finite list of fixed times or only the interval $[0,1]$. |
| Scaling and profile | Infectious count is divided by $n$; the target is exactly $\min(t,2-t)$ on $[0,2]$. No extra normalization or survival factor appears. |
| Stopping | `countsFullLaw` holds at infectious zero. The estimates include held steps after early extinction; they do not replace the process by an unrestricted walk. |
| Uniform-event measurability | The real-time error event is proved Borel measurable by its dependence on finitely many path observations. |
| Initial endpoint | The infectious root gives error $1/n$ at time zero. This is explicitly checked. |
| Final endpoint | At time $2n$ there can still be one infective; the probe proves the bound $I^n_{2n}\le1$. Extinction at $2n$ is not assumed. The separate terminal horizon is $2n+1$. |

The event formulation controls the uniform topology on the entire real
interval, since it applies to every positive error threshold. A continuous
path carrier is not imposed on the approximating step functions.

## Checked proof dependencies and departure

The implementation replaces the source's simple-walk coupling route by a
direct kernel estimate. For $0\le r\le1$ with
$r\lambda_n(n-m)\ge1$, the weight $r^I$ is superharmonic for every actual
state reachable through the early horizon $m$. This is proved from the
infection/recovery kernel, using the true susceptible lower bound, then
iterated under the actual full path law. It yields the unconditional bound

$$
\Pr(I^n_m=0)\le\frac1{\lambda_n(n-m)}
$$

when the denominator is at least one. There is no assumed independence of
successive infection signs.

The statistic `missedInfections` counts every step that does not consume a
susceptible individual. It includes both recoveries and held steps after
early absorption. Its expectation is bounded by

$$
m\left(\frac1{1+\lambda_n(n-m)}+r\right).
$$

Thus the estimate already pays for the possibility of early extinction.
The pathwise identity relating susceptible count to missed infections is
proved on legal histories, rather than assumed for an unrestricted walk.

The second deterministic ingredient is the actual full-grid bound

$$
\left|I^n_k-\min(k,2n-k)\right|\le2U^n_m+1,
\qquad 0\le k\le2n,\quad m\le n.
$$

Its proof checks the potential bound, the pre-extinction count identity,
absorption persistence and the one-step drop bounds. It also applies to paths
that became extinct before the comparison time. Choosing
$m=n-\lceil dn\rceil$ retains infection pressure of order $dn\lambda_n$, which
diverges. Markov's inequality and the expected susceptible bound give a
limiting error probability at most a constant times $d/\varepsilon$.
Letting $d$ decrease to zero proves uniform grid convergence. The triangular
profile is Lipschitz with constant one, and the proved rounding bound is
$1/n$; these transfer the estimate to the full real interval $[0,2]$.

This route verifies the source's absolute first-half fluid conclusion and
its extension to the descending second half. It bypasses the printed random
walk coupling and does not certify that coupling as checked. It keeps the
actual per-pair rate throughout and uses no unproved fluid or noise
convergence hypothesis.

## Explicit remaining obligations

- A79's separate relative startup estimate, uniformly for
  $\log\log n\le k\le(1-\delta)n$, remains open. An absolute error divided by
  $n$ does not establish the relative error divided by $k$ near the lower
  cutoff. This audit does not use or certify that estimate.
- The identification of the independently specified physical exponential/
  Poisson epidemic with the constructed embedded chain is still the A65/A66
  boundary. T07.II.a is proved for the genuine embedded count law, not yet
  fully transferred to that independent physical construction.
- Uniform-vertex height, conditional independent-pair distance and maximum
  height in T07.II.b are not consequences of this file alone. Their sampling,
  startup, truncation and late-time dependencies remain in the full inventory.

## Current proof evidence

The independent command
`lake env lean -DautoImplicit=false verification/SIRStrongCountsStatements.lean`
passes with only its requested axiom output. Retained evidence is
`sir-strong-counts-statements.log`: all eleven probed closures contain exactly
`propext`, `Classical.choice` and `Quot.sound`. The implementation author's
direct check also passed without diagnostics; its independent evidence is
`sir-strong-counts-direct.log` and `sir-strong-counts-axioms.log`. Root Lake
integration is recorded separately from this statement reconstruction.
