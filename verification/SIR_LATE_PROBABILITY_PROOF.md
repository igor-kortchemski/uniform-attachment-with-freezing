# Late SIR infection probabilities: proof record

Date: 29 October 2026. Scope: A83, the displayed transition-probability
convergence at source lines 2258–2276, and its monotonic extension.
Source: `attachement-uniforme-1-final.tex`, SHA-256
`88953dd87165a14b0e643c5b3d0075d8ce5ec39cdcfc0c25d313570fc3ab00df`.
This records the implementation route; it is not an independent statement
audit or a declaration of complete source coverage.

`SIRLateInfectionProbability.lean` proves, for general nonnegative rates with
$n\lambda_n\to+\infty$ and every fixed $\varepsilon>0$,

$$
\Pr\left(\exists k\ge\lfloor3n/2\rfloor:
\frac{\lambda_n U^n_k}{1+\lambda_n U^n_k}\ge\varepsilon\right)\longrightarrow0.
$$

The law is the actual constructed stopped `countsFullLaw`. This implies the
source's supremum statement through time $2n$ and proves the stronger uniform
statement over the entire subsequent history. The literal rational formula
and real-time floor are exposed in
`countsFullLaw_infection_pressure_after_three_halves_tendsto_zero`.

The source monotonicity argument is checked directly: susceptible counts are
antitone on every legal stopped history, including after absorption. The
infection probability is increasing in the susceptible coordinate, so its
late supremum has the same event probability as its value at
$\lfloor3n/2\rfloor$.

The convergence proof deliberately replaces the source's future-event walk
coupling. The proved strong stopped fluid limit and valid population bound
first yield $U^n_n/n\to0$ in probability, and show that infectious extinction
by $\lfloor3n/2\rfloor$ has probability tending to zero. On the actual
stopped/unstopped joint law, survival at that time gives equality of the
stopped and auxiliary susceptible coordinates there and at time $n$.
The auxiliary susceptible path is antitone under its actual full marginal.
If its late infection probability is at least $\varepsilon$, all intermediate
infection probabilities are at least $\varepsilon$.

Writing $M$ for the actual accumulated centered noise, the exact finite-sum
identity proves

$$
(b-a)\varepsilon\le U_a+|M_b|+|M_a|
$$

on any such interval $[a,b]$. With $a=n$ and
$b=n+\lfloor n/2\rfloor=\lfloor3n/2\rfloor$, for $n\ge2$ a large late
infection probability therefore forces at least one of three events:

- $U^n_n\ge\varepsilon n/16$;
- infectious extinction by $b$;
- $\max_{k\le2n}|M_k|\ge\varepsilon n/16$.

All three actual probabilities tend to zero. The last convergence is the
proved uniform noise concentration for the genuine unstopped kernel and
holds for arbitrary varying rates. Exact complete marginal identities
project the conclusion back to the stopped count law.

No independent-sign or reverse-time domination assumption is added. The
argument does not justify the source's later conditioning on the future
transition event or its reversed iid coupling (S14). The later harmonic sum,
height comparison, and main T07.II.b results still need their own proofs.
The physical exponential/Poisson-process identification is also separate.

The standalone direct check passes without diagnostics; evidence is retained
in `sir-late-infection-probability-direct.log`. All eight relevant axiom closures use exactly `propext`, `Classical.choice`
and `Quot.sound`; evidence is retained in
`sir-late-infection-probability-axioms.log`. Root Lake integration is recorded
separately.
