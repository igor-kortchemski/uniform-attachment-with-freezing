# Manuscript recommendations

Source: [attachement-uniforme-1-final.tex](attachement-uniforme-1-final.tex).

The manuscript is unchanged. The complete correctness findings S01–S19 and
their evidence are in [FORMALIZATION_REPORT.md](FORMALIZATION_REPORT.md).

| Priority | Source | Recommendation and evidence | Status |
| --- | --- | --- | --- |
| Correctness | `lem:loiTn`, lines 670–674 | Restrict the tree class to labels compatible with the fixed schedule. S01 gives probability $0$ versus the claimed $1/6$. | Correction needed |
| Correctness | Coalescence law, lines 620–626 | Require distinct vertices and separately treat equal uniform samples. S02 gives probability $0$ versus $1$. | Correction needed |
| Correctness | `prop:bounds`, lines 1200–1211 | The upper bound fails at $n=1$, $t=1/4$. Use the actual vertex count or $n+1$ in the union bound, then recheck its downstream use. S16 has a Lean certificate for the actual reverse random-tree law. | Correction needed |
| Correctness | Uniform-block proof, lines 1322–1328 | The displayed geometric partition can fail when there is no complete block: $a=2,b=3,\beta=4$ is a counterexample. Restrict $1<\beta<C$ when $aC<b$ before sending $\beta\downarrow1$. | Original partition not certified; see S15 |
| Correctness | `eq:c0`, lines 1856–1867 | Restrict the lower linear bound to the controlled range $i\ge A_n$; long alternating prefixes contradict the printed full range. | Correction needed |
| Correctness | Local proof, lines 902–906 | Forward selection uses $S_{n-1}$, not $S_n$; prove the reciprocal-series comparison after fixing the products. | Proof repair needed |
| Correctness | SIR proof, lines 2181 and 2295 | Retain the drift error from $n\lambda_n\to\lambda$; justify the separate reversed-path coupling. | Substantive proof obligations |
| Correctness | SIR Grönwall criterion, lines 2162–2176 | Replace the future global maximum in the drift hypothesis by an adapted current or past bound and retain initial control. Even $X_k^n=k$ with $X_0^n=0$ satisfies the printed scalar bounds but has normalized maximum $1$. See S18 and `SIRSourceChecks`. | Printed criterion refuted; corrected fluid proof established |
| Correctness | SIR extinction comparison, line 2158 | Compare hitting zero or the nonpositive integers. Starting at $1$, the supercritical biased walk hits zero with probability $1/\lambda$, whereas hitting the negative integers has probability $1/\lambda^2$. | Wording correction needed; see S19 |
| Correctness | Binary-tree example, line 745 and figure caption | Replace $\mathfrak B_{4,15}^+$ by $\mathfrak B_{4,8}^+$. Its second parameter counts leaves; the displayed image has fifteen vertices. The named class with second parameter fifteen would have twenty-nine. | Formal size contradiction; see S20 |
| Correctness | Random-mean complement, line 1423 | Begin the equality for $h_n^+-M_n$ strictly after the birth cutoff. The term at the cutoff is already included in $M_n$; the larger inclusive sum can still serve as an upper bound. | Correction needed; see S21 |
| Clarity | Introduction line 311 | Correct the reversed signs in the summary of Algorithm 2 to agree with its precise definition. | Editorial correction needed |
| Clarity | Birth-law proof line 611 | Conditional frozen birth time is uniform on labels shifted by one, not on the unshifted labels. The Lean law implements the correct shift. | Counting proof checked |
| Exposition | Lower bound lines 1235–1242 | A direct count comparison gives the harmonic bound without adjacent swaps. This is the implemented proof; the swap argument remains unchecked. | Optional alternative proof |
| Exposition | Uniform-block estimate, lines 1311–1378 | Abel summation of $S_i-ci$ gives the exact statement with an explicit uniform endpoint error, avoiding geometric subdivisions. | Alternative proof formalized |

The remaining findings include integer rounding in strict Poisson tails,
moment estimates for noninteger powers, and missing zero-mean cases. They remain
visible in the coverage report and have not been silently repaired in the TeX.

See the original [template](.agents/templates/MANUSCRIPT_RECOMMENDATIONS.md)
and [attribution](.agents/skill-notices/lean-palomar-skills-updated/ATTRIBUTION.md).

The cut-forest definition should distinguish genuine activity from the marked-root convention. A marked root frozen after the lower cut contributes one to the convention-based count but zero to the urn population. The component-size argument needs explicit slack for this unit correction. The parenthetical characterization of the active set should also include the initial root at time zero, and the matching description should use the active vertices at the lower cut time. Retaining each root's freezing clock makes full labelled-state reconstruction by a fresh uniform matching valid. If those clocks are erased by the bare all-star convention, matching alone loses the true root labels/activity: the strictly surviving schedule $(+1,-1)$ at cuts 1 and 2 gives a formal counterexample. State the full reconstruction for the augmented forest and derive the required bare-forest observable formulas separately. These issues are retained as S17 in the coverage report.


## Geometric-block and finite good-index corrections — 30 October 2026

In the proof of L08, choose $1<\beta<C$ before the partition, under the
existing condition $aC<b$. Form every interval with its actual integer
cutoffs. The last partial block needs the bound
$(\beta-1+1/A_n)/(c-\eta_n(\varepsilon))$; the integer count can exceed
the real geometric length. Its intermediate denominator is $\beta^m$,
not $\beta^{\ell-1}$. The corrected endpoint term still vanishes in
the required limits. State eventual nonnegativity of $L_n$ before
multiplying by its lower block-count estimate. The formal counterexamples
and repaired proof are detailed in the A37–A38 audit and S15.

The finite cumulative-good definition uses positive indices. Its exact
lower cutoff is $\max(1,\lceil\log A_n/\log C\rceil)$; the simpler
ceiling agrees eventually because $A_n\to\infty$. This preserves the
source definition also in initial rows with $A_n\le1$. In the conditional
growth argument, retain the true $S_a\le a+1$. For $a\ge3$ the favorable
mean is at least three times the target, and conditional Chebyshev yields
a sufficient bound $3k^3/2^k$, with the same required asymptotic order.


## Poisson polynomial proof corrections — 30 October 2026

The real bound $\lceil u\rceil!\le u^3(u/e)^u$ is false at $u=21/10$.
The desired cubic strict-tail bound remains true for every $\lambda>2,t>1$;
a valid proof uses the singleton $\lfloor\lambda t\rfloor+1$, and handles
$2<\lambda t<3$ separately. Supply the sufficiently large choice
$\log C\ge(Kt)^3$ when converting the cubic prefactor to $\log(C)^{-4}$.

The displayed positive rate slack also needs $1<f(c)-\eta$. For a general
positive margin, use the auxiliary threshold
$t=\max((f(c)+1)/2,f(c)-\eta)$, with $1<t<f(c)$, and use monotonicity
of the actual Poisson tail to retain the original event. The original slack
is formally negative for an admissible $f(c)=5/4$, $\eta=3/4$. The exact
statements and counterexamples are in S22/S23 and the independent A56 audit.


## Observations from the examples, intrinsic class and late-height steps — 30 October 2026

Examples (second bullet, $\tau=n$). The conditional uniform plane tree is exact for the
chronological plane order, for every success probability $p\in(0,1)$, because every finite plane tree with
$m$ vertices has the same limit mass $(1-p)^m p^{m-1}$; only odd $n=2m-1$ have positive probability.
Saying "when the plane order is chosen uniformly at random" is then a consequence (the uniform law is
invariant under independent uniform sibling permutations), not an extra hypothesis.

Section on increasing trees. The statement that $\mathfrak T^+_{k,n}$ is the set of trees obtainable by
Algorithm 1 holds as a union over all schedules; for a fixed schedule only schedule-compatible trees have
positive probability, so the sentence before Lemma `loiTn` should say "for some schedule".

Late-height argument. The height of a vertex born at time $m>n$ is stochastically $H+1+\sum_i B_i$ with $B_i$
independent Bernoulli$(1/S_{i})$ at attachment steps; the deterministic $+1$ (the vertex itself) is absent from the
printed domination, and the parameter indices should be those of the post-step active count.

Pólya lemma. The hypothesis conditions the increments on $U_n$ alone, which does not make $(U_n)$ a Markov
chain, while the maximal inequality needs the transitions given the whole past (or an explicit Markov
hypothesis). Heuristically, pairwise-martingale processes with the same one-time marginals can decorrelate across
logarithmic time scales because $\sum 1/Z_n=\infty$ even though $\sum 1/Z_n^2<\infty$; this is not a formal counterexample.
In the applications the full path law is proved, so stating it as the hypothesis is harmless.
