# A77: the same-epsilon terminal capture coefficient

Source scope: `attachement-uniforme-1-final.tex`, lines 2199–2203, together with the reverse birth definition at line 576 and Lemma `lem:bunif`. This is an authored review of the capture proof, with an independent component review of the root-authored `CanonicalReverseBirthClock.lean`. It does not claim whole-paper coverage.

## Exact statement and range

For every finite infection parameter $\lambda>1$, every general rate sequence with $n\lambda_n\to\lambda$, and every fixed $0<\varepsilon<t_0$, the following bounds hold eventually:

$$
\mathbb P\!\left(\operatorname{birth}_{\tau'_n}(V)\leq (t_0-\varepsilon)n\right)\geq1-\varepsilon,
$$

and

$$
\mathbb P\!\left(V\in\mathcal T_{\lfloor(t_0-\varepsilon)n\rfloor}\right)\geq1-\varepsilon.
$$

The first vertex is conditionally uniform on the complete original terminal tree with its actual reverse freezing clock. The second statement is also proved directly for the native SIR plane-tree history and a uniform terminal vertex. Two conditionally independent uniform terminal vertices have equal capture marginals and satisfy the same bound. The product sampling includes diagonal vertex pairs.

The same $\varepsilon$ controls the cutoff and the error. This is stronger than the printed asymptotic lower bound on the entire meaningful positive-cutoff range $0<\varepsilon<t_0$. It does not silently replace that cutoff by a separate tolerance-dependent choice. No claim is made for the unqualified expression outside this range; the paragraph uses a small positive $\varepsilon$ to keep its truncation before the positive extinction time.

`SIRCaptureCoefficientSource.lean` supplies the literal source ratio hypothesis $\lambda_n/(\lambda/n)\to1$. No rate sequence is replaced by the special sequence $\lambda/n$.

## Why the unconditional coefficient is one

Write $s=1-1/\lambda$ for the actual major-outbreak limiting probability. The analytic proof establishes

$$
g_\lambda(t_0)<\frac1\lambda,
\qquad
t_0>2s.
$$

The positive fluid zero lies after the profile peak, where $g_\lambda=1/\lambda$. The strict inequality follows from the proved strict decrease of the susceptible profile; the zero equation $t_0=2(1-g_\lambda(t_0))$ gives the second inequality.

Fix $t=t_0-\varepsilon>0$. For every $b<t_0/2$, the actual probability of being alive at time $tn$ while having fewer than $bn$ terminal vertices tends to zero. This lower bound is **proved**, rather than assumed as final-size convergence. Choose a later fixed time $q\in(\max(t,2b),t_0)$. On survival at $qn$, the exact count identity gives at least $qn/2$ vertices up to rounding, and the terminal population is larger. The event alive at $tn$ but extinct at $qn$ has probability tending to zero because the two true pre-extinction survival probabilities tend to the same $s$.

Choose a deadline $d>t_0$, a constant $b<t_0/2$, and an absolute late-step bound $a>d-t$, so that

$$
s\,\frac{a}{b}<\varepsilon.
$$

The inequality $2s<t_0$ provides a strict margin for these choices, for every $0<\varepsilon<t_0$. By the actual post-fluid-zero extinction theorem, survival beyond $dn$ has vanishing probability. On extinction before that deadline, the number of newly recovered vertices after the prefix is at most the number of late event steps. Therefore the missing recovered fraction is at most $a/b$ on the alive-prefix gate and on the terminal-card good event. It is zero off the alive-prefix gate and at most one on every other history. Averaging gives

$$
\mathbb E[\text{missing recovered fraction}]
\leq \frac{a}{b}\,\mathbb P(I_{\lfloor tn\rfloor}>0)+o(1)
\longrightarrow s\frac{a}{b}<\varepsilon.
$$

This argument includes early-extinct histories. A conditional-major-outbreak coefficient is not substituted for the unconditional one. No independence between the survival gate, extinction deadline, terminal size, or sampled vertex is assumed.

## Reverse birth versus actual prefix membership

The source reverse birth is a freezing-time index minus one; it is not the forward infection time. `SIRCaptureCoefficientWordBirth` proves the exact label CDF at the true first-zero index from the actual feasible-word recursions. It counts recovered vertices at the prefix, while all prefix vertices count both recovered and infectious vertices. The reverse missing fraction therefore dominates the forward missing fraction.

The genuine adaptive word law has exactly the count-prefix law of `countsFullLaw`. This identifies the expected missing recovered fraction used above with the actual source label-law tail. The proof covers finite cutoffs after extinction as well as cutoffs before extinction. The final event with a real cutoff is bounded using the stronger strict integer CDF, so its floor and inequality endpoints are retained.

`SIRCaptureCoefficientObserved` transports that entire birth law to conditionally uniform vertices of the original forward terminal tree, observed through their actual freezing clocks. `actualTerminalVertexBirthLaw` retains the same vertex and its reverse clock jointly and proves that its chronological vertex ID is at most the reverse birth clock almost surely. Thus a captured reverse birth implies actual chronological capture; no event equality is assumed.

`SIRCaptureCoefficientNative` additionally constructs the sampler directly on `treeFullLaw`: choose uniformly among all actual terminal plane vertices and test membership in the earlier actual vertex set. Its probability is proved to be one minus the expected forward missing fraction using the genuine count-path projection and exact population/cardinality invariant. The two-sample law is a conditional product of these actual uniform sample kernels, with its exact product-map identity and equal marginals proved.

## Independent component review: reverse-clock law

The reviewer did not write `CanonicalReverseBirthClock.lean`. Its entire definition and proof were read against the source birth definition. Under the canonical timestamp bijection, every actual vertex retains its exact freezing label. Frozen label $j+1$ gives birth $j$; an active label has no freezing time and the explicit fallback $n+1$, minus one, gives birth $n$. The uniform bijection includes all vertices, and unused values outside the sampled vertex set play no role. The law identity is proved using the actual construction equivalence and actual deterministic reverse label law. Its terminal transport holds the tree after extinction while retaining the true extinction horizon in the clock. No conditional independence or hypothetical correspondence is an assumption. The bridge is faithful, including the extinction endpoint and the zero horizon.

## Coverage and evidence

The ten new `SIRCaptureCoefficient*.lean` components, including the source-ratio wrapper and exact two-reverse-clock observation law, formalize the formerly retained exact coefficient and reverse-birth justification. `SIRCaptureCoefficientObservedPairs` constructs both reverse clocks from independent uniform samples conditional on the same actual terminal tree and adaptive word; its two marginal laws are equal to the proved single-clock law. No unconditional independence of the sampled birth times is asserted. The previous main weak limits with tolerance-dependent cutoffs remain valid separate proofs; they are not relabelled as this exact estimate. The source's short appeal to Lemma `lem:bunif` omits the unconditional survival weighting and terminal-size margin; the explicit calculation above checks that required argument.

`SIRCaptureCoefficientStatements.lean` reconstructs eight expanded source-facing statements, including the actual samplers and root-authored clock bridge, and queries 31 axiom closures. The final ordinary imported direct check passes with exit zero and no diagnostics beyond the requested axiom output, recorded in `sir-capture-coefficient-statements.log`. All 31 closures contain exactly `propext`, `Classical.choice`, and `Quot.sound`. The earlier source-combined check remains recorded in `sir-capture-coefficient-source-statements.log`; it is superseded for module-import evidence by this ordinary imported check. Every maintained proof module was also checked directly, without artifact writes. Root artifact builds are current, including Source and ObservedPairs in the 4,114-job batch `capture-source-pairs-one-susceptible-build.log`.

The authored probe does not replace independent source review. Root independently checked the main capture theorem with six expanded examples and twelve axiom queries. The final literal reverse-clock pair lift independently passes the semantic review in `SIR_CAPTURE_PAIR_INDEPENDENT_AUDIT.md`: its conditional product is formed before word/tree mixing, both exact marginal laws are proved, and the source ratio and same-epsilon thresholds are retained. That independent semantic review and this authored imported probe have distinct provenance. Complete project/publication checks remain owned by the integrating agent. Other retained source arguments, including the separate reversed iid/localization claims, remain governed by `FORMALIZATION_REPORT.md`.

The focused integration and ordinary imported probe can be reproduced from the project directory by the sole artifact-build owner:

```sh
lake build Freezing1.SIRCaptureCoefficientSource Freezing1.SIRCaptureCoefficientObservedPairs
lake env lean -DautoImplicit=false verification/SIRCaptureCoefficientStatements.lean > verification/sir-capture-coefficient-statements.log 2>&1
```

No proof repair or focused-import check is pending for this A77 milestone. These checks do not constitute the project's complete publication verification.
