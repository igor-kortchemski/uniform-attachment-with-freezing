# Terminal strong-regime maximum: proof record

Date: 29 October 2026. Implemented modules: `ForwardCutMaximum.lean`,
`SIRLateMaximumWord.lean`, `SIRLateMaximum.lean`,
`SIRTerminalPrefixMaximum.lean`, and `MainSIRStrongMaximum.lean`.
This is an implementation proof record; the independent changed-statement
audit is separate.

The conclusion proved for the actual stopped embedded infection-tree law is

$$
n\lambda_n\longrightarrow\infty
\quad\Longrightarrow\quad
\Pr\left(\varepsilon\le
\left|\frac{\operatorname{Height}(\mathscr T^n)}{\log n}-e\right|\right)
\longrightarrow0,
\qquad\varepsilon>0.
$$

The final theorem is `SIR.sir_terminal_maximum_tendsto`. It observes the raw
plane-state vertex maximum at event time $2n+1$ under the constructed
`treeFullLaw`. The imported absorption theorem proves that this is a terminal
state and that the entire actual state is held afterwards. The wrapper
`sir_terminal_maximum_of_source_ratio` uses exactly the source condition
$\lambda_n/(1/n)\to\infty$. No rate, noise, height, or survival convergence
conclusion is included as an additional hypothesis.

Source arguments checked: the strong height conclusion at line 2103;
the time-$n$ maximum reduction and late attachment sum at lines 2247–2257;
the late reciprocal remainder and reversed-walk proof at lines 2275–2322;
and the final conditional-height/Bennett argument at lines 2326–2331 of
`attachement-uniforme-1-final.tex`. The time-$n$ maximum theorem and its
relative-startup dependencies are supplied by the separate strong random
environment chain. The earlier A83 and accumulated-charge replacements are
recorded in `SIR_LATE_PROBABILITY_PROOF.md` and
`SIR_LATE_ATTACHMENT_PROOF.md`.

For a deterministic schedule $x$, let $H_k$ be its proved height scale and
$C_a(s)$ the maximum number of ancestral edges above the canonical cut at
event $a$. The true forward kernel gives an exponential sum bound, hence

$$
\Pr_x(C_a(T)\ge L)
\le (T+1)e^\theta
\exp\left((H_T-H_a)(e^\theta-1)-\theta L\right),
\qquad \theta\ge0,\quad a\le T\le\tau(x).
$$

This bound includes the actual extinction event $T=\tau(x)$. The proof
iterates the all-vertex exponential sum, using the active mean only at the
preceding alive state. It does not invoke an active mean at a state with no
active vertices. For terminal words extinguished before $a$, the cut height
is identically zero. The deterministic comparison is

$$
\operatorname{Height}(\operatorname{truncate}_a s)
\le\operatorname{Height}(s)
\le\operatorname{Height}(\operatorname{truncate}_a s)+C_a(s).
$$

The scalar bridge is proved for the actual feasible adaptive word. Its
capped count history obeys the true legal count transition at each index.
The first zero of its infectious count is proved to equal the deterministic
schedule extinction time, including equality at that first zero. For an
actual transition $C_j\to C_{j+1}$, the post-birth height-scale reciprocal is
dominated by the previously proved charge

$$
\frac{\mathbf1_{\{C_{j+1}.U<C_j.U\}}}{C_{j+1}.I}
\le
q(C_j,C_{j+1})
=\frac{\mathbf1_{\{C_{j+1}.U<C_j.U\}}}{C_j.I}.
$$

The charged sign is $x_{j+1}$, with its matching post-birth infectious
denominator. There are no walk increments after actual extinction in this
comparison. Exact count-prefix pushforward identifies the adaptive word
charge with the true stopped count-history charge, whose post-$n$ sum is
$o(\log n)$ in probability.

On a word with charge at most $\delta\log n$, take
$\theta=4/\eta$ and $\delta=(e^\theta-1)^{-1}$. The cut tail at
$L=\eta\log n$ is bounded by
$2e^\theta(n^{-2}+n^{-3})$. The complementary word probability tends to
zero by the actual charge theorem. Integration against the genuine adaptive
terminal-word law therefore proves $C_n/\log n\to0$ in probability.

The terminal-word mixture's earlier truncated maximum is identified with
the actual time-$n$ maximum. This uses the exact longer-word projectivity
theorem from `SIRRandomEnvironmentTransferPrefix.lean` and a separate
extinct-before-cut argument. It does not infer a joint law from two marginal
laws. The two deterministic height bounds give a union bound by the earlier
maximum's $\varepsilon/2$ deviation and a cut height of at least
$(\varepsilon/2)\log n$. Both probabilities tend to zero.

This is a substantive proof departure. The implemented forward exponential
sum and exact word-mixture argument replace the printed conditional
coalescence/Bennett argument. The source's future-conditioned reversed iid
domination and shifted reciprocal identity are not certified by this proof.
The physical Poisson-contact-process identification remains separate from
this embedded-model result, as do other source obligations outside this
height chain.

All five modules pass direct Lean checking with `autoImplicit=false` and no
diagnostics. The direct logs are `forward-cut-maximum-direct.log`,
`sir-late-maximum-word-direct.log`, `sir-late-maximum-direct.log`,
`sir-terminal-prefix-maximum-direct.log`, and
`main-sir-strong-maximum-direct.log`. The twelve probed dependency closures
in `sir-late-maximum-axioms.log` contain exactly `propext`,
`Classical.choice`, and `Quot.sound`. The final wrapper closures are checked
in `main-sir-strong-maximum-axioms.log`; root integration and independent
statement reconstruction are recorded separately.
