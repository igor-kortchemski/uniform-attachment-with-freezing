# Independent review of the reversed SIR height identity

This checks source lines 2253 and 2275–2285 against the root-authored
`SIRReversedHeightIdentity`. The reviewer did not author that module.
The formal reversal is deterministic algebra; it makes no assertion
about independence under a future-conditioned epidemic event.

The corrected forward pre-step charge is

$$
\sum_{n\leq i<\tau}\frac{1}{I_i}\mathbf 1_{\{X_{i+1}=1\}}.
$$

The proved substitution $j=\tau-i$ identifies it exactly with

$$
\sum_{1\leq j\leq\tau-n}
\frac{1}{I_{\tau-j}}\mathbf 1_{\{X_{\tau-j+1}=1\}}.
$$

The finite-set bijection handles all natural $n,\tau$, including empty
intervals. There is no assumption that the printed differently indexed
sum already agrees with this charge. Natural subtraction is used only
inside the indicated intervals, where the proof establishes its bounds.

If `activeCount x τ = 0` and $i\leq\tau$, the module also proves

$$
\sum_{0\leq j<i}-X_{\tau-j}=I_{\tau-i}.
$$

The sums and active populations in this identity are integers. It
follows by the exact active-count recurrence, without truncating a
negative value or importing a reversed stochastic law. Reindexing the
sum gives precisely the source's reversed increments and partial sums.

The source definition at line 2253 instead uses $X_i$ with denominator
$I_i$. It cannot equal the displayed reversed sum. The actual feasible
three-event SIR word $(+,-,-)$ starts with one susceptible individual
and has populations $1,2,1,0$. At $n=1,\tau=3$, the printed forward
sum is $1/2$ while the printed reversed sum is zero. Feasibility is
proved through `SignWordFeasible`, and the module proves the exact
equality between its example sequence and `wordSchedule` of this finite
word. Thus the counterexample is not merely an arbitrary scalar path.
The independent probe reconstructs the failure directly with the
`wordSchedule` expression.

This establishes the corrected reindexing identity and refutes the
literal differently indexed equality. It does not establish the
subsequent reduction to the last half-window. It also does not establish
the claimed iid domination after conditioning on a future hazard event.
Those source arguments remain **open**. The already proved main
late-height bounds use the separate forward potential/martingale route;
this algebra does not certify the printed stochastic shortcut.

The refreshed artifact, including the exact `wordSchedule` equality,
passes the root 3,945-job build in `sir-reversed-height-identity-build.log`.
The probe `SIRReversedHeightIndependentStatements.lean` passes its
actual-import direct check with exit zero, four expanded examples and
five axiom queries. Every closure uses only `propext`, `Classical.choice`
and `Quot.sound`, or a subset. The durable output is
`sir-reversed-height-independent-statements.log`.
