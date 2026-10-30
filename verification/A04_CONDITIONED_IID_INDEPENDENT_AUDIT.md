# A04: independent audit of finite-survival-conditioned iid rows

The integrating reviewer independently reconstructed the claim at source
lines 342–343 and inspected the seven new deterministic, conditional-mixture
and iid-consumer modules. The reviewer did not author those modules.

The stronger introductory maximum condition supplies both literal nested
linear-regime assumptions. `UniformTailRatio` retains a single eventual
window uniformly in every eligible integer index, and is proved equivalent
to convergence of the full finite maximum. The bulk proof uses the prescribed
sublogarithmic cutoff to reach every macroscopic index. Survival through
each row's horizon remains the original standing assumption.

The probabilistic statement uses the actual iid sign law with
$1/2<p<1$. Its row event is exactly $\{\tau>n\}$, while the common survivor
event is exactly $\{\tau=\infty\}$. The latter has positive mass by the
proved supercritical extinction formula. Neither positive mass nor an
existing coupling is a new premise of the final theorem.

For decreasing events $E_n$, the exact conditional mixture uses the weight
$\mu(\bigcap_j E_j)/\mu(E_n)$ and the residual conditional law on
$E_n\setminus\bigcap_j E_j$. A zero residual uses a genuine probability
fallback with coefficient zero. The construction samples one common uniform
variable, one true survivor and a product of residual samples. Every entire
row has exactly $\mu(\,\cdot\mid E_n)$. Continuity from above gives weights
tending to one, so almost surely all sufficiently late whole rows equal
the same survivor. Conditioning transfers the genuine iid strong law to
that survivor. Uniform tail ratios above any prescribed diverging cutoff
then give the two literal source assumptions.

This is an existence coupling with exact finite-conditioned marginals. It
does not assert almost sure convergence for arbitrary couplings, including
independent rows. The source does not specify a joint law for the varying
conditional rows; this explicit interpretation and construction are retained
as a proof clarification. The source's main distributional application
can use this coupling. No iid property after survival conditioning is assumed.

`A04ConditionedIidIndependentStatements.lean` reconstructs four statements,
including the final existence theorem with the carrier, both conditional
events and literal nested limits expanded. Eleven closure queries use only
`propext`, `Classical.choice`, `Quot.sound`. Its ordinary imported check
passes with exit zero in `a04-conditioned-iid-independent-statements.log`.
The separately authored probe passes eight examples/fifteen closures.
Focused actual artifact evidence ends in
`iid-linear-conditioned-rows-build.log` (3,970 jobs).

No additional estimate or weakened conditioning was found in this scope.
The final whole-project checks and publication evidence remain separate.
