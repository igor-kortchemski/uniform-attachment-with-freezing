# A77: independent audit of the exact capture coefficient

The integrating reviewer independently read source lines 2199–2203 and
the new capture analytic/count/probability/word/law/observed/native modules,
their source-ratio wrappers and the two reverse-sample interface. The
reviewer authored `CanonicalReverseBirthClock`, so that dependency is not
represented as independently reviewed here. The capture author separately
reviewed its full uniform-bijection and freezing-label transport.

The final bound keeps the same $\varepsilon$ in the cutoff
$(t_0-\varepsilon)n$ and the error $1-\varepsilon$, for every
$0<\varepsilon<t_0$. It uses the genuine unconditional epidemic law.
It does not assume a major-outbreak condition or a terminal capture estimate.

The strict scalar slack is $2(1-1/\lambda)<t_0$, derived from the fluid
profile at extinction being below $1/\lambda$. It supplies constants
$d>t_0$, $0<b<t_0/2$ and $a>d-(t_0-\varepsilon)$ with
$(1-1/\lambda)a/b<\varepsilon$. These constants are chosen before the
eventual size window. For any $b<t_0/2$, the actual probability of being
alive at the cutoff but having fewer than $bn$ terminal vertices tends to
zero: choose a later pre-extinction fluid time above both the cutoff and
$2b$, then use survival-gate agreement and the deterministic event-count
lower bound on terminal cardinality. Thus no surviving-branch coefficient
is incorrectly substituted for the unconditional coefficient.

Actual recovered counts increase by at most one per event. The reverse
missing fraction is bounded by late event count divided by terminal size,
and is zero if the prefix is already extinct. Integrating the genuine
gate/terminal-size/deadline bounds yields eventual expected missing
fraction strictly below $\varepsilon$. All three error probabilities
and the gate's exact survival weight are proved from the original count law.

The word bridge identifies the true first zero, recovery labels and
terminal cardinality, then gives the exact uniform reverse-label tail.
All positive-probability adaptive words use this genuine law. The unused
infeasible-word completion is a probability measure and is outside almost
sure support; it is not used as a mathematical default at an actual word.

The observed law samples all vertices of the original terminal forward
tree using its native freezing-label-minus-one clock at true extinction.
The full law, including absorption, equals the reverse-label sampling law.
This clock is distinct from chronological birth. Their order, proved on
actual histories, transfers capture to chronological prefix membership.
The native plane-tree history version also directly identifies capture
probability with one minus the actual missing vertex fraction, using the
complete actual count-history projection.

Both pair interfaces sample two independent uniform vertices conditionally
on the same tree before mixing. They include the diagonal pair and prove
the two true marginal probabilities equal, with the same bound. They do
not assert independence after mixing over the tree. The source-ratio
wrappers preserve the literal rate hypothesis. The separate pair semantic
review is retained in `SIR_CAPTURE_PAIR_INDEPENDENT_AUDIT.md`.

`SIRCaptureCoefficientIndependentStatements.lean` reconstructs seven exact
types, expanding the actual forward frozen-clock sampler and native
prefix-membership sampler, and retaining the literal two reverse-birth
marginal equality. Its ordinary imported check passes with exit zero:
`sir-capture-coefficient-independent-statements.log`, fifteen permitted
axiom closures. The separately authored imported probe passes eight
examples/thirty-one closures. Focused artifact checks end in
`capture-source-pairs-one-susceptible-build.log` (4,114 jobs).

No extra capture premise or changed coefficient was found. The source's
brief invocation of the uniform birth lemma is supplemented by the proved
fluid survival/cardinality argument above. This closes the retained A77
capture obligations; it does not certify the later reversed iid coupling.
