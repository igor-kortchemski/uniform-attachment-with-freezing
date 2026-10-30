# A37–A38: independent audit of the repaired geometric proof

The reviewer independently reconstructed source lines 1311–1378, then
read `IntervalFreezingCounts`, all six `GeometricHeight` proof/check
modules and the relevant source-limit definitions in
`LinearRegimeAssumptions` and `LinearRegimeUniform`. The reviewer did not
write these geometric modules.

The source conclusion is a nested limit: first the row limsup of the
maximum over every integer pair $A_n\le a<b\le\varepsilon n$ with
$aC<b$, then $\varepsilon\downarrow0$, for each fixed $C>1$. Its height
sum uses precisely the attachment steps and the post-step population.
The near-origin hypothesis controls the actual finite maximum of
$|S_i^n/i-c|$; the original standing positivity and $c\in(0,1]$ are
retained by the literal-source wrapper.

Both attachment/freezing count identities and EqProp9 are proved.
The repaired partition chooses $1<\beta<C$ and floors all geometric
cuts. The ceil/floor indices are ordered under $aC<b$, and the exact
integer partition permits empty complete blocks. This restriction does
not restrict the final theorem, since $\beta$ is an internal auxiliary
parameter that can still tend to one.

The complete-block estimates use the actual reciprocal-population sum
and exactly the source's rational constants $U_n$ and $L_n$, including
their rounding losses. Denominator positivity follows from
$0\le\eta<c$. Multiplication by the lower block-count bound explicitly
requires $L_n\ge0$; eventual positivity is proved from the actual source
maximum, not assumed in the final asymptotic theorem.

The last partial interval requires an additional $1/A_n$ term. The
proved aggregate upper endpoint error is
$[2(\beta-1)+1/A_n]/(c-\eta)$; normalization divides it by the positive
$\log C$. The initial endpoint bound and the refined lower endpoint
inequality are also checked. The extra term vanishes because
$A_n\to\infty$.

The limiting proof selects $\beta$ close to one using elementary exact
logarithm inequalities. Continuous rational envelopes then select a
single positive tolerance controlling both the row error and $1/A_n$.
The near-origin hypothesis supplies one cutoff and one eventual bound
for every integer interval in that window. This preserves the source's
uniform quantifiers and order of limits. The final theorem has no extra
partition, block estimate, sign or convergence hypothesis. It uses the
existing exact maximum and generic quantified-to-nested-limit conversion;
it does not call the earlier Abel estimate or its uniform theorem.

Three printed finite steps remain false: the unrestricted partition,
the last-block integer-count comparison without rounding, and the
intermediate last-block denominator indexed by the first rather than
last block. `GeometricHeightSourceChecks` proves actual counterexamples
for all three, including a surviving all-attachment schedule. These
counterexamples refute finite proof steps, not L08. The repaired geometric
strategy proves the original conclusion, and the report must preserve
that distinction.

`A37A38GeometricIndependentStatements.lean` reconstructs five types:
the signed count identity, the actual floor/ceil partition, the expanded
finite rational bounds, the fully quantified uniform conclusion, and the
literal nested-limit conclusion. Its ten axiom closures include the
three counterexamples and actual-max positivity. The direct check passed
without diagnostics in `a37-a38-geometric-independent-statements.log`;
all closures use only the three permitted axioms. Final source-consumer
artifact evidence is `geometric-uniform-probability-embedding-build.log`
(3,427 jobs), followed by the integrated default build (4,518 jobs).

No mismatch or extra mathematical premise was found in this corrected
scope. This is a scoped source audit, not a publication verification or
whole-paper coverage claim.
