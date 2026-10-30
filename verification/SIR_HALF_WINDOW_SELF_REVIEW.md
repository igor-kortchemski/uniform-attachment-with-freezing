# Corrected SIR half-window reduction: implementing self-review

This root-authored extension concerns source lines 2275–2285. The printed
index equality is already formally refuted in the independently audited
`SIRReversedHeightIdentity`; it remains false. The new argument uses the
correct pre-step charge, represented by the actual susceptible decrease
and reciprocal infectious population before the event.

`SIRCountsExtinctionIndex` defines a total measurable minimum of a zero
or the deterministic horizon $2n+1$. The actual counts law is proved to
be absorbed by that horizon. Consequently the defined index is almost
surely the genuine first zero, with strictly positive infectious count
at every earlier time. The cap is a totalization with proved correctness
on the actual law, not an added stopping or support assumption.

`SIRReverseHalfWindow` splits the corrected full charge at
$\tau-\min(\lfloor n/2\rfloor,\tau-n)$. It proves the exact reverse
sum of the last part, with precisely the source's number of indices.
Early extinction and empty intervals are included.

On a triangle-fluid good event with error below $n/8$, the early
remainder is at most $16$, uniformly over every endpoint at most
$2n+1$. Its times lie before approximately $3n/2+2$, where the triangle
profile gives an infectious population at least $n/8$. Each charge is
then at most $8/n$, and there are at most $2n$ terms. The actual
strong-infection fluid theorem shows that the normalized early remainder
vanishes in probability, uniformly over every possible endpoint.

The actual first-zero specialization and the deterministic splitting
prove the source sufficiency reduction for the corrected charge: if the normalized last half-window
vanishes in probability, so does the whole corrected late charge. The
last-window convergence is the hypothesis of this sufficiency statement,
not a claimed proof of the still-open reverse iid coupling. No forward
late-charge budget estimate is invoked to certify this source reduction.

The actual-file check passed with exit zero before a style-only cleanup.
The current focused artifact build passes 3,948 jobs in
`sir-half-window-reverse-word-build.log`. The author probe is
`SIRHalfWindowStatements.lean`. This is explicitly implementing self-review;
independent review has been assigned. A85's epidemic coupling and A86's
localized reverse expectation remain distinct obligations.
