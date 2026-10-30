# A31: actual source factorization and its boundary cases

This is an authored proof record for source lines 1146–1161, following an
independent reconstruction of the displayed mathematical claims. It is
not an independent audit of the three new modules authored here.

The source's actual alternating kernel, complete Ionescu–Tulcea path law,
minimum/fallback extraction times and nonstarvation hypothesis are the
existing `InterleavedChain` objects. The new modules assume no conditional
factorization or independence premise. The initial mark is `true`, the
source mark one; the finite-cylinder recurrence is proved more generally
for either initial mark.

## First selection, including absence of a selection

`InterleavedSourceFirstSelection` defines `everSelected` using positive
times. Its `firstSelectionValue` event is proved equivalent to the
literal event that some positive time is the first requested mark and
the corresponding coordinate then has the specified value. Both events
are measurable. The source's right-selection event has all earlier
positive marks equal to one, followed by mark two; this exact form is
proved in `first_right_value_literal`.

The companion module `InterleavedSourceFirstSelectionLaw` proves

$$
\mathbb P(\text{first selected value}=z)
=\mathbb P(\text{some selection occurs})\,\alpha(a,z),
$$

where $a$ is the coordinate's actual starting state. This theorem does
**not** require fairness and does not use the already proved product law
of extracted chains. It starts from finite harmonic cylinder-completion
expectations. If a selection eventually occurs, the completion becomes
the first-value indicator. If no selection occurs, it stays at
$\alpha(a,z)$. Bounded convergence therefore retains the never-selected
mass explicitly. Probability mass conservation and finite cancellation
give the formula above. This also covers absorbing states and a scheduler
that never selects the coordinate.

The source's fairness assumption is then used only when $a$ is
nonabsorbing, to prove that the selection probability is one. The claimed
first-selected transition probability is consequently exactly
$\alpha(a,z)$, for either coordinate.

## The displayed asynchronous factorization

Let $B_{u,v}$ prescribe the two finite extracted future words $u,v$.
Their lengths may differ. The new `source_right_prefix_transition` and
`source_left_prefix_transition` prove the actual finite-cylinder
recurrences

$$
\mathbb P(B_{u,v},V_{s+1}=z)
=\mathbb P(B_{u,v})\alpha(y_s,z),
\qquad
\mathbb P(B_{u,v},U_{r+1}=z)
=\mathbb P(B_{u,v})\alpha(x_r,z).
$$

These follow from the independently established harmonic-completion
product-cylinder theorem and the elementary Markov-word append identity.
Combining them with the first-selection law proves exactly the source's
displayed factorization with the restarted first-selection probability
from $(x_r,y_s,1)$, for either nonabsorbing coordinate.

The numerical equality is thus checked. Its formal derivation does not
treat the asynchronous joint prefix as a stopping-time history, nor
assume a full conditional future-path restart from $(x_r,y_s,1)$. The
source's printed double-induction order is not reproduced: the existing
independent cylinder-completion proof establishes the product conclusion
first, and the displayed scalar identities are then verified as
consequences. This proof departure must remain explicit.

## Absorption, empty words and null events

For an absorbing last state, the two new
`source_*_factorization_absorbing` theorems give the two source terms:
the probability of no future selection times the equality indicator,
and the probability of a selection times the transition mass. The two
selection probabilities sum to one, and the absorbing transition is the
actual Dirac measure. No selection is required at an absorbing state;
the minimum/fallback convention is retained.

`never_right_selected_literal` identifies the complement selection event
with all positive marks being one, exactly the source's first term.
`fullLaw_selectedTime_strict_of_nonabsorbing` separately proves that the
next extraction time is strictly larger whenever the extracted state is
nonabsorbing, almost surely for every rank. This uses the actual
simultaneous pathwise fairness theorem, so evaluating it at a random
extraction time introduces no unstated stopping-time assumption.

Empty words are allowed. Their last states are read by `getLastD` using
the original initial state, giving the natural $x_0=x$, $y_0=y$
conventions missing from the printed subscript notation. Null prefix
events are also allowed: all identities are multiplicative probability
equalities and no division by a prefix probability is used.

## Evidence boundary

All three modules pass actual-file direct checking with zero diagnostics.
Current outputs are `interleaved-source-first-selection-direct.log`,
`interleaved-source-first-selection-law-direct.log` and
`interleaved-source-factorization-direct.log`. Their root artifact builds
pass 3,868, 3,802 and 3,126 jobs, respectively, in
`pair-coupling-source-urn-first-selection-build.log`,
`source-urn-tail-first-selection-law-build.log` and
`interleaved-source-factorization-build.log`.

The actual-import probe `InterleavedSourceFactorizationStatements.lean`
passes with six expanded examples and thirteen axiom queries. Every
closure uses exactly `propext`, `Classical.choice` and `Quot.sound`, or a
subset. The durable output is
`interleaved-source-factorization-statements.log`. An independent review
of the newly authored proofs is left to the root integration milestone.
No new assumption on the scheduler or the source chains is introduced,
and no artifact-writing build is run by this worker.
