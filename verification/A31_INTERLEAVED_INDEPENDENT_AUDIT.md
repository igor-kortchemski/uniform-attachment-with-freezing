# A31: independent audit of the source scalar factorizations

The integrating reviewer independently read source lines 1146–1161 and
the three new `InterleavedSource` modules. The reviewer did not author
these modules. The existing alternating kernel, path law, fairness and
minimum/fallback extraction semantics were checked against the source.

The literal first-right-selection event requires all previous positive
marks to select the left coordinate, followed by a right mark with the
requested value. Its probability is proved to be the probability of
ever selecting the right coordinate times the actual transition mass
from its starting state. This stronger identity needs no fairness or
independence-of-extracted-chains premise. Finite harmonic completion
expectations and bounded convergence retain the never-selected mass.
Fairness supplies eventual selection only at a nonabsorbing state.

For either coordinate, the displayed finite-cylinder recurrence and the
source restart-factor probability identity are exact numerical
equalities. The two-term absorbing formula retains the no-selection
probability, equality indicator and actual Dirac transition. Empty words
use their original starting states; null prefix events need no division.
The strictly later extraction time at nonabsorbing states is proved
almost surely using simultaneous pathwise fairness.

The source's double induction is not the formal proof order. The scalar
prefix recurrences follow from the previously established product-cylinder
law, whose proof uses harmonic completion. This verifies the displayed
mathematical identities without asserting an independent full Markov
restart at an asynchronous joint endpoint. That substantive departure
remains explicit; the first-selection identity itself does not depend on
the final product conclusion.

No extra factorization, positive-cylinder-mass or future-law hypothesis
was found. `A31InterleavedIndependentStatements.lean` has three expanded
examples and seven standard axiom closures, passing with exit zero in
`a31-interleaved-independent-statements.log`. The authored probe has six
examples/thirteen closures. The final focused build passes 3,126 jobs in
`interleaved-source-factorization-build.log`. This resolves the retained
scalar factorization obligation, with the proof-order distinction above.
