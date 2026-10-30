# Main local results: independent audit of the full ambient bridge

The integrating reviewer independently reconstructed the local topology
definition at source lines 882–889 and the Introduction's T01–T02 local
claims. The reviewer then read the full chronological labels, vertex
equivalence, graph geometry, ball records/isomorphisms, closed embedding,
law transport and `MainLocalAmbient` consumers. The reviewer did not
author those tree-bridge modules. The reusable probability-law transport
lemma was written by the reviewer and retains separate self-review
provenance; the namespace-wide axiom audit covers it.

The target ambient is the previously independently reviewed A20 space
of all unordered rooted locally finite trees with natural edge labels
and natural-or-active vertex labels. Repeated labels and trees outside
chronological support remain in that ambient. The embedding is derived
from actual children sorted by birth ID. Its incoming edge label is
exactly that ID and its vertex label is exactly the original frozen-time
or active label. Auxiliary graph IDs do not replace either label.
An active vertex has an occupied label slot containing the active symbol,
distinguished from an absent vertex slot.

The address-to-original-vertex map is bijective. Heights equal address
lengths, roots have birth zero, and actual parent relations recover the
parent field. In each radius ball, genuine unordered labelled graph
isomorphism preserves birth IDs through incoming edge labels, frozen
labels through vertex labels, height through root distance, and parents
through the rooted graph. Consequently it preserves every chronological
record. Conversely equality of record balls supplies an actual labelled
ball isomorphism. This proves equality of the two finite observations at
the SAME radius, including zero, without an assumed encoding reflection.

The embedding therefore preserves and reflects convergence. Its image
is also proved closed: an ambient tree whose every finite ball lies in
the image determines unique chronological record balls. Restriction and
the same-radius equivalence prove their coherence. Those records define
an actual chronological tree whose image has all the required ambient
balls, hence is the original ambient point. Closedness is not a support
or chronological-law premise.

For probability laws, pushforward by a closed embedding is a closed
embedding in the weak topology. The generic proof identifies its range
with laws supported on the closed image; Portmanteau proves that set
closed. An arbitrary ambient weak limit of chronological laws therefore
has a chronological preimage, and convergence reflects to that preimage.
No support assumption is imposed on the limiting law.

`source_local_convergence_equivalences` has the Introduction's three
conditions in the full unordered ambient, with the same fixed-schedule
nonextinction and coordinatewise eventual agreement assumptions and no
nonextinction assumption on approximating rows.
`source_local_convergence_common_limit` retains one measurable limiting
tree and the same law for the fixed and diagonal sequences. The iid
wrapper retains every parameter below one, the actual full iid-sign
history, absorption and the same geometric plane-tree limit, including
the zero parameter. It does not assert that arbitrary ambient trees
possess chronological order.

The independent `ChronologicalAmbientIndependentStatements.lean`
reconstructs six exact types and queries seven axiom closures. It passes
with exit zero in `chronological-ambient-independent-statements.log`;
only the three permitted axioms occur. The separate authored imported
probe has nine examples and fifteen closures. The final focused build
passes 4,142 jobs in `ambient-positive-urn-poisson-reverse-build.log`.

No semantic mismatch or unproved encoding/support premise was found.
This closes the additional A20/main-model representation dependency
identified at the prior milestone. The previously recorded corrections
and proof departures in T01–T02 are retained. This audit does not certify
whole-paper coverage, Comparator equality or publication verification.
