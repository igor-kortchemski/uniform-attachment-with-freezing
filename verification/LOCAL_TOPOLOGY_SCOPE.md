# A20 topology domains and proof record

Source checked: lines 882–889, with the paper's own Ulam–Harris plane-tree
definition at lines 927–935. This record distinguishes existing domains,
the new generic plane-labelled and unordered domains, and the separate
chronological-to-ambient transport needed by the main results. It does not concern the growing-history
degree/freezing arguments A21–A22.

The plane and unlabelled variant was already proved before this milestone.
`PlaneTree.lean` defines all locally finite plane shapes by canonical
offspring coordinates in a closed subset of a countable product of
discrete natural numbers, and proves Polishness. `PlaneTreeGeometry.lean`
identifies the nonempty prefix-closed Ulam–Harris tree, its actual children,
and its finite generations and balls. `PlaneTreeLocalTopology.lean` proves
that convergence is equivalent to eventual equality of every complete
finite ball. Offspring coordinates at an address can be recovered from the
next larger ball, including for absent addresses. This is the generic
unlabelled plane domain, not a chronological subclass.

`LocalTreeTopology.lean` and `LocalTreeGraph.lean` supply a different domain:
coherent finite balls with natural birth IDs, distinct IDs, and parents
with smaller birth IDs. Every element is decoded into a genuine connected,
acyclic, locally finite graph; its heights equal root distances, and its
stored balls are precisely the graph-distance balls. This proves the
assertions for the time-labelled domain used by the formalized growth
process. It is not, by itself, a representation of every arbitrarily
labelled unordered tree without chronological edge-label constraints.

The new `PlaneTreeLabelledTopology.lean` uses the existing complete plane
shape and independent vertex/incoming-edge label arrays. The vertex
alphabet $V$ and edge alphabet $E$ can be any countable types; their labels
have the discrete topology. The source alphabets of natural labels and
natural labels plus the active symbol are covered, in particular by
`Tree (Option ℕ) ℕ`.

Label slots distinguish an absent address from an actual vertex label.
A present vertex has a nonempty vertex-label slot, and precisely a present
nonroot vertex has a nonempty incoming-edge slot. Absent addresses have
empty slots and the root has no incoming edge. If the actual vertex
alphabet contains an active symbol represented by `none`, that symbol is
stored as `some none`, distinct from an absent slot. There is no
distinctness, increasing-label, chronological, positivity or nonempty
alphabet assumption.

Presence at a fixed Ulam–Harris address is proved clopen in the existing
plane-shape topology. The slot constraints therefore define a closed
subset of the Polish product of shape and countable discrete label
coordinates. This yields Polishness of the full labelled carrier. A
complete labelled radius-$h$ ball is the finite set of present addresses
of length at most $h$, with their vertex labels and incoming-edge labels,
including the boundary labels. Its address projection is the existing
unlabelled plane ball. Convergence is proved equivalent to eventual
equality of all such finite labelled balls. Empty absent slots prevent
extra topology from labels at nonvertices.

`PlaneTreeLabellings.lean` is the semantic completeness check for these
label coordinates. It constructs a tree from any existing plane shape,
any assignment $V$ to its actual vertices and any assignment $E$ to its
actual nonroot edges. It recovers both assignments from an encoded tree
and proves that redecorating its shape recovers the entire encoded tree.
Thus the carrier is not merely a restricted collection of selected
labelled examples. Empty alphabets are handled through the actual vertex
and edge domains without an extra nonemptiness premise.

`LocalTopologyVariants.lean` extracts actual metric witnesses from the
proved Polish instances: compatibility with the existing topology,
completeness for that metric, and separability. The plain plane, generic
plane-labelled and specialized chronological instances are all exposed.
The positive-radius convergence criteria use exactly the source's
$h\geq1$ convention. Radius zero follows by restriction of radius one
(or by the fixed unlabelled root), so no root-label condition is lost.

Current proof evidence: `PlaneTreeLabelledTopology.lean` passes an
actual-file direct Lean check with `autoImplicit=false` and zero
diagnostics; root focused build passes. The metric/positive-radius
packaging and the semantic labelling consumer also pass zero-diagnostic
actual-file direct checks. The imported evidence probe
`PlaneLabelledTopologyEvidence.lean` passes eight source-shaped examples
and fourteen closure queries; every queried closure uses exactly
`propext`, `Classical.choice` and `Quot.sound`. Retained direct evidence
uses the matching module names under `verification/`, and the imported
evidence is `plane-labelled-topology-evidence.log`.

The broad-domain target in A20 is the source's
unrestricted unordered, vertex-labelled and edge-labelled locally finite
tree space when its edge labels are not chronological/distinct IDs.
The new broad-domain work has now constructed the arbitrary repeated-label
finite quotient and its truncations (`UnorderedFiniteTruncation.lean`),
proved its representative fibers finite, and constructed the closed Polish
tower of coherent quotient balls (`UnorderedCoherentBalls.lean`). A compact
finite-fiber argument proves existence of literally compatible ordered
finite representatives, without a normalization or compatible-lift
hypothesis. `UnorderedPlaneRealization.lean` realizes each tower as an
actual infinite locally finite plane-labelled tree with the exact finite
labelled balls. The finite reader correctness is supplied by
`PlaneFiniteRootedCorrectness.lean`.

`PlaneTreeGraph.lean` decodes every plane shape into a genuine connected,
acyclic, locally finite graph, with an explicit address-to-vertex
equivalence and root distance equal to address length. Its natural IDs are
auxiliary names, not the actual edge labels. `PlaneLabelledGraphIso.lean`
defines true root/parent/vertex-label/edge-label preserving bijections and
transports them to actual graph isomorphisms. `PlaneBallIso.lean` and
`PlaneCoherentIso.lean` prove finite isomorphism-fiber compactness and the
construction of a genuine global isomorphism. With the separately authored
finite forward helper, `PlaneFiniteBallIso.lean` proves that equal
unordered ball towers force a genuine global rooted labelled isomorphism.

The separately authored `RootedUnorderedGraphIsoConverse.lean` now proves
the reverse finite classification. `UnorderedFiniteIsoBridge.lean` and
`UnorderedTreeQuotientCore.lean` use it to obtain invariance and
surjectivity of the actual finite-ball map; the same-tower isomorphism
theorem gives injectivity. The intermediate core's finite-reflection proof
input is fully discharged by `UnorderedTreeTopology.finiteIsoReflection`.
The final carrier is the actual forgetting-order quotient of all generic
plane trees over the source alphabets, not a bare coherent-ball carrier.

`PlaneRootedGraphIso.lean` also proves that an actual root-preserving graph
isomorphism automatically preserves the parent relation, using adjacency
and exact root distance. Thus the quotient imposes no extra parent/order
condition. Its final equality criterion is precisely a rooted graph
isomorphism preserving full actual vertex and incoming-edge labels.

`UnorderedTreeTopology.lean` supplies the proved quotient/tower equivalence,
a Polish instance, an explicit compatible complete and separable
`localMetricSpace`, its distance `localDist`, and exact positive-radius
finite-truncation convergence. Its public conclusions carry no finite
reflection, inverse, normalization or representation hypothesis. Actual
graph representatives are connected, acyclic and locally finite. The
finite-ball equality is identified with genuine finite rooted labelled
isomorphism, including boundary labels and repeated integer labels.

Final actual-file direct checking passes with zero diagnostics. The root
focused artifact build passes 3,952 jobs. The authored imported statement
probe `UnorderedLocalTopologyStatements.lean` passes twelve exact examples
and twelve final closure queries, all exactly `propext`, `Classical.choice`
and `Quot.sound`; evidence is `unordered-local-topology-statements.log`.
The earlier seventeen dependency closure probes also pass using only those
standard axioms or a subset. Root performs the independent source audit.

The standalone A20 topology construction is therefore proved. The affected
T01–T02 representation dependency now has a complete proof in the frozen
chronological bridge modules: exact equality of finite unordered classes
matches raw record-ball equality at the same radius; the actual embedding
has closed image; and the pushforward on probability laws preserves and
reflects weak limits without an extra support premise. The full source-
ambient main consumers pass the 4,142-job root artifact build. The authored
imported probe passes nine examples and fifteen standard-axiom closures;
the independent root probe passes six statements and seven closures. The
independent semantic audit found no remaining encoding/support premise.
The proof and current evidence are recorded in
`CHRONOLOGICAL_AMBIENT_BRIDGE.md` and
`CHRONOLOGICAL_AMBIENT_INDEPENDENT_AUDIT.md`; no main theorem has been
changed or given a weaker source target.
