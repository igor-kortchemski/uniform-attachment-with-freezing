# Independent review of the all-positive recursive-tree example

Reviewed source: `attachement-uniforme-1-final.tex`, the first example at line 273. Reviewed root-authored module: `RecursiveTreeLaw.lean`. The reviewer did not write that module. This is an independent automated review, not human review. The finite conditioned uniform-plane-tree example in the next source sentence is outside this module's scope and remains separately tracked under A03.

## Mathematical interface

The independent comparison law starts from vertex $0$. At step $n+1$, it samples a fresh uniform parent from $\{0,\ldots,n\}$ and attaches the new vertex $n+1$. The parent distribution is specified without reference to the current random tree. It is sampled by binding that fixed uniform measure after the old state, so the new mark is independent of the entire old state. The expanded verification probe also reconstructs this recursion as a pushforward of the actual product of the old-state law and the uniform parent law. No random-active-set law or assumed recursive-tree equivalence is hidden in the comparison definition.

`treeLaw_allAttachment_vertex_sets` proves from the original transition law that both the vertex set and the active set are exactly $\{0,\ldots,n\}$ almost surely. Thus no extinction/empty-set fallback is used, and every sampled parent is legal. `treeLaw_allAttachment_eq_recursive` identifies the full labelled forward-state measures. Parent pointers, graph, heights, freezing fields, and chronological labels are retained. This is stronger than equality of unlabelled shapes.

The proof uses the proved vertex/active-set invariant to replace the original uniform-active transition by the independent comparison transition. It does not add a tree-law, independence, support, or survival premise to the final equality. All horizons, including zero, are covered. The separately checked `newest_parent_law` gives the new parent marginal by projecting the concrete attachment update; the probe transports this marginal back to the original forward law.

## Source count correction and retained scope

After $n$ attachments the model has $n+1$ vertices, including the initial root. The printed count “on $n$ vertices” is false under the source's indexing. This is the existing S05 count correction, not a new discrepancy. The probe checks that the actual one-step law has exactly two vertices with probability one.

The corrected first example is faithful and proved: the all-positive model is the random recursive tree on $n+1$ vertices. This module makes no claim that a finite symmetric-sign tree conditioned on extinction is uniform among plane trees, and it does not count that separate A03 assertion as complete.

## Evidence

`RecursiveTreeIndependentStatements.lean` independently reconstructs five expanded examples and queries six transitive axiom closures. Its ordinary imported check must pass on the root-built artifact before citing a mechanical verdict; the log is `recursive-tree-independent-statements.log`. Whole-project integration and publication evidence remain owned by the integrating agent.
