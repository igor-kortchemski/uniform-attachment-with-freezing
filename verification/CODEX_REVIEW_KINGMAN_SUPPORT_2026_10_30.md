# Independent review of A07 and the intrinsic A14/A16 bridge

The reviewer did not author these proof modules. This scoped read-only review
reconstructed the assertions at manuscript lines 311, 523–536, 658–720 and
2346, then inspected their definitions, exported types and the new central
proof bodies. The manuscript is the unchanged 2,590-line source with SHA-256
`88953dd87165a14b0e643c5b3d0075d8ce5ec39cdcfc0c25d313570fc3ab00df`.
No proof sources were changed. This review does not certify the rest of the
paper, independent kernel replay, Comparator or a Palomar candidate.

## A07: the actual embedded Kingman jump chain

No blocking mathematical defect was found in the advertised embedded-chain
statement. `KingmanPartition.lean:190` specifies a kernel on finite families
of finite blocks without referring to any forest. Each ordered pair of
distinct blocks is uniformly selected and the blocks are replaced by their
union. Below two blocks the kernel holds the partition. The structural
predicate `Blocks.IsPartitionOf` requires nonempty disjoint blocks covering
the original finite set, not an assumed coalescent law.

`merge_eq_merge_iff` shows that distinct unordered block pairs have distinct
merge outcomes. Consequently `mergeLaw_unordered` at line 235 proves the
exact mass $1/\binom m2$ per unordered pair. `mergeLaw_ae_partition` retains
the original label set and removes exactly one block. The holding branch
does not enter the nonterminal actual all-positive process.

`ReverseKingman.lean` defines a forest block as all vertices sharing a
given root and proves these are genuine blocks. The root-to-block map is
injective. Its bijection on legal ordered pairs proves
`joinLaw_map_blocks` from the actual uniform root-join kernel, rather than
assuming a projected transition law.

`ReverseKingmanHistory.lean:87` proves the projection of the complete actual
recorded history after every $k\leq n$ joins equals the separately specified
recorded Kingman chain. The record retains the entire list of earlier
partitions, so this is a joint law, not a collection of marginal identities.
The initial partition has $n+1$ singleton blocks, as required by the initial
root convention. The all-positive schedule gives merges in the reverse
process. The reversed-sign prose and vertex-count issue in the source
remain corrections; the theorem does not validate them. No continuous-time
holding times or exponential-clock coupling are claimed.

## A14/A16: intrinsic unordered objects and actual forward support

No blocking mathematical defect was found in the union-over-schedules
bridge and bijection. The input `UnorderedIncreasingClass` is defined from
finite rooted labelled trees modulo sibling permutations, with only counts,
the complete label multiset and heap-increasing conditions. Its definition
does not assume a forward state, a legal history, or positive probability.

`RootedForwardEncoding.lean:152` explicitly uses vertex zero for the root
and each incoming edge label for the corresponding nonroot vertex ID.
Parent, depth and freezing labels are taken from the finite tree records.
The outside-vertex default values are characterized, and uniqueness is
proved. Distinct positive labels, already required by the source class,
justify all lookups at the vertices actually used. No arbitrary default
is substituted for missing geometric data.

`Rooted.IsEncoding` at line 165 includes the entire vertex set, actual
parent adjacency, active/frozen data, depths and canonical outside values.
Its invariance under sibling permutation is proved, so the encoding
descends to the genuine unordered source quotient. `HeapIncreasing` is
the source condition without a sibling ordering: increasing edge labels
away from the root and every integer vertex label above incident edge
labels. It does not add the canonical sorted-sibling requirement.

`ForwardIntrinsicSupport.IncreasingLabelled` bundles these structural label
properties on a forward state. Inspecting the bundle found no hidden legal
history or support premise. The induced schedule is explicitly given by
which positive labels are vertex IDs. The proved `HistoryShape` supplies
an actual legal history and nonextinction through the required horizon.
`RootedForwardEncodingMain.lean:140` therefore proves for every intrinsic
unordered object the existence of a state and schedule with positive
actual forward mass, with exactly $n-1$ attachment and $n-k$ freezing steps
up to $N=2n-k-1$.

The converse decoder reconstructs sorted child lists from the actual parent
map. The count proof shows that every state vertex occurs exactly once;
the complete edge/frozen label multiset is exactly $\{1,\ldots,N\}$.
`ForwardStateDecodingMain.lean:132` states both directions of the
union-over-schedules support equivalence. The uniqueness proof compares
all decoded child blocks, proving two encodings of the same state are
sibling-permutation equivalent. `ForwardStateDecodingUnique.lean:361`
then gives a genuine equivalence between intrinsic unordered classes and
intrinsic forward states, with both inverses proved. Its classical choices
are characterized by existence and uniqueness; they do not bypass these
proofs. The almost-sure actual forward-sample class consumer is also proved.

This closes the previously retained intrinsic all-schedules interpretation.
It does not prove the paper's false fixed-schedule broad-support formula;
that correction remains essential. The older schedule-compatible product
mass and factorial-fibre theorems are used as already checked dependencies,
not independently reimplemented here.

## Current mechanical evidence and limits

The root reported a fresh current default artifact build passing 4,631
jobs before the probe was run. The new independent
`CodexKingmanSupportStatements.lean` reconstructs eight exact statements,
including the complete terminal history with the record map expanded,
the uniform unordered-pair mass, reachability starting with no assumed
state, and the full intrinsic-class/state equivalence. Nine queries inspect
the transitive axiom closures. The ordinary imported check passes with exit
zero and no diagnostics beyond the axiom output in
`codex-kingman-support-statements.log`; all nine closures use only `propext`,
`Classical.choice` and `Quot.sound`. This is separate from Claude's authored
probes and the earlier statement-only resumption review.

Publication detail for the coordinator: the pre-existing authored
`verification/A14IntrinsicStatements.lean` deliberately lacks a `module`
header to unfold recursive definitions. Any statement that *all* repository
Lean files have such headers must state its scan exclusions or account for
this exception. Actual proof modules in this review use `module`. This
documentation/packaging detail is not a defect in the mathematical bridge.
