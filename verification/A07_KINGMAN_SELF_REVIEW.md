# A07 all-positive reverse forest and Kingman's jump chain — authored self-review

Scope: source lines 311, 523–536 and 2346 (Algorithm 2 with all signs positive "corresponds to Kingman's coalescent"). This is an **authored** review by the agent who wrote the modules, not an independent audit.

## Interpretation

The source gives no holding-time construction, so the checkable content is the embedded jump chain: the partition-valued process obtained from the all-positive reverse forest merges two uniformly chosen distinct blocks at each step, starting from singletons. No continuous-time identity is claimed or assumed. (The introduction's reversed sign convention and $n$ versus $n+1$ count remain the S05 corrections: the all-positive terminal tree has $n+1$ vertices.)

## What is proved

Files: `KingmanPartition`, `ReverseKingman`, `ReverseKingmanHistory`.

1. `Kingman.Blocks`, `Blocks.IsPartitionOf s` (nonempty, pairwise disjoint, within and covering $s$), `Blocks.merge`, and the independently specified kernel `mergeLaw`: uniform ordered pair of distinct blocks, merged; unchanged below two blocks. The kernel mentions no forest.
2. `mergeLaw_unordered`: each unordered pair of distinct blocks of a partition with $m$ blocks gets mass $1/\binom m2$ (via `merge_eq_merge_iff`). `mergeLaw_ae_partition`: the merge of a partition of $s$ is a partition of $s$ with exactly one block fewer.
3. `ofForest_isPartitionOf`: the family of components of an actual `RootedForest` is a genuine partition of its vertex set; `ofForest_isolated`: isolated vertices give the discrete partition.
4. `ofForest_joinChoice` and `joinLaw_map_blocks`: one actual uniform ordered-root join of a forest projects exactly to the Kingman merge of its component partition (bijection between ordered pairs of distinct roots and ordered pairs of distinct blocks).
5. `map_blockHistory_lawAfter`: for the all-positive schedule, for every $k\le n$, the **entire** joint history of `ReverseHistory.lawAfter` (current forest together with all earlier forests), projected to component partitions, equals `kingmanLawAfter`, the recorded Kingman chain with its past, started from the discrete partition of the $n+1$ original labels. `ae_kingmanLawAfter_partition`: along it every state is a genuine partition of the same set with $k$ fewer blocks and a past of length $k$; hence one block remains after $n$ jumps.

## Evidence

Direct checks of the three modules: exit 0 with no diagnostics; artifacts built; included in the integrated default build. Authored probe `verification/A07KingmanStatements.lean`, log `verification/a07-kingman-statements.log`: exit 0, six axiom queries all standard.

## Not claimed

- No holding times, no continuous-time process, no Kingman coalescent in the sense of a Markov process on $[0,\infty)$.
- Only the all-positive schedule. The general-schedule reverse forest is not a pure coalescent (negative steps insert singletons).
