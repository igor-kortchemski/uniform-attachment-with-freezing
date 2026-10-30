# A14/A16 intrinsic class: encoding of labelled rooted trees as forward states

Scope: source lines 638-720 (the table defining $\mathfrak T^+_{k,n}(A)$ and the sentence that it is the set of all trees obtainable by Algorithm 1). The fixed-schedule version is false (already refuted); the statement proved here is about the **union over schedules**.

Modules (all new, each under 1000 lines, standard axioms only):

- `Freezing1/RootedForwardEncoding.lean`: encoding relation, explicit state, existence, uniqueness, sibling-order independence.
- `Freezing1/RootedForwardEncodingIncreasing.lean`: heap-increasing trees with labels $1,\dots,N$ give `Forward.IncreasingLabelled N`; vertex, active and schedule counts.
- `Freezing1/RootedForwardEncodingMain.lean`: union-over-schedules export, class-level (sibling-permutation quotient) statements.
- Probe `verification/A14IntrinsicStatements.lean`, log `verification/a14-intrinsic-statements.log`.

## The encoding

Source carrier: `Rooted.node (label : Option ℕ) (children : List (ℕ × Rooted))`; a child carries the label of its **incoming edge**, `label = none` means the vertex is active (`a`), `some w` is a frozen vertex with integer label $w$.

A forward state has vertex identifiers equal to the edge labels (attachment times), the root being $0$; `frozenAt v = some w` records that $v$ was frozen at time $w$ (the vertex label), `none` means active.

`Rooted.Encodes s t i` (recursive, same shape as `phi` and `HeapIncreasing`) says that the state `s` matches the node `t` whose incoming identifier is `i`:

- for a leaf-like node `node label []`: `s.frozenAt i = label`;
- for `node label ((e, c) :: rest)`: `c.Encodes s e`, `s.parent e = i`, `s.height e = s.height i + 1`, and `(node label rest).Encodes s i`.

The characterization `Rooted.encodes_node_iff` unfolds this to: `frozenAt i = label` and, for every child `(e, c)`, `parent e = i`, `height e = height i + 1`, `c.Encodes s e`. Thus the parent of the vertex named by edge $e$ is the vertex at the upper end of $e$ (identifier of the incoming edge of the parent node, $0$ for children of the root), the height is the depth, and each frozen label sits at the vertex below its edge.

`Rooted.IsEncoding t s` is the conjunction of:

1. `s.vertices = insert 0 t.edgeLabels.toFinset` (vertices are $\{0\}\cup$ the edge-label set);
2. `t.Encodes s 0`;
3. `Forward.CanonicalDefaults s` (parent $0 = 0$; outside the vertex set parent $= 0$, height $= 0$, `frozenAt = none`) and `s.height 0 = 0`;
4. `s.active = s.vertices.filter (frozenAt = none)`;
5. `s.graph = SimpleGraph.fromRel (u ∈ V ∧ v ∈ V ∧ u ≠ 0 ∧ parent u = v)` (the parent adjacency).

Equivalent flat form (`Rooted.encodes_iff_forall_mem`): the state matches one record `(vertex, parent, depth, label)` per node, listed by `Rooted.nodeRecs`.

### Faithfulness results

- `Rooted.IsEncoding.unique`: two encodings of the same tree are equal as `Forward.State`s (no hypothesis on the labels); in particular they agree on the vertex set (also immediate from item 1).
- `Rooted.toState_isEncoding` / `Rooted.exists_isEncoding`: if $0,\ e_1,\dots,e_{n-1}$ are pairwise distinct (`(0 ::ₘ t.edgeLabels).Nodup`) the explicit state `Rooted.toState t` (parent, height, `frozenAt` read off the node records, default values elsewhere) is an encoding. `Rooted.IsEncoding.eq_toState`: it is the only one. For labels $=A.val$ with $0\notin A$ the hypothesis holds (`Rooted.nodup_zero_cons_edgeLabels`).
- `Rooted.UnorderedEq.encodes_iff`, `Rooted.UnorderedEq.isEncoding_iff`, `Rooted.UnorderedEq.toState_eq`: sibling permutations and subtree congruence do not change the encoding; the encoded **state is literally the same**, not merely related by relabelling siblings.

## What is proved

For `t : Rooted` with `t.HeapIncreasing` (every vertex label above its adjacent edge labels, every child edge above the incoming edge; `Rooted.Increasing` implies it) and `t.labels = (Finset.Icc 1 N).val`:

1. `Rooted.IsEncoding.increasingLabelled`: every encoding state `s` satisfies `Forward.IncreasingLabelled N s` (all fields: root, defaults, parent membership/order, heights, active set, graph, injectivity of freezing labels, birth before freezing, parent freezes after child, bounds by $N$, disjointness and cover of $\{1,\dots,N\}$ by edge and vertex labels).
2. `Rooted.IsEncoding.forward_support`: therefore there is a schedule `x` with `(N : ℕ∞) ≤ extinctionTime x`, `Forward.HistoryShape x N s` and `(Forward.treeLaw x N) {s} ≠ 0`.
3. Counts. With $n$ = `vertexCount` and $k$ = `activeCount`: `s.vertices.card = n`, `s.active.card = k` (`vertices_card`, `active_card`), and for **every** `x` with `HistoryShape x N s` (such `x` agrees with `scheduleOf s` on $1..N$, `HistoryShape.eq_scheduleOf`): `plusCount x N = n - 1`, `minusCount x N = n - k` (`schedule_counts`; also the filter form `positive_steps`, `negative_steps`).
4. Main export on the actual unordered class `UnorderedIncreasingClass.exists_forward_support`: for every `k n` and every `q : UnorderedIncreasingClass k n (Finset.Icc 1 (2*n-k-1))`, with $N=2n-k-1$,

   there is `s` with `q.val.IsEncoding s`, `s.vertices.card = n`, `s.active.card = k`, and `x` with `N ≤ extinctionTime x`, `HistoryShape x N s`, `treeLaw x N {s} ≠ 0`, `plusCount x N = n - 1`, `minusCount x N = n - k`.

   The hypothesis $1\le n$ is not needed (a nonempty class has $n=\texttt{vertexCount}\ge1$). Variants: `exists_forward_support_of_representative` (any representative `t` with `⟦t⟧ = q.val`), `RootedClass.exists_forward_support` (sorted canonical representatives), `UnorderedIncreasingClass.increasingLabelled` (every encoding state of a class is `IncreasingLabelled`), `UnorderedSourceClass.existsUnique_isEncoding` (each class has exactly one encoding state).

Quotient handling: `UnorderedSourceClass.IsEncoding` is defined with `Quotient.lift`, well defined because `isEncoding_iff` holds for `UnorderedEq` representatives. Hence statements are about the class, and hold for every representative and for the sorted representative (`isEncoding_canonical_iff`).

## Relation to the paper

This proves the inclusion **intrinsic class $\subseteq$ union over schedules of forward supports** (with the paper's counts: $n-1$ attachments, $n-k$ freezings, $N=2n-k-1$ steps). Combined with the already proved `increasingLabelled_iff_exists_support`, an intrinsic class element is a support point of `treeLaw x N` for some non-extinct schedule `x`.

## Not proved / caveats

- The **converse inclusion** (every `IncreasingLabelled N s` state, equivalently every state reachable by Algorithm 1 under some schedule, is the encoding of a heap-increasing rooted tree with labels $1,\dots,N$, i.e. decoding a state into a `Rooted` tree by recursion on the parent relation) is **not** proved here. So the set equality "$\mathfrak T^+_{k,n}$ = all trees obtainable by Algorithm 1" is established in the direction class $\Rightarrow$ obtainable only; the other direction still needs a decoder `State → Rooted` with the same encoding property.
- The correspondence is on the intrinsic data only. Probabilities are those of `treeLaw x N` for the schedule `x`; the statement is existential in `x` (the printed fixed-schedule claim is false and not claimed). The schedule is determined on $1..N$ by `s` (positive steps are exactly the non-root vertex identifiers).
- Existence of an encoding state uses distinct positive edge labels (`(0 ::ₘ t.edgeLabels).Nodup`), automatic for trees whose labels are `Finset.Icc 1 N`; uniqueness needs no hypothesis. A tree with a repeated edge label has no encoding state in the intended sense.
- The root is allowed to be active (`label = none`) or frozen (`some w`); this follows the carrier `Rooted` (the paper's table does not distinguish the root).
- `IsEncoding` fixes `s.graph` as the parent graph and `s.active` as the vertices with no freezing label; these are the conventions of `IncreasingLabelled` (`graph_iff`, `active_iff`).


Update: the converse (decoder, class bijection, almost-sure statement) is proved in `A14_CONVERSE_NOTES.md`; the first caveat above is superseded.
