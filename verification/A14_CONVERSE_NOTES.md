# A14/A16 converse: decoding forward states into intrinsic labelled trees

Scope: source lines 638-720. The paper states that $\mathfrak T^+_{k,n}$ is "the set of all possible trees with $k$ active vertices and $n-k$ frozen vertices which can be obtained by Algorithm 1", and that $\mathcal T_n$ is an element of $\mathfrak T^+_{S_n,N_n}$. The encoder direction (class $\subseteq$ union over schedules of forward supports) is in `A14_INTRINSIC_NOTES.md`. This note covers the **converse**: a decoder from forward states to labelled rooted trees, the resulting iff, and the round trip. The printed fixed-schedule support claim stays false and is not claimed; every statement is about the union over schedules, or about the actual random sample of one schedule.

Modules (all new, each under 1000 lines, `module`, only standard axioms `propext`, `Classical.choice`, `Quot.sound`):

- `Freezing1/ForwardStateDecodingTree.lean` (146 lines): the decoder `decodeTree`, children lists, local properties.
- `Freezing1/ForwardStateDecodingCount.lean` (230 lines): the double count, the encoding property, the label set $\{1,\dots,N\}$, numeric facts.
- `Freezing1/ForwardStateDecodingMain.lean` (171 lines): exports (decoder, class, iff, support and almost-sure statements).
- `Freezing1/ForwardStateDecodingUnique.lean` (390 lines): the decoder inverts the encoder up to sibling order; uniqueness of the encoded class; bijection.
- Probe `verification/A14ConverseStatements.lean` (not a `module` file, so that the worked example can unfold well-founded definitions by `simp`), log `verification/a14-converse-statements.log`.

## Construction (decoder)

For a forward state `s : Forward.State` and a bound $N$ (`decChildren s N v`, `decodeTree s N v`):

- the children of the vertex $v$ are the vertices $w$ with $v < w \le N$, `w ∈ s.vertices` and `s.parent w = v`, listed in increasing order of $w$ (`List.range'` filtered); `mem_decChildren` is the membership characterization, `decChildren_pairwise` the strict sorting;
- `decodeTree s N v = Rooted.node (s.frozenAt v) ((decChildren s N v).map fun w => (w, decodeTree s N w))` (`decodeTree_eq`); the node label is the freezing label (`none` is active, `a`), the edge label of the child is its vertex identifier $w$ (the attachment time);
- the recursion is well founded on $N - v$ (children have larger identifiers); `decChildren_induction` is the induction principle along the recursion.

The decoded tree of the state is `decodeTree s N 0` (root $0$).

## What is proved

Throughout, `h : Forward.IncreasingLabelled N s` is the schedule-free intrinsic condition from `ForwardIntrinsicSupport.lean`.

1. Local properties (`Tree`): `decodeTree_heapIncreasing h v` (from `parent_lt`, `frozen_after_birth`, `parent_frozen_after_child`), `decodeTree_canonical` (strictly increasing siblings, no hypothesis), `decodeTree_increasing h v` (`Rooted.Increasing`), `decodeTree_encodes h v` (recursive `Rooted.Encodes` using `height_parent`).
2. The double count (`Count`): for a non-root vertex $u \le N$ of $s$ and every $v$, the multiplicity of $u$ among the identifiers (the root $v$ and the edge labels) of `decodeTree s N v` equals the multiplicity of `s.parent u` there plus $1$ if $u = v$ (`decode_count_step`). Taking $v = 0$ and strong induction on $u$ gives `decodeTree_ids : 0 ::ₘ (decodeTree s N 0).edgeLabels = s.vertices.val`: the identifiers of the decoded tree are exactly the vertices of $s$, each once.
3. `decodeTree_isEncoding h : (decodeTree s N 0).IsEncoding s` (vertex set, `Encodes`, canonical defaults, root height, active set, parent graph).
4. `decodeTree_labels h : (decodeTree s N 0).labels = (Finset.Icc 1 N).val`: the vertex labels are the filter-map of `frozenAt` over the vertices (generic lemma `Rooted.IsEncoding.vertexLabels_eq`), they are pairwise distinct (`frozen_injective`, defaults), disjoint from the edge labels (`label_disjoint`), bounded by $N$ (`vertex_le`, `frozen_le`), positive (`frozen_after_birth`), and cover $1..N$ (`label_cover`).
5. `decodeTree_vertexCount h`, `decodeTree_activeCount h`: vertex and active counts of the tree are $n$ = `s.vertices.card` and $k$ = `s.active.card`.

Exports in `Freezing1.Forward` (`Main`):

- `IncreasingLabelled.exists_rooted : IncreasingLabelled N s → ∃ t : Rooted, t.HeapIncreasing ∧ t.labels = (Finset.Icc 1 N).val ∧ t.IsEncoding s`.
- `IncreasingLabelled.exists_rooted_increasing`: moreover `t.Increasing` (sorted siblings), `t.vertexCount = s.vertices.card`, `t.activeCount = s.active.card`; `IncreasingLabelled.exists_rootedClass : ∃ t : RootedClass s.active.card s.vertices.card (Finset.Icc 1 N), t.val.IsEncoding s`.
- Numeric facts: `IncreasingLabelled.card_param : N + s.active.card + 1 = 2 * s.vertices.card`, `eq_two_mul_sub : N = 2 * s.vertices.card - s.active.card - 1`, `label_counts`: $n-1$ edge labels, $n-k$ vertex labels, $N = (n-1) + (n-k)$.
- `IncreasingLabelled.toClass h : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N)` with `toClass_isEncoding`; `IncreasingLabelled.exists_class`; `IncreasingLabelled.of_class q (hs : q.val.IsEncoding s) : IncreasingLabelled N s` for any $k$, $n$, $N$.
- The iff: `increasingLabelled_iff_exists_class : IncreasingLabelled N s ↔ ∃ q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N), q.val.IsEncoding s`, and in the paper's parametrization `increasingLabelled_iff_exists_paper_class : IncreasingLabelled N s ↔ N = 2 * s.vertices.card - s.active.card - 1 ∧ ∃ q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 (2 * s.vertices.card - s.active.card - 1)), q.val.IsEncoding s`.
- Union over schedules equals encoded classes: `exists_support_iff_exists_class : (∃ x, (N : ℕ∞) ≤ extinctionTime x ∧ (treeLaw x N) {s} ≠ 0) ↔ ∃ q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N), q.val.IsEncoding s`.
- The random sample: `treeLaw_support_exists_class` (every support point of `treeLaw x N`, $N \le$ `extinctionTime x`, has $N = 2n-k-1$ and encodes a class), `treeLaw_ae_exists_class : ∀ᵐ s ∂ treeLaw x N, N = 2 * s.vertices.card - s.active.card - 1 ∧ ∃ q, q.val.IsEncoding s`, and `treeLaw_ae_exists_paper_class`, where in addition `(s.active.card : ℤ) = activeCount x N` and `s.vertices.card = plusCount x N + 1` almost surely, i.e. the paper's $S_N$ and $N_N$ are the deterministic quantities of the schedule and the sample lies in $\mathfrak T^+_{S_N,N_N}$ (with $N_N = (S_N + N + 1)/2$).

Round trip (`Unique`):

- `Rooted.IsEncoding.unorderedEq_decodeTree`: a heap-increasing tree with labels exactly $1..N$ encoded by $s$ is sibling-permutation equivalent (`Rooted.UnorderedEq`) to `decodeTree s N 0`; `Rooted.IsEncoding.unorderedEq_of_encoding`: two such trees encoded by the same state are equivalent.
- `UnorderedIncreasingClass.eq_of_isEncoding`: a state encodes at most one class; `UnorderedIncreasingClass.existsUnique_state`: a class has exactly one encoding state; `IncreasingLabelled.existsUnique_class`: an intrinsic increasing state encodes exactly one class; `UnorderedIncreasingClass.state_counts`.
- `Forward.intrinsicClassEquiv k n N : UnorderedIncreasingClass k n (Finset.Icc 1 N) ≃ {s : State // IncreasingLabelled N s ∧ s.active.card = k ∧ s.vertices.card = n}` (bijection through the encoding relation, with `classToState`, `stateToClass`, `classToState_isEncoding`, `stateToClass_isEncoding`).
- `treeLaw_support_existsUnique_class`, `treeLaw_ae_existsUnique_class`: the sample encodes exactly one class, so "$\mathcal T_n \in \mathfrak T^+_{S_n,N_n}$" holds with a uniquely determined element.

Proof of the round trip: for a tree $t$ at identifier $i$ with local hypotheses (`DecHyp`: encodes, heap-increasing, root above $i$, edge labels vertices $\le N$, edge labels nodup), the edge-label multiset of $t$ is below that of `decodeTree s N i` (bottom-up along `decChildren_induction`, injecting the children of $t$ into the decoded children). At the root cardinalities agree ($n-1$), so the multisets are equal. Top-down, equality of the sums over children forces the child set of $t$ to be exactly the decoded child set and the subtree edge labels to agree, so the induction hypothesis applies and the children lists agree up to permutation (`Rooted.UnorderedEq.children_congr`, `.perm`).

Combined with the encoder (`UnorderedIncreasingClass.exists_forward_support`, `increasingLabelled_iff_exists_support`) this proves: the intrinsic class $\mathfrak T^+_{k,n}$ is in bijection with the intrinsic increasing forward states with these parameters, and these states are exactly the support points, over all non-extinct schedules, of the forward law at time $N = 2n-k-1$.

## Verification

Direct checks (`lake env lean -DautoImplicit=false`) of the four modules: exit status 0, no output. Artifacts built with the serialized `bl.sh`. Probe `verification/A14ConverseStatements.lean`: exit status 0, 31 `#print axioms` lines, all `[propext, Classical.choice, Quot.sound]`. The probe also contains a worked example: for the tree with root `a`, edge $1$ to a vertex frozen at $3$, edge $2$ to an active leaf, the decoder applied to `exTree.toState` with $N = 3$ returns `exTree`.

## Caveats

- The statements are for the schedule-free predicate `IncreasingLabelled`, itself equivalent to support over the union of schedules (`increasingLabelled_iff_exists_support`). The fixed-schedule claim of the source remains false.
- The almost-sure and support statements need `(N : ℕ∞) ≤ extinctionTime x` (the law is absorbed afterwards; nothing is claimed beyond extinction).
- The decoder is noncomputable (classical decidability for membership) and defined by well-founded recursion; sibling order is the increasing order of edge labels, but all class-level statements are order independent.
- The root may be active or frozen (carrier convention, as in the encoder note). $n \ge 1$ is automatic since $0$ is a vertex.
- The class parameters of the iff are $k$ = `s.active.card` and $n$ = `s.vertices.card`, with label set $\{1,\dots,N\}$; $N = 2n-k-1$ is derived (`card_param`), not assumed. In the paper's notation the label set is $[1, 2N_n - S_n - 1]$ and $N$ is the number of steps.
- No existing file, `Freezing1.lean`, `FORMALIZATION_REPORT.md` or lake file was modified. The new modules are not yet imported from `Freezing1.lean`.
