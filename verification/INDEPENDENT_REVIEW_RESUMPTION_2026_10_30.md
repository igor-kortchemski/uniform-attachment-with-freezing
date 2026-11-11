# Independent statement review: Claude resumption milestone (A03, A06, A07, A14/A16, A87)

Reviewer: a read-only reviewer who did not write any of the reviewed declarations. Date: 30 October 2026.
Source: `attachement-uniforme-1-final.tex` (2,590 lines, hash unchanged in the report). Report reviewed:
`FORMALIZATION_REPORT.md` rows A03 (l.75), A06 (l.78), A07 (l.79), A14 (l.86), A16 (l.88), A87 (l.159)
and the section "Claude resumption milestone" (l.882-911).

Scope and method. For each family I read the tex statement first, then the exported Lean statements, then followed
the definitions that give them meaning (state, kernel, event, carrier types, junk values). I did not audit proof
scripts beyond Lean acceptance, and I did not re-review upstream results that these families import (the chronological
plane bridge `map_fullLaw_toPlaneState`, T02 `planeLimitLaw_fixedPoint`, T04.II `linear_uniform_distance_deviation_tendsto_zero`,
`LinearRegimeAssumptions`, the general-schedule `Reverse` kernel). Statement-level review only; no Comparator/Palomar view.

Evidence run by me (no `lake build`): scratch probe
`ReviewProbe.lean` (a local scratch file, not retained)
(`lake env lean -DautoImplicit=false`, exit 0, only a deprecation warning). It (a) re-proves the A03 conclusion for an
independently written event `{H | (H (2m-1)).active = ∅ ∧ ∀ k < 2m-1, (H k).active ≠ ∅}` (so `ExtinctionTimeIs` with `card = 0`
is not hiding anything), (b) prints `#print axioms` for 15 headline exports (A03 x4, A07 x2, A06 x3, A14 x4, A87 x2): all
`[propext, Classical.choice, Quot.sound]`, and (c) prints the exact elaborated types of `treeLaw_ae_exists_class` and
`treeLaw_ae_exists_paper_class`. All 26 modules of the five families are imported by `Freezing1.lean`; none contains
`sorry`/`axiom`/`native_decide`.

## Verdicts

| Family | Verdict | Blocking | Should-fix | Minor |
| --- | --- | --- | --- | --- |
| A03 conditioned uniform plane tree + uniform reordering | statement faithful with caveats | 0 | 3 | 2 |
| A07 Kingman jump chain, whole joint history | statement faithful as described | 0 | 1 | 1 |
| A06 sampled matrices + GH non-tightness | faithful with caveats (the row presents it less partially than it is) | 0 | 2 | 2 |
| A14/A16 intrinsic class, encoder/decoder | statement faithful with caveats | 0 | 2 | 2 |
| A87 per-vertex exponential-moment domination | faithful with caveats (fixed word, exponential moment only) | 0 | 2 | 1 |
| Report-wide consistency | not accurate as written | 0 | 2 | 0 |

No statement-fidelity defect was found: I found no hidden assumption, no wrong junk-value convention that leaks into a
conclusion, and no quantifier mismatch. Nothing is blocking. The "overstated" label applies to no family; the report
needs the corrections of the last section, two of which (R1, R2) are factual inconsistencies inside the report.

## A03 (tex 271-274)

Source: iid non-constant uniform signs; conditionally on tau = n, T_n(X) is a uniform plane tree when the plane order is uniformly random.

Checked definitions.
- Chain and sign convention: `PlaneForward.State` (vertices, active) with `initial = ⟨{[]},{[]}⟩`, `step`
  (`PlaneFiniteState.lean:44-45`: attach inserts `u ++ [childCount+1]` into vertices and active; freeze erases `u`),
  kernel `transition p s = (signLaw p).bind (signedTransitionLaw s)` (`ForwardPlaneKernel.lean:74-76`), uniform active vertex,
  empty active set absorbing. `transition_apply_split` (l.98-102) confirms `true` = attach with weight `p`. This is Algorithm 1
  with fresh iid signs and the paper's chronological child order.
- `ExtinctionTimeIs n H := (H n).active.card = 0 ∧ ∀ k < n, (H k).active.card ≠ 0` (`FinitePlaneExtinctionTime.lean:27-28`):
  genuinely the first active-zero time. The initial state has one active vertex, so the `k = 0` clause is harmless and the
  definition agrees with `tau = inf{n >= 1 : S_n = 0}`. `step_vertices_active_count` / `ae_vertex_active_time_count`
  (l.42-88) prove `2|V_k| = |A_k| + 1 + k` before absorption, whence odd `n = 2m-1` and `|V| = m`
  (`ae_extinctionTimeIs_iff_finiteVertexCount`, l.126-156) and parity (`ae_not_extinctionTimeIs_of_even`, l.160-164).
- Conditioning: `iid_signs_conditioned_extinction_uniform_plane` (`FinitePlaneConditionedUniform.lean:63-67`) uses
  `ProbabilityTheory.cond` of `fullLaw p initial` on a measurable history event of positive mass, pushed forward by `chainLimit`;
  `_at_time` (l.99-102) pushes forward by the genuinely stopped state `shape (H (2m-1))` and so does not depend on the junk
  value of `chainLimit` (`PlaneChainLimit.lean:22-24`, leaf off the convergence set, which is null). `measure_extinctionTimeIs`
  (l.38-48): `P(tau = 2m-1) = |FinitePlaneClass m| (1-p)^m p^(m-1)`, consistent with the Catalan formula at p = 1/2.
  m = 0 and even times are excluded/handled (`measure_extinctionTimeIs_even`, l.114-118). Not vacuous: `finitePlaneUniform_isProbability`.
- Carrier: `Tree` = canonical offspring functions on `List ℕ` (`PlaneTree.lean:50`), `FinitePlaneClass m` = finite trees with
  `ncard {u | Present T u} = m` (`FinitePlaneConditionalBounds.lean:109`), `finitePlaneUniform m` = normalized sum of Diracs
  (`FinitePlaneUniformLaw.lean:46-47`). Correct ordered rooted trees with `m` vertices.
- `shufflePMF` (`FinitePlaneShuffleDef.lean:184-189`): for finite `T`, `uniformPerm (degree T)` bound with the independent product
  `piFin` of the recursively shuffled child subtrees, rebuilt by `ofChildren (A ∘ σ)`. This is exactly an independent uniform
  permutation of the children at every vertex (the one-level mass `shufflePMF_apply_eq` is the correct `1/d! * Σσ Π_j` formula;
  I rederived it). Infinite trees map to Dirac (junk, irrelevant on the finite class). `finitePlaneUniform_bind_shuffleLaw`
  (`FinitePlaneShuffleMain.lean:112-113`) is unconditional; `..._shuffled` (l.149-157) is the correct composition.
  `SameUnordered.shufflePMF_eq` (`FinitePlaneShuffleUnordered.lean:60-61`) shows the random order depends only on the unordered tree.

Findings.
- should-fix (A03-1): row l.75 contradicts itself. Its bold lead says "uniform sibling reordering open:" and a later bold
  sentence says "Uniform sibling reordering also proved". The latter is the true state (`..._shuffled` proved, probe exit 0).
- should-fix (A03-2): the conditioning event is stated on the state history, not on the sign sequence. The two coincide
  because `|A_k| = S_k(X)` and every sign is read off the vertex-count increment before absorption, but no Lean statement in this
  family says so; the row and the self-review assert it in prose. Add one sentence ("event of the chain = {tau(X)=n}; signs are
  recoverable from the history; identification of this plane chain with the labelled forward T_n is the earlier bridge
  `map_fullLaw_toPlaneState`, not part of this family").
- should-fix (A03-3): the handover files `verification/A03_FINITE_PLANE_HANDOVER.md` (and report l.877 pointing to it) still
  read "outstanding"; mark them superseded.
- minor: the theorem is proved for every `p ∈ (0,1)` (strictly more than the source `p = 1/2`); the report says so. Positivity
  `0 < p` is genuinely needed (for `m >= 2` and `p = 0` the event is null). OK.
- minor: `SameUnordered` is not tied to the A20 unordered quotient; correctly disclosed in the row.

Verdict A03: faithful with caveats. The question "is `ExtinctionTimeIs` the first active-zero time and does the conditioning match
'given tau = n'?" is answered yes, modulo A03-2.

## A07 (tex 311, 523-536, 2346)

Source: Algorithm 2 with all `X_i = +1` is Kingman's coalescent (embedded in the paper only as a remark/research question).

Checked definitions.
- `Kingman.mergeLaw` (`KingmanPartition.lean:190-193`) is defined on `Blocks V` (a bare `Finset (Finset V)`) with no reference to
  forests: uniform over `family.offDiag` (ordered pairs of distinct blocks), pushing `merge A B = insert (A ∪ B) ((family.erase A).erase B)`;
  Dirac below two blocks. It is an independent specification of Kingman's jump. `mergeLaw_unordered` (l.235-237): each unordered
  pair of a partition gets mass `1/choose(m,2)` (uses `merge_eq_merge_iff`, so distinct pairs give distinct outcomes);
  `mergeLaw_ae_partition` (l.224-226): partition of the same set, one block fewer. The junk branch is harmless and is never used
  on non-partitions in a conclusion.
- `joinLaw_map_blocks` (`ReverseKingman.lean:150-151`): one `RootedForest.joinLaw` (uniform ordered pair of distinct roots, join
  under the first) projects exactly to `mergeLaw (ofForest F)`, by a bijection of ordered root pairs with ordered block pairs.
- `map_blockHistory_lawAfter` (`ReverseKingmanHistory.lean:87-89`): `(ReverseHistory.lawAfter allPositive n k).map blockHistory
  = kingmanLawAfter (discrete ((range (n+1)).disjSum ∅)) k` for all `k <= n`. `ReverseHistory.lawAfter`
  (`ReverseHistory.lean:83-87`) is the recursive bind on the full `History` (`current`, `past` list) and `blockHistory`
  (l.49-50) maps current and every past forest through `ofForest`; `kingmanLawAfter` (l.34-37) is the identical recursion on
  partitions. So this is a projection of the genuine joint law of the whole history, not of one-step marginals. The all-positive
  kernel is `Reverse.transitionLaw x i = F.joinLaw` when `x (i+1)` (`ReverseForest.lean:108-109`), i.e. it follows Algorithm 2
  (+1 merges), not the reversed sentence in the Introduction (recorded as S05). Initial forest has `n+1` isolated labels.

Findings.
- should-fix (A07-1): the row records no review status (the milestone calls it a self-review). Add "authored self-review +
  this independent statement review".
- minor: no continuous time, only the all-positive schedule, no claim that the partition process is Markov beyond the equality of laws
  (that is implied but not stated). The row says "no holding times"; fine.

Verdict A07: faithful as described. `mergeLaw` is an independent specification; the history theorem projects the full joint history.

## A06 (tex 357, in the setting of `thm:lineaire`)

Source: T_n/ln n is not tight for GHP, but converges in the sampling topology of [ET21, Jan21] to the long dendron Υ_{δ_{(c+1)/(2c)}}.

Checked definitions.
- `scaledGH n s` (`LinearBushGHTree.lean:97-102`): vertex set of the forward state `s` (all vertices, frozen and active) with
  metric `s.graph.dist / log n` (`instMetricSpaceScaledVertices`, l.73-89), as an element of Mathlib's `GHSpace` via `toGHSpace`;
  `default` if `s` is not connected or `log n <= 0`. The graph is the genuine tree (`Forward.ValidAt` carries `acyclic`,
  `reachable`, `adj_mem`). Junk is only on `n <= 1` and on states of probability zero (`treeLaw_valid`), and every
  conclusion is an eventual/`Tendsto` statement or uses `measure_mono_ae`, so the junk value never enters. Hypotheses are
  satisfiable (e.g. all-plus schedules with `A_n = 1 + log log (n+3)`).
- Contradiction with GH tightness is real: `linear_not_tight` (l.198-206) says no compact `K` has `P(T_n/ln n ∈ K) >= 1/2`
  eventually; `linear_not_isTightMeasureSet` (l.217-225) derives `¬IsTightMeasureSet` of the pushforward family (Borel sigma-algebra
  on `GHSpace`, all `n`) via `isTightMeasureSet_iff_exists_isCompact_measure_compl_le` with `ε = 1/2`; the finitely many junk
  indices cannot rescue tightness of the family because the contradiction is eventual. Packing machinery:
  `IsSeparatedFamily r f` means `dist > r`, `PackingNumberLE` = no separated family larger than `M`; `exists_packingNumberLE_of_isCompact`
  (`LinearBushGHPacking.lean:95-98`) is the standard uniform bound on compacts and `PackingAtLeast` (`LinearBushSamplingSeparated.lean:35-37`)
  uses the same strict inequality, so the two ends match. The scale `r = (c+1)/(2c) < (c+1)/c` is legitimate.
- Sample matrices: `sampleKernel` = `k` iid uniform vertices of the same state, `sampleLaw` = bind over the actual tree law
  (`LinearBushSamplingMatrix.lean:97-104`); `linear_sampled_distance_matrix_tendsto_zero` (l.240-250) is convergence in probability of
  `D/ln n` to `starMatrix ((c+1)/(2c)) k` (off-diagonal `(c+1)/c` by `starMatrix_linear`), diagonal identically 0, coincidences
  `V_i = V_j` included in the off-diagonal pair law (`sampleLaw_pair_apply`).

Findings.
- should-fix (A06-1): the row (l.78, and l.900) is not labelled "Partial" although two of the source's three claims are not in Lean:
  (i) GHP non-tightness (only the GH version; the continuity-of-forgetting remark is prose), (ii) convergence in the [ET21, Jan21]
  topology to the long dendron (only finite-dimensional sampled matrices). The phrase "dictionary entries" is jargon; replace by the
  explicit list. Also record what the notes admit and the report omits: the identification "sampled matrix of Υ_{δ_a} equals
  `starMatrix a k`" was not checked against [Jan21, Ex. 3.12] (`A06_NOTES.md`: the reference text was not available).
- should-fix (A06-2): add one sentence that "hence in distribution" and "sampling topology" are not Lean statements. For the record,
  the gap is mathematically benign: because the limit is deterministic, annealed convergence in probability of the `k` x `k` matrices
  gives quenched convergence in probability by Markov, hence convergence in distribution of the random tree in the sampling topology,
  provided that topology is characterized by sample matrices (as in the notes). That is what the unformalized passage consists of.
- minor: `hτ : ∀ n, n < extinctionTime (x n)` (strict, for every `n`) is slightly stronger than the paper's standing
  `n <= tau(X^n)`; under the bulk condition `S^n_n > 0` eventually, so only finitely many `n` differ. Mention once.
- minor: `LinearRegimeAssumptions` (`nearOriginMaximum`, `bulkMinimum`) were read against `eq:assumptions` and look faithful
  (maximum over `A_n <= i <= εn`, bulk minimum over `εn <= i <= n` including `n`), but they were reviewed elsewhere and I did not
  redo that audit.

Verdict A06: faithful with caveats; the formalized GH/finite-sampling statements are exactly as the row describes; the row
must not be read as covering GHP or the dendron.

## A14 / A16 (tex 638-720)

Source: `T^+_{k,n}(A)` = rooted trees with `n` vertices, `n-1` edges and `n-k` vertices labelled injectively by `A`
(`|A| = 2n-k-1`), other `k` vertices `a`; edge labels increase away from the root; integer vertex labels exceed adjacent edge labels.
`T_n ∈ T^+_{S_n,N_n}`; `T^+_{k,n}` is the set of trees obtainable by Algorithm 1.

Checked definitions.
- `Forward.IncreasingLabelled N s` (`ForwardIntrinsicSupport.lean:27-45`): schedule-free. Vertex identifiers are birth times, the
  root is `0`, so "edge label of `v`" is `v` itself. Conditions: `parent_lt` (edge labels increase along root paths),
  `frozen_after_birth` (frozen label exceeds the parent edge) and `parent_frozen_after_child` (exceeds every child edge) = the
  paper's adjacency condition; `frozen_injective`, `label_disjoint`, `vertex_le`, `frozen_le`, `label_cover` = each of `1..N` is
  used exactly once, as an edge or a vertex label; `active_iff` = `a` vertices are the unfrozen ones; `graph_iff`/`parent_*`
  = the tree structure; `defaults` pins junk fields. This matches the paper and nothing extra is assumed; `card_param`
  (`ForwardStateDecodingMain.lean:31`) derives `N + k + 1 = 2n`.
- `Rooted.IsEncoding` (`RootedForwardEncoding.lean:165-172`) + `UnorderedSourceClass.IsEncoding` (`RootedForwardEncodingMain.lean:121`):
  `s.vertices = {0} ∪ edgeLabels`, `parent`/`height`/`frozenAt` read off the node records, `active = unfrozen`, graph = parent
  adjacency, canonical defaults elsewhere; unique with no hypothesis (`IsEncoding.unique`, l.193), exists iff `0 ::ₘ edgeLabels`
  is nodup (automatic for labels `⊆ [1,N]`), sibling-order independent, well defined on the `UnorderedEq` quotient. `HeapIncreasing`
  (`RootedUnorderedTrees.lean:70-74`) is the paper's condition (child root-above edge, parent label above edge). The carrier
  `UnorderedIncreasingClass k n A` correctly forces `|A| = 2n-k-1`.
- `increasingLabelled_iff_exists_support` (`ForwardIntrinsicSupport.lean:147-155`): `IncreasingLabelled N s ↔ ∃ x, N ≤ τ(x) ∧ treeLaw x N {s} ≠ 0`.
  `intrinsicClassEquiv` (`ForwardStateDecodingUnique.lean:361`) is a bijection class ≃ intrinsic states with the stated counts.

Findings.
- should-fix (A14-1): l.86 and l.88 cite `treeLaw_ae_exists_class` for "T_n ∈ T^+_{S_n,N_n} with S_n, N_n the schedule's counts". That theorem
  (`ForwardStateDecodingMain.lean:151`) takes `k, n` from the sample (`s.active.card`, `s.vertices.card`). The deterministic-parameter
  statement is `treeLaw_ae_exists_paper_class` (l.162: `↑s.active.card = activeCount x N ∧ s.vertices.card = plusCount x N + 1 ∧ ∃ q, ...`).
  Cite that one.
- should-fix (A14-2): the A16 row (l.88) repeats the A14 paragraph verbatim and also keeps "reverse admissibility of every arbitrary shape in
  the printed class remains unchecked". Say what the new bridge adds to A16 (nothing about the fixed-schedule product `1/(S_n!) Π 1/S_{i-1}`;
  it only shows the printed class equals the union over schedules) or drop it from A16.
- minor: "not yet extinct at N" should read "N <= tau(x)" (tau = N is allowed, giving `k = 0`).
- minor: `verification/A14_INTRINSIC_NOTES.md`, "Not proved / caveats", first bullet says the converse is not proved; it is in
  `A14_CONVERSE_NOTES.md`. Add a pointer.

Verdict A14/A16: statement faithful with caveats. `IncreasingLabelled` matches the paper's intrinsic increasing conditions; the
encoding of a source tree is faithful (unique, order-independent, quotient-well-defined). The fixed-schedule support claim stays
false, as the report says.

## A87 (tex 2326-2330)

Source: height of a vertex added between `n` and `tau'_n`, conditionally on `tau'_n, (I_i)`, is stochastically dominated by `Height(T_n)` plus independent Bernoulli(`1_{X_i=1}/I_i`) variables; then Bennett.

Checked statements.
- `attachFactor x c j` (`ForwardActiveHeightMgf.lean:214-217`) = `(S_j+1)⁻¹ (S_j + c)` if `x (j+1)` else `1`, with `S_j = (activeCount x j).toNat`.
  `lintegral_activeHMean_pow_treeLawFrom` (l.219-223): for `ValidAt n s`, `|active s| = S_n`, `PositiveThrough x (n+K)`, every `c : ℝ≥0∞`, every
  `k <= K`: `E[activeHMean r (c^·)] = (Π_{i<k} attachFactor x c (n+i)) · activeHMean s (c^·)` under `treeLawFrom x n s k`. I checked
  the arithmetic by hand: after an attachment the active set gains the new vertex (height `h(v)+1`, `v` uniform), so the mean multiplies by
  `(S+c)/(S+1) = 1 + (c-1)/(S+1)`; `S+1` is the active count after the step. Freezing a uniform active vertex leaves the mean unchanged
  in expectation (`lintegral_activeHMean_freeze`, needs `S >= 2`, supplied by positivity).
- `newVertex_height_pow_le` (l.319-325): for `x (n+k+1) = true`, `c >= 1`, `k+1 <= K`, active heights `<= H`:
  `E[c^{height of vertex n+k+1}] <= c · Π_{i<k} (1 + 1_{x(n+i+1)} (S_{n+i}+1)⁻¹ (c-1)) · c^H`. Index convention: the Bernoulli
  parameters are `1/S_i`, `S_i` = active count after step `i`, for the attachment steps `i = n+1 .. n+k`; the birth step `n+k+1`
  itself contributes only the deterministic `+1` (`c ·`). `attachFactor_eq_bernoulli` (l.293-295) is the exact Bernoulli moment form.
  The hypothesis is on active heights only (weaker than `Height(T_n)`), and any `ValidAt n s` with the right active count is allowed.

Findings.
- should-fix (A87-1): row l.159 places "Independent restricted audit six expanded examples/eight closures passes" immediately before the
  per-vertex paragraph. That audit (`SIR_LATE_BENNETT_INDEPENDENT_AUDIT.md`, 09:08) predates and does not cover `ForwardActiveHeightMgf`
  (built 11:07); the new modules have the root's probe and this review only. Reword.
- should-fix (A87-2): state precisely in the row what is proved: an inequality of exponential moments for all `c >= 1`, for a fixed word, from any valid
  state with `|active| = S_n`; no coupling or stochastic ordering is constructed (the recursion does give equality of generating functions
  for the uniform active vertex for all `c >= 0`, hence equality in law, but that is not stated as a theorem). Also say "indices
  `i = n+1..n+k`, `S_i` after the step; the printed sum to `tau'_n - 1` is a weaker upper bound". The "+1 missing in the printed statement" remark is
  correct (the first attachment already gives height `<= H+1`; no Bernoulli can supply a deterministic `+1`); add "harmless for the `O(ln n)` conclusion".
- minor: the probe `A87A14StateStatements.lean` restates the two exports verbatim; I additionally checked the formulas by hand (above).

Verdict A87: faithful with caveats; exponential-moment domination for the fixed word, correctly hedged in the open-items list
(shifted-mean bound and future-conditioned random-mean argument remain uncertified).

## Global totals

`verification/build.log`: "Build completed successfully (4631 jobs)"; no `error`/`sorry` lines (46 linter-warning lines). `verification/axioms.log`
line 1: "Checked 8618 Freezing1 declarations; all transitive axioms belong to propext, Classical.choice, Quot.sound." No Lean source under
`Freezing1/` is newer than `build.log`. The file count 648 in the milestone equals 644 `Freezing1/*.lean` + `Freezing1.lean`, `Challenge.lean`,
`Solution.lean`, `scripts/AxiomAudit.lean`. So the milestone-section totals are supported by the logs.

## Required corrections to the report text

- R1 (l.75, A03): delete "uniform sibling reordering open:" from the bold lead; make the lead say the reordering is proved. (A03-1)
- R2 (report-wide): the "Check | Actual result" table (l.258, l.260) and l.860, l.867 still state 4,596 jobs / 7,986 declarations as the current
  result; the milestone says 4,631 / 8,618. Update or mark as historical. The "Remaining mathematical obligations" paragraph (l.840-845) still lists the
  A03 ordering, A07 specialization, the A14/A16 bridge and A87 per-vertex domination as open; the milestone says it supersedes only the
  "stopped-draft precision" paragraph. Extend the supersession statement or edit the list (A06 remains partial).
- R3 (l.75): add the sentence of A03-2 on the history event versus the sign event, and say that the proved model is the chronological plane chain.
- R4 (l.78, l.900, A06): label "Partial"; list explicitly the non-formalized parts (GHP non-tightness, sampling-topology convergence, dendron
  identification not checked against [Jan21, Ex. 3.12]); note the strict `hτ` convention. Replace "dictionary entries".
- R5 (l.86, l.88): cite `treeLaw_ae_exists_paper_class` for the deterministic `S_n, N_n`; fix "not yet extinct at N"; dedupe the A16 paragraph.
- R6 (l.159): detach the independent-audit sentence from the per-vertex paragraph; state exponential-moment/fixed-word/index convention.
- R7 (l.78, l.86, l.88, l.79, milestone l.882-911): replace "no independent review yet" by "independently reviewed at statement level
  (`verification/INDEPENDENT_REVIEW_RESUMPTION_2026_10_30.md`); proofs not independently audited", and add this file to the
  milestone's review list. Provenance sentence (l.889-890) can stay.
