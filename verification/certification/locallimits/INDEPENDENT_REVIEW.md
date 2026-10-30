# Independent review of `Challenge/LocalLimits.lean` (T01 = `thm:cvlocale`, T02 = `thm:BGW`)

Reviewer: independent (did not write the Challenge or the proofs). Read-only except this file.
Identity checked: manuscript SHA-256 `88953dd8...ab00df` matches; `Challenge/LocalLimits.lean` SHA-256
`ed94fb8f...08e9` (824 lines, 25 `sorry` = the 25 names of `comparator/locallimits.json`); built `.olean` is
newer than the source. `compare.log`/`leanchecker.log` were read, not re-run.

## 0. Overall verdict

No statement is unfaithful. All 6 main statements are **faithful with caveats**; the caveats are documentation
items, none changes the mathematics. The 19 pinning targets are adequate (two are weak, see section 5).
The chronological carrier is an **adequate and mathematically equivalent** encoding of the manuscript's local
space for these theorems, provided the reader is told the seven items of section 4.

| Statement (Challenge line) | Verdict | Caveats (section 4) |
| --- | --- | --- |
| `local_convergence_equivalences` (423-429), T01 (I)-(II)-(III) | faithful with caveat | R1, R2, R3 |
| `local_convergence_common_limit` (434-444), T01 last sentence | faithful with caveat | R1, R2, R3 |
| `ForwardAnnealed.iid_signs_geometric_local_limit` (817-822), T02 | faithful with caveat | R1, R4, R5, R6 |
| `planeLimitLaw_isBienayme` (796-798), T02 | faithful with caveat | R4, R5, R6 |
| `planeLimitLaw_eq_geometricBienaymeLaw` (802-804), T02 | faithful with caveat | R4, R5, R6 |
| `planeLimitLaw_offspring_mass` (808-811), T02 (corollary) | faithful with caveat | R4, R5, R6 |

## 1. Reconstruction from the tex alone (before reading the Lean)

**T01** (tex 257-268). Data: rows $\mathbf X^n\in\{-1,+1\}^{\mathbb N}$, $n\ge0$, and one $\mathbf X$ with
$\tau(\mathbf X)=\infty$ (i.e. $S_k(\mathbf X)\neq0$ for all $k$, with $S_0=1$, $S_k=1+\sum_{i\le k}X_i$) such that
for each $i\ge1$, $X^n_i=X_i$ for all large $n$. Then (I) the laws of $\mathcal T_n(\mathbf X^n)$ converge weakly in
the local space; (II) $\mathcal T_n(\mathbf X)$, coupled by Algorithm 1 (uniform active vertex chosen independently
of the past), converges locally almost surely (its limit is by definition $\mathcal T_\infty(\mathbf X)$); (III)
$\sum_i S_i^{-1}1_{X_i=-1}$ diverges; and the law of $\mathcal T_\infty(\mathbf X)$ is the limit in (I).
Algorithm 1 (tex 424-433) defines $\mathcal T_n$ for all $n$ and holds the tree fixed once no vertex is labelled
$a$ (tex 427; also tex 249), so rows with $\tau(\mathbf X^n)\le n$ are admitted (the sentence at tex 250
"for $0\le n\le\tau$" only says where the tree still moves).

**Local topology** (tex 881-889). $\mathfrak T$ = rooted, vertex-labelled, edge-labelled, locally finite trees
(up to labelled isomorphism); $\lfloor t\rfloor_h$ = vertices at distance $\le h$ from the root, the edges between
them, all labels; $t_n\to t$ iff every $\lfloor t_n\rfloor_h=\lfloor t\rfloor_h$ eventually. The trees $\mathcal T_n$
are double-labelled, so "the local topology" in T01 is that of $\mathfrak T$ (plane/unlabelled variants are the
other families, used only after $\tau\mapsto\overline\tau$ in the proof of T02).

**T02** (tex 277-280). For $p\in[0,1)$ and i.i.d. signs with $P(X_1=+1)=p$ (tree built conditionally on the
signs), $\mathcal T_\infty$ "is a Bienayme tree with offspring $\mu(k)=(1-p)p^k$". A Bienayme tree is a plane
tree (tex 927-946); the plane tree is $\overline{\mathcal T_\infty}$ of tex 1010 (children ordered by increasing
label of the edge to the parent, then all labels erased), and the proof (tex 979-1010) first needs that
$\mathcal T_n$ converges a.s. for every $p\in[0,1)$. Root degree $0$ iff $X_1=-1$, probability $1-p=\mu(0)$.

## 2. The model as formalized (what I read and what it means)

* `SignSequence = ℕ → Bool`, `true` = $+1$ (59). `activeCount` = $S_n$ (63-64), not stopped; `extinctionTime`
  = first $k$ with $S_k=0$ else `⊤` (67-69). Index $0$ unused; `hxy` quantifies $i\ge1$ (425). OK.
* `Forward.State` (80-86), `step` (117-118): attach `t` to the chosen active `v` (edge label `t`, new active
  vertex), or freeze `v` with `frozenAt := some t` (label = freezing time); `none` = label $a$. Matches 429-430.
* `Forward.transitionLaw` (158-161): uniform choice in `s.active`, and `dirac s` if `s.active = ∅`: this is
  exactly the absorbing clause of tex 427. `treeLaw` (169-171) iterates it with sign `x (n+1)` at time `n+1`.
  `State` has the discrete $\sigma$-algebra, so every `map`/`bind` here is genuinely measurable (no junk).
* `ForwardInfiniteHistory.fullLaw x` (339-340): Ionescu-Tulcea (`Kernel.trajMeasure`) of the Markov kernel
  `historyKernel` (323-325) from `dirac initial`: precisely the coupling of Algorithm 1 (fresh uniform choice,
  independent of the past). `map_eval` (348) pins the time marginals; the joint law is the Markov chain by
  definition.
* `LocalTree.Tree` (233): coherent sequences of finite record sets (birth = label of the incoming edge,
  parent birth, height, `frozenAt : Option ℕ`) with discrete topology on balls and product topology;
  `tendsto_iff_balls` (237) pins "eventual equality of every ball". `localTreeOfState` (285-287),
  `localBall_graph_distance` (272) pins radius = graph distance of the actual graph.
* `DiagonalLocalConvergence` (408-410): $\exists\nu\in\mathcal P(\mathrm{Tree})$ with
  $\mathrm{Law}(\mathcal T_n(x_n))\to\nu$ weakly (Mathlib topology on `ProbabilityMeasure`, i.e. bounded
  continuous test functions); `AlmostSureLocalConvergence` (414-416): `∀ᵐ H ∂fullLaw y`, the local trees
  converge to some tree; `freezingReciprocalSum y n` $=\sum_{i=1}^n 1_{y_i=-1}/S_i$ (403-404, the term is
  $\ge0$, and $S_i\ge1$ under $\tau=\infty$, so `1/0` junk never occurs); (III) as `Tendsto ... atTop atTop`
  is exactly divergence of a series of nonnegative terms.
* T02 side: `PlaneTree.Tree` = canonical offspring fields on Ulam-Harris addresses (471), product topology
  (agrees with ball-eventual-equality of plane trees); `bienaymeLaw` = pruning of i.i.d. offspring
  (531); `IsBienayme` (552-556) = tex 940-947 (root law, and given $k$ children the child subtrees are i.i.d.
  copies); `toPlaneTree` (616-617) orders children by increasing birth (`childList`, 590-591; `follow`,
  598-601) = $\overline\tau$ of tex 1010. `ForwardAnnealed` (656-734): `signLaw p` gives mass $p$ to `true`;
  `transitionLaw p` averages out a fresh sign; `fullLaw p` = Markov chain of states with that kernel.

## 3. Checks run (Lean, never `import Mathlib`; all load the built `Challenge.LocalLimits`)

Scratch files (outside the repository): `.../scratchpad/rev/{Nonvac,Indep,Geom}.lean` in the session scratchpad.

1. **Independent restatement of T01** (`Indep.lean`, compiles): my own walk `S'` (recursion), $\tau=\infty$ as
   `∀ n, S' y n ≠ 0`, and (III) as `¬ Summable (fun i => term y (i+1))`; `T01_indep` follows from
   `local_convergence_equivalences` (bridge: `S'_eq`, `sum_eq`, `not_summable_iff_tendsto_nat_atTop_of_nonneg`).
   No binder/elaboration surprise in the equivalences statement.
2. **Non-vacuity** (`Nonvac.lean`, compiles, axioms `propext, Classical.choice, Quot.sound`):
   `alt i := decide (i % 2 = 1)` has `extinctionTime alt = ⊤` and `Tendsto (freezingReciprocalSum alt) atTop atTop`
   ((III) true, $S\in\{1,2\}$); `fun _ => true` has `extinctionTime = ⊤` and $\sum=0$ ((III) false). Rows
   `row n i := if i ≤ n/2 then alt i else false` satisfy `hxy` (`row_hxy`) and are extinct at a time
   $\le n/2+2<n$ for every $n\ge5$ (`row_extinct`). So the hypotheses are satisfiable in both regimes, and the
   absorbing convention for rows is not vacuous (rows with $\tau(\mathbf x^n)\le n$ occur under the hypotheses).
3. **T02 constants** (`Geom.lean`): for `p : unitInterval` with `p < 1`,
   `geometricMeasure (σ p) {k} = ENNReal.ofReal ((1-p)*p^k)` (also at $p=0$: $\mu=\delta_0$);
   `signLaw p {true} = p`. The range `hp : p < 1` is exactly what excludes Mathlib's junk
   `geometricMeasure 0 := dirac 0` (reached only at $p=1$, `σ 1 = 0`). Measurable-structure instances: `OpensMeasurableSpace`
   found; no `MetrizableSpace` instance for `LocalTree.Tree`/`PlaneTree.Tree` is derivable inside the Challenge
   (not needed by any statement).
4. **Mechanical**: `compare.log` ("statements and reachable constants match", permitted axioms only) and
   `leanchecker.log` taken as reported; not re-run (shared machine).

## 4. Findings and the exact caveats a reader must be told

Severity: High = unfaithful; Medium = must be documented before certification; Low = should be documented;
Info = no action.

**F1 (Medium, R1) The carrier is the closed *chronological* subspace of $\mathfrak T$, not $\mathfrak T$.**
`LocalTree.Tree` (230-233) consists of trees whose edge labels are pairwise distinct, positive and increasing
away from the root, each vertex being identified with its incoming edge label (`ValidBall.unique`,
`parent_data`, 220-223); vertex labels are `Option ℕ`. The docstring at 230-232 ("rooted, vertex-labelled and
edge-labelled, locally finite trees") reads as the whole of $\mathfrak T$ and overclaims. Equivalence with the
manuscript, which I re-derived independently of the project:
(a) for such trees, labelled-isomorphic balls $\Leftrightarrow$ equal record sets (an isomorphism is forced
by distinct edge labels and maps the vertex with incoming label $b$ to the vertex with incoming label $b$), so
the topology of `tendsto_iff_balls` is the subspace topology of $d_{loc}$;
(b) the subspace $S$ is closed in $\mathfrak T$ (every ball of a limit is a ball of some $t_n$, hence
chronological);
(c) all $\mathcal T_n(\mathbf x)$ lie in $S$ (pins `treeLaw_valid`, `localTreeOfState_balls`);
(d) hence for laws on $S$, weak convergence in $\mathcal P(S)$ $\Leftrightarrow$ weak convergence of the images in
$\mathcal P(\mathfrak T)$ (closed-set portmanteau: a limit $\nu'$ on $\mathfrak T$ has $\nu'(S)\ge\limsup\mu_n(S)=1$),
and "converges a.s. in $S$" $\Leftrightarrow$ "in $\mathfrak T$" (closedness); limit identification transports by
the embedding. So (I), (II), the limit law of T01 and the a.s. limit of T02 coincide with the manuscript's.
This equivalence is **not** inside the Challenge. The project proves it for its own formalization of
$\mathfrak T$ (`UnorderedLocal.Tree`, quotient of plane trees with `Option ℕ` vertex labels and `ℕ` edge labels
by root/parent/label-preserving bijections): `LocalTree.isClosedEmbedding_toUnordered`
(ChronologicalAmbientEmbedding.lean:87), `source_diagonalLocalConvergence_iff` (MainLocalAmbient.lean:40),
`source_local_convergence_equivalences`/`_common_limit` (55, 65). I did not audit those ambient definitions
beyond confirming their shape; they are outside the Challenge's statement closure (about 1800 lines).

**F2 (Low-Medium, R2) Absorbing extension after extinction.** `Forward.transitionLaw` (159-161) holds the tree
once no vertex is active. This is Algorithm 1 as written (tex 427) and the Challenge assumes no
$\tau(\mathbf x^n)>n$, so it covers every row; any reading restricted to rows with $\tau(\mathbf X^n)\ge n$ follows
as a special case. Section 3.2 shows such rows exist under the hypotheses. The docstring at 421-422 says it.

**F3 (Low, R3) Which topology.** T01 is formalized for the double-labelled topology (the strongest reading of
(I), the native type of $\mathcal T_n$). Plane/unlabelled variants of (I) are not asserted equivalent to (II),
(III); the manuscript does not claim it either. (II) has the same meaning in every variant since each vertex label
changes at most once.

**F4 (Low-Medium, R4) T02 is about $\overline{\mathcal T_\infty}$.** The theorem (tex 277-280) says "$\mathcal T_\infty$
has the law of a Bienayme tree"; a labelled tree is not literally a plane tree. The Lean statements use the
paper's own convention of tex 1010 via `toPlaneTree` (children by increasing birth time = increasing label of
the edge to the parent; labels erased). This is the strongest natural reading: the unordered-unlabelled reading
follows from it. The pins fix only canonicity, root degree and continuity of `toPlaneTree` (611-626); the
ordering at non-root vertices rests on reading `childList`/`follow` (590-601), which I checked: sorted by
`(· ≤ ·)` on births, `j = 0` gives `none`, address lists read first step first, consistent with `prune`,
`child` and `Canonical`.

**F5 (Low, R5) Annealed history versus the joint law of (signs, tree).** `ForwardAnnealed.fullLaw p` (733-734)
is the law of the tree history with the signs integrated out; the signs are not a coordinate. This equals the
tree-marginal of the manuscript's two-stage construction because $X_n$ is independent of the past of signs and
uniform choices, so the history is Markov with kernel $\sum_s P(X_n=s)K_s$ (`transitionLaw_apply_split`, 762-767,
weight $p$ on `true`). A.s. convergence and $\mathcal T_\infty$ are functions of the tree history, so nothing is
lost. The path-level mixture theorem exists in the project
(`ForwardAnnealedHistory.map_prefix_eq_iid_sign_mixture`, line 111; `treeLaw_eq_iid_sign_mixture`) but could not be
a target because `wordSchedule` contains a private auxiliary proof (NOTES, adjustment 1); the Challenge pins only
the one-step mixture and the time marginals (`map_eval`, 741). Severity low: the identification is a standard
two-line argument.

**F6 (Low, R6) Junk values of `Measure.map` / `ProbabilityMeasure.map`.** In this Mathlib,
`Measure.map f μ` for non-a.e.-measurable `f` and `μ ≠ 0` is a Dirac mass at an arbitrary point
(Mathlib/MeasureTheory/Measure/Map.lean:99-106), and `ProbabilityMeasure.map` takes no measurability argument
(ProbabilityMeasure.lean:627-629). Affected: `localLimitLaw` (380, 757), `planeLimitLaw` (781), `bienaymeLaw` (531).
Analysis: T01 is safe (`AEMeasurable localLimit (fullLaw y)` is the first conjunct of
`local_convergence_common_limit`, and `local_convergence_equivalences` does not use `localLimitLaw`). T02:
`planeLimitLaw_*` are not individually accompanied by `AEMeasurable localLimit (fullLaw p)`, but a junk Dirac cannot
satisfy them: for $p\in(0,1)$ the geometric law is not a Dirac, and for $p=0$ the Dirac would be at the opaque
`Classical.ofNonempty`, whose truth is unprovable; and `iid_signs_geometric_local_limit` carries a.s. convergence of
measurable maps, which gives measurability of `planeLimit`. `bienaymeLaw` is non-junk because
`bienaymeLaw_map_degree`/`exists_unique_bienaymeLaw` would fail for a Dirac (`geometricBienaymeLaw_probability`
alone would not detect junk). No loophole, but the statements do not say it; optional pin:
`ForwardAnnealed.aemeasurable_localLimit` (ForwardAnnealedLifetime.lean:231).

**F7 (Low, R7) T02's a.s. convergence is stated for plane trees.** The first conjunct (818-820) asserts
$\mathrm{toPlaneTree}(\mathcal T_n)\to\mathrm{planeLimit}$ a.s.; the manuscript's first claim in the proof (tex 979) is
a.s. convergence of the labelled $\mathcal T_n$ (existence of $\mathcal T_\infty$). It is implied: where the labelled
trees do not converge, `localLimit` takes the default, `planeLimit` is the one-vertex tree, and plane
convergence to it forces the root to have no child from some time on, hence a root-only (eventually constant)
labelled tree, contradiction. Optional pin: `ForwardAnnealed.fullLaw_tendsto_localLimit` (ForwardAnnealedLifetime.lean:219).

**F8 (Info) Options and instances.** `set_option backward.isDefEq.respectTransparency false` (313, 455, 637,
653, 702, 754), `bootstrap.genMatcherCode false` (595, 678), `linter.auxLemma false` (703) exist for
proof compatibility and Comparator constant sharing; none changes a statement. `historyKernel._proof_1/_2` (709-719) are
stated, not assumed. No axiom, `opaque`, `unsafe` or `native_decide` in the file.

**F9 (Info) Manuscript.** Tex 904 uses $S_n$ where the freezing probability at step $n$ is $1/S_{n-1}$ (recorded in
MANUSCRIPT_RECOMMENDATIONS.md:15). Since $S_{n-1}=S_n+1\le2S_n$ at a $-1$ step, the divergence criterion (III) of the
*theorem* is unaffected, and the Lean (III) uses the theorem's $S_i$.

**Required caveats (suggested wording for the Challenge header and NOTES):**

* R1. "`LocalTree.Tree` is the closed subspace of the local space of rooted vertex- and edge-labelled locally finite
  trees consisting of chronological trees (pairwise distinct positive edge labels increasing away from the root; a
  vertex is identified with its incoming edge label; vertex label `none` = $a$, `some t` = frozen at $t$). Its
  topology is the subspace topology of $d_{loc}$ (`tendsto_iff_balls`); since it is closed and contains every
  $\mathcal T_n$, weak convergence, a.s. convergence and the limit are the same as in the full local space (the
  project proves this outside the Challenge)." Also correct the docstring at 230-232.
* R2. "After extinction the tree is held constant (Algorithm 1); no hypothesis $\tau(\mathbf x^n)>n$ is made."
* R3. "The local topology is the one on double-labelled trees."
* R4. "$\mathcal T_\infty$ has the law of a Bienayme tree" means: $\overline{\mathcal T_\infty}$ (children by increasing birth,
  labels forgotten, as in the proof of the manuscript) has the law $\mathrm{BGW}(\mu)$, $\mu(k)=(1-p)p^k$; `IsBienayme`
  is the branching characterization of tex 940-947 and `exists_unique_bienaymeLaw` shows it determines the law.
* R5. "`ForwardAnnealed.fullLaw p` is the marginal law of the tree history of the i.i.d.-sign construction (signs
  integrated out); this suffices as the statements concern only the trees."
* R6. "`planeLimitLaw`, `localLimitLaw` use `ProbabilityMeasure.map`; measurability of `localLimit` is part of the
  statement for T01 (first conjunct) and implied for T02."
* R7. "$p=0$ is included ($\mu=\delta_0$, $\mathcal T_\infty$ is the root); $p=1$ is excluded (`hp`)."

## 5. The 19 pinning targets

| Target (Challenge line) | Judgement |
| --- | --- |
| `Forward.transitionLaw_probability` (164) | adequate: no junk in `treeLaw`; also a private-aux cut point |
| `Forward.treeLaw_valid` (181) | adequate: support consists of valid trees, so the default of `localTreeOfState` never matters |
| `LocalTree.tendsto_iff_balls` (237) | adequate, key for F1: topology is eventual equality of every ball |
| `ValidAt.localBall_graph_distance` (272) | adequate: ball radius = graph distance in the real graph |
| `ValidAt.localBalls_valid` (279) | neutral (well-formedness of the record family; data-defining proof) |
| `ValidAt.localTreeOfState_balls` (290) | adequate |
| `ForwardInfiniteHistory.map_eval` (348) | adequate for marginals (joint law is by definition the Markov chain) |
| `tendsto_localLimit_of_exists` (374) | adequate: `localLimit` is the limit when it exists |
| `ForwardInfiniteHistory.map_eval_localTree` (388) | adequate |
| `PlaneTree.bienaymeLaw_map_degree` (535) | adequate: root law $=\mu$; excludes junk |
| `PlaneTree.geometricBienaymeLaw_probability` (544) | weak alone (a junk Dirac is also a probability law); fine with the two neighbours |
| `PlaneTree.exists_unique_bienaymeLaw` (560) | strong: `IsBienayme` is non-vacuous and has exactly one probability solution, `bienaymeLaw` |
| `LocalTree.canonical_planeOffspring` (611) | well-formedness only |
| `LocalTree.degree_toPlaneTree` (620) | partial pin (root only); deeper ordering not pinned (F4) |
| `LocalTree.continuous_toPlaneTree` (625) | adequate: the continuity used at tex 1010 |
| `ForwardAnnealed.treeLaw_zero_parameter` (686), `_one_parameter` (690) | adequate: orientation $p=P(+1)$, $p=0$ all freezing, $p=1$ all attaching |
| `ForwardAnnealed.map_eval` (741) | adequate for marginals; path-level mixture absent (F5) |
| `ForwardAnnealed.transitionLaw_apply_split` (762) | adequate and the essential i.i.d.-sign link |

## 6. Residual remarks

* No small non-vacuity lemma is in the Challenge (NOTES says so). Section 3.2 supplies one (about 60 lines); it could
  be added as a 26th target only if wanted; it is not needed for fidelity.
* Quantifier order is preserved: the schedule rows, $\mathbf y$, and the approximation $\mathbf x$ are universally
  quantified before the conclusions; (I)$\Leftrightarrow$(II) and (II)$\Leftrightarrow$(III) give the full cycle; the
  "in this case" of T01 is formalized as the hypothesis (III) (equivalent by the first theorem).
* Palomar-specific reading checks (Comparator coverage of all reachable constants, kernel check) were taken from
  the logs; I did not re-run them.
* Recommended before certification: fix R1 docstring (Challenge 230-232), add R1-R7 to the module docstring or
  NOTES. Optional strengthening: pins for `aemeasurable_localLimit` and `fullLaw_tendsto_localLimit` (F6, F7).
