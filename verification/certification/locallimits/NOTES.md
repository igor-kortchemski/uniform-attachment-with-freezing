# Local-limit interface (Theorems `thm:cvlocale` and `thm:BGW`): certification notes

Files:

- Challenge: `Challenge/LocalLimits.lean` (module `Challenge.LocalLimits`; 824 lines, 35.5 KB).
- Solution: `Solution/LocalLimits.lean` (module `Solution.LocalLimits`; `public import Freezing1`).
- Configuration: `comparator/locallimits.json` (25 theorem names, no definition holes, axioms
  `propext`, `Classical.choice`, `Quot.sound`).
- Evidence: `compare.log`, `run.log`, `leanchecker.log` in this directory.

## Targets

Statements of the manuscript (`attachement-uniforme-1-final.tex`):

| Lean name | Manuscript item |
| --- | --- |
| `Freezing1.local_convergence_equivalences` | Theorem `thm:cvlocale` (lines 257-268): (I) $\Leftrightarrow$ (II) and (II) $\Leftrightarrow$ (III) |
| `Freezing1.local_convergence_common_limit` | Theorem `thm:cvlocale`, last sentence: $\mathcal T_\infty(\mathbf x)$ is the local limit of $(\mathcal T_n(\mathbf x^n))$ (measurability, a.s. limit, weak limits) |
| `Freezing1.ForwardAnnealed.iid_signs_geometric_local_limit` | Theorem `thm:BGW` (lines 277-280): a.s. convergence of the plane trees to $\mathcal T_\infty$ and its law is the geometric Bienaym\'e law |
| `Freezing1.ForwardAnnealed.planeLimitLaw_isBienayme` | Theorem `thm:BGW`: branching characterization with offspring law $\mu(k)=(1-p)p^k$ |
| `Freezing1.ForwardAnnealed.planeLimitLaw_eq_geometricBienaymeLaw` | Theorem `thm:BGW`: the law is the iid-offspring construction |
| `Freezing1.ForwardAnnealed.planeLimitLaw_offspring_mass` | Theorem `thm:BGW`: root degree has mass $(1-p)p^k$ |

Extra targets (statements pinning the meaning of the model; each is an existing project theorem, copied with
its exact statement and a `sorry` body):

- Forward process: `Forward.treeLaw_valid` (the support consists of valid trees),
  `Forward.transitionLaw_probability`, `ForwardInfiniteHistory.map_eval` (time marginals of the infinite history
  are the tree laws).
- Local space: `LocalTree.tendsto_iff_balls` (local convergence is eventual equality of every ball),
  `Forward.ValidAt.localBall_graph_distance` (balls are graph-distance balls),
  `Forward.ValidAt.localBalls_valid`, `Forward.ValidAt.localTreeOfState_balls`,
  `ForwardInfiniteHistory.tendsto_localLimit_of_exists` (`localLimit` is the limit when it exists),
  `ForwardInfiniteHistory.map_eval_localTree`.
- Plane trees: `LocalTree.canonical_planeOffspring`, `LocalTree.degree_toPlaneTree`,
  `LocalTree.continuous_toPlaneTree`, `PlaneTree.bienaymeLaw_map_degree`,
  `PlaneTree.geometricBienaymeLaw_probability`, `PlaneTree.exists_unique_bienaymeLaw` (existence and
  uniqueness for `IsBienayme`, so the characterization is not vacuous).
- i.i.d. signs: `ForwardAnnealed.transitionLaw_apply_split` (sign law: `+1` with probability `p`),
  `ForwardAnnealed.treeLaw_zero_parameter`, `ForwardAnnealed.treeLaw_one_parameter` (orientation of `p`),
  `ForwardAnnealed.map_eval` (time marginals of the annealed history).

There is no existing small non-vacuity lemma for the hypotheses of Theorem `thm:cvlocale`
(a schedule with `extinctionTime = ⊤` and divergent freezing sum together with an approximating array), so none
is included.

## Imports of the Challenge

Only Mathlib: `Algebra.BigOperators.Group.Finset.Basic`, `Basic.Real.Basic`, `Tactic`,
`Tactic.DeriveCountable`, `Data.ENat.Lattice`, `Data.Finset.Sort`, `Combinatorics.SimpleGraph.Acyclic`,
`Combinatorics.SimpleGraph.Metric`, `Topology.MetricSpace.Polish`,
`MeasureTheory.Constructions.BorelSpace.Basic`, `MeasureTheory.Constructions.BorelSpace.Metrizable`,
`MeasureTheory.Constructions.Pi`, `MeasureTheory.Measure.ProbabilityMeasure`,
`MeasureTheory.Integral.DominatedConvergence`, `Probability.Distributions.Uniform`,
`Probability.Distributions.Bernoulli`, `Probability.Distributions.Geometric`,
`Probability.Independence.InfinitePi`, `Probability.Kernel.IonescuTulcea.Traj` (the union of the direct Mathlib
imports of the source modules; no further module was needed).

## Copied declarations (verbatim from the development, with the same `namespace`/`open`/`set_option` context)

Source module: declarations.

- `Path`: `SignSequence`, `activeCount`. `Extinction`: `extinctionTime`.
- `ForwardTree`: `State`, `initial`, `attach`, `freeze`, `step`, `ValidAt`, `initial_valid`.
- `ForwardLaw`: `MeasurableSpace State`, `DiscreteMeasurableSpace State`, `transitionLaw`, `treeLaw`,
  `treeLaw_probability`.
- `LocalTreeTopology`: `VertexRecord` (with `deriving DecidableEq, Countable`), `Ball`, `TopologicalSpace Ball`,
  `restrict`, `ValidBall`, `ValidSequence`, `Tree`.
- `ForwardLocalTree`: `MeasurableSpace`/`BorelSpace` on `LocalTree.Tree`, `localRecord`, `localBall`,
  `localTreeOfState`, `localTreeLaw`, `localTreeLaw_probability`.
- `ForwardInfiniteHistory`: `History`, `historyKernel`, `historyKernel_markov`, `fullLaw`, `fullLaw_probability`.
- `ForwardLocalLimit`: `localLimit`, `localLimitLaw`, `localProbabilityLaw`.
- `MainLocalLimit`: `freezingReciprocalSum`, `DiagonalLocalConvergence`, `AlmostSureLocalConvergence`.
- `PlaneTree`: `Address`, `Offspring`, `Canonical`, `Tree`, `degree`, `child`, measurable-space instances.
- `PlaneTreePruning`: `pruneRaw`, `canonical_pruneRaw`, `prune`.
- `PlaneBienaymeLaw`: `offspringFieldLaw`, `bienaymeLaw`, `geometricBienaymeLaw`.
- `PlaneTreeBranching`: `IsBienayme`.
- `LocalTreeChildren`: `findRecord`, `recordAt`, `childIDs`, `childList`.
- `ChronologicalPlaneTree`: `follow`, `planeOffspring`, `toPlaneTree`.
- `CountableMarkovShift`: `Prefix`.
- `ForwardAnnealed`: `signLaw`, `signLaw_probability`, `transitionLaw`, `transitionLaw_probability`,
  `transitionKernel`, `treeLaw`.
- `ForwardAnnealedHistory`: `historyKernel`, `historyKernel_markov`, `fullLaw`, `fullLaw_probability`.
- `ForwardAnnealedLifetime`: `localLimitLaw`. `ForwardPlaneLimit`: `planeLimit`, `planeLimitLaw`.

## Adjustments that were necessary

Comparator follows every constant occurring in the type or the value of each non-target constant, and
requires the Challenge and Solution constants to be identical. Because the development is spread over many
modules while the Challenge is one module, three Lean mechanisms made verbatim copying insufficient. Each
adjustment keeps the elaborated constants identical to the Solution's; none changes a statement.

1. Module-private auxiliary lemmas. Proofs using `simp`, `omega` or tactic blocks create auxiliary lemmas
   named `_private.<module>.0.<declaration>._simp_1_n` (or `_proof_1_n`); the module name is part of the name, so
   a theorem whose proof term mentions one can never be identical in a module called `Challenge.LocalLimits`.
   Such theorems are reachable here through definition bodies (they are proof arguments of data). They are
   therefore stated as targets (with `sorry` bodies; only their statements are compared, and they are proved in
   the Solution). The cut points are `Forward.transitionLaw_probability` (replaces `uniform_active_probability`),
   `Forward.ValidAt.localBalls_valid` (replaces `localRecord_injective`, `mem_localBall_iff`,
   `localRecord_mem_ball_iff`, `ValidAt.localBall_valid`, `restrict_localBall`,
   `LocalTree.restrict_restrict`) and `LocalTree.canonical_planeOffspring` (replaces `follow_append`,
   `length_childList`). The remaining reachable theorems (`initial_valid`, `PlaneTree.canonical_pruneRaw`,
   `Forward.treeLaw_probability`, `Forward.localTreeLaw_probability`, `ForwardInfiniteHistory.historyKernel_markov`,
   `ForwardInfiniteHistory.fullLaw_probability`, the `ForwardAnnealed` probability instances) are copied with
   their proofs and match. A pair of candidate extra targets using `ForwardAnnealed.wordSchedule`
   (`treeLaw_eq_iid_sign_mixture`, `map_prefix_eq_iid_sign_mixture`) was dropped because `wordSchedule` itself
   contains a private auxiliary proof (`by omega`).
2. Sharing of `match` auxiliaries. Within one module Lean reuses an existing `foo.match_1` for an identical
   `match` expression. In the development `Forward.treeLaw` / `ForwardAnnealed.treeLaw` (natural-number
   recursion) and `PlaneTree.pruneRaw` / `LocalTree.follow` (list recursion) live in different modules and
   have separate matchers. `set_option bootstrap.genMatcherCode false in` is placed before `LocalTree.follow`
   and `ForwardAnnealed.treeLaw` in the Challenge; this changes the cache key of the matcher so that a fresh
   `treeLaw.match_1` / `follow.match_1` with the identical value is created, and affects no constant.
3. Sharing of auxiliary proofs. In the same way Lean reuses the nested proof `Finset.mem_Iic.mpr le_rfl`
   (abstracted as `historyKernel._proof_1`) of `ForwardInfiniteHistory.historyKernel` inside
   `ForwardAnnealed.historyKernel`, and also inside the type of its measurability proof. The two auxiliary
   theorems `ForwardAnnealed.historyKernel._proof_1` and `_proof_2` are therefore stated explicitly in the
   Challenge (with `set_option linter.auxLemma false`), and the definition refers to them. The resulting
   constants `_proof_1`, `_proof_2` and `historyKernel` are identical to the Solution's.

The Challenge is 824 lines (hard limit 1000; the aim of 700 was not reached because the closure spans about
twenty source modules, each needing its own `namespace`/`open`/`set_option` block to reproduce the elaboration
context, plus docstrings).

## Diagnostic result

`scripts/local-comparator-diagnostic.sh comparator/locallimits.json <scratch>/locallimits-diag` (local
diagnostic, not the official Comparator, not run in the Linux sandbox) printed

```
compare: statements and reachable constants match
axioms: only permitted axioms
leanchecker exit=0
```

(about 3.5 minutes; logs in this directory). Before the adjustments above the comparison failed successively at
`ForwardAnnealed.treeLaw._f`, `Forward.uniform_active_probability` and
`ForwardAnnealed.historyKernel._proof_2`. Nanoda and the other bundled checkers were not run for this group.

## After the independent review (30 October 2026)

* Docstring of `LocalTree.Tree` corrected (reviewer R1): it is the chronological closed subspace of the paper's local space, not
  the whole space of rooted locally finite labelled trees.
* Added pins: `ForwardAnnealed.fullLaw_tendsto_localLimit` (labelled a.s. convergence under the annealed law, reviewer F7) and
  `ForwardAnnealed.aemeasurable_localLimit` (the push-forward `localLimitLaw` is the genuine image measure, R6), and
  `extinctionTime_le_iff`. The config has 28 names.
* `non-vacuity/`: ported `module` versions of the reviewer's Lean checks (`Nonvac.lean`: schedules with `τ=∞` for which (III) holds
  and fails, and rows that go extinct before time `n`; `Indep.lean`: an independent restatement of T01 from the Challenge).
* Reader caveats (R2-R5, R7 of the review) are collected in `../MAIN_RESULTS_CORRESPONDENCE.md` and `../OPEN_OBLIGATIONS.md`.
