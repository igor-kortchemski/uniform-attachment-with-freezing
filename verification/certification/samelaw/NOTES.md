# Palomar Challenge/Solution pair for Theorem `thm:samelaw` (group T05)

Files: `Challenge/SameLaw.lean` (module `Challenge.SameLaw`, 680 lines),
`Solution/SameLaw.lean` (imports `Freezing1`), `comparator/samelaw.json`.
Evidence in this directory: `compare.log`, `run.log`, `leanchecker.log` (final run) and
`compare-attempt1-failed.log` (first run, see "Adjustments").

## Result (local diagnostic, not the official Comparator)

`scripts/local-comparator-diagnostic.sh comparator/samelaw.json <scratch>/samelaw-diag` prints

    compare: statements and reachable constants match
    axioms: only permitted axioms

and `leanchecker --from-export` on the Solution export exits 0. The diagnostic takes about 2 minutes on
this machine for this pair. `Challenge/SameLaw.lean` direct check
(`lake env lean -DautoImplicit=false Challenge/SameLaw.lean`) gives only `declaration uses sorry` warnings
(24, one per target); the recorded artifact build passes.

## Targets (24 theorems; each a `sorry` body in the Challenge, listed in `comparator/samelaw.json`)

Main target (manuscript Theorem `thm:samelaw`, tex lines 661-664; Algorithm 1 at tex 424-436,
Algorithm 2 at tex 527-538):

* `Freezing1.CanonicalTree.construction_laws_eq`: for every schedule `x` and `n <= extinctionTime x`,
  `forwardLaw x n = reverseLaw x n`.

Extra targets, copied with their exact statements; they pin down the meaning of the objects:

* Probability/non-triviality: `CanonicalTree.forwardLaw_probability`, `CanonicalTree.reverseLaw_probability`
  (both laws are probability measures; in the source they are `instance`s of a `Prop` class, hence theorems;
  they are stated with the keyword `theorem` in the Challenge); `uniformRootPair_isProbabilityMeasure`.
* Algorithm 1 (forward law): `Forward.transitionLaw_apply` (uniform choice among the active vertices),
  `Forward.treeLaw_valid` (support in valid trees, via the structure `Forward.ValidAt`),
  `Forward.treeLaw_isTree`, `Forward.treeLaw_counts` (`S_n` active vertices and `plusCount + 1` vertices).
* Algorithm 2 (reverse law): `ReverseStamped.joinChoice_edgeTime` (a merge stores its time at the second
  root), `ReverseStamped.treeLaw_forest_isTree`, `ReverseStamped.treeLaw_canonical_ids` (edge times are
  injective on vertices with value set `{0} ∪ attachmentTimes`), and the deterministic operations
  `RootedForest.join_roots`, `RootedForest.join_graph` (a merge adds exactly the edge between the roots),
  `RootedForest.adjoin_roots`, `RootedForest.adjoin_graph` (inserting a fresh isolated root).
* The common observable: `CanonicalTree.forward_frozen_iff`, `CanonicalTree.reverse_frozen_iff`,
  `CanonicalTree.reverse_adj_iff`, `CanonicalTree.transportGraph_adj_iff` (what the frozen pairs and the
  graph of the observables are), `CanonicalTree.forward_edge_time` (the label of a forward parent edge is the
  larger endpoint identifier), `CanonicalTree.forwardLaw_vertices`, `CanonicalTree.reverseLaw_vertices` (both
  laws have the same canonical identifier set `{0} ∪ attachmentTimes`),
  `CanonicalTree.treeLaw_reverse_graph_isomorphic` (the reverse observable graph is isomorphic to the forest
  graph).

Dropped after a first draft (cheap but redundant, to keep the file short): `join_vertices`,
`adjoin_vertices`, `transitionLaw_eq_dirac_of_empty`, `reverse_active_iff`, `mem_frozenPairs`.

## Copied declarations (all verbatim from the source modules; docstrings rewritten)

| Source module | Declarations |
| --- | --- |
| `Path` | `SignSequence`, `plusCount`, `activeCount` |
| `Extinction` | `extinctionTime` |
| `ForwardTree` (`Freezing1.Forward`) | `State`, `initial`, `attach`, `freeze`, `step`, `ValidAt`, `State.tree` |
| `ForwardLaw` (`open MeasureTheory`, `open scoped ENNReal Classical`) | `instance : MeasurableSpace State := ⊤`, `transitionLaw`, `treeLaw` |
| `RootedForest` | `RootedForest` (structure, with proof fields), `isolated`, `roots`, `mem_roots`, `depth_eq_zero_iff`, `parent_of_root`, `join`, `graph`, `adjoin`, `toGraph` |
| `UniformRootPair` | `uniformRootPair` (with `variable {V} [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V]`) |
| `ReverseForest` (`Freezing1.Reverse`) | `Forest`, `initial` |
| `ReverseStampedForest` (`Freezing1.ReverseStamped`) | `Forest`, `instance : MeasurableSpace Forest := ⊤`, `initial`, `joinChoice`, `insertLabel`, `joinLaw`, `transitionLaw`, `lawAfter`, `treeLaw` |
| `ReverseTimestampSupport` | `attachmentTimes` |
| `CanonicalTreeObservable` (`Freezing1.CanonicalTree`) | `Observable`, `instance : MeasurableSpace Observable := ⊤`, `edgeTime`, `frozenPairs`, `transportGraph`, `forward`, `reverseLabel`, `reverse`, `forwardLaw`, `reverseLaw` |
| `ConstructionEquivalence` | target `construction_laws_eq` only |

Each source module is reproduced in its own `namespace`/`open`/`section`/`variable` context (the only `set_option`s
of these modules, `backward.isDefEq.respectTransparency false` in `ForwardTree` lines 244 and 260, belong to theorems
that are not reachable from the statements and were not copied). The closure includes the proof terms of the
`RootedForest` structure fields of `isolated`, `join`, `adjoin`, `graph`, `transportGraph`; these are copied with
their original tactic proofs.

## Imports (Mathlib only; union of the Mathlib `public import`s of the 37 project modules in the transitive
## import closure of the source modules)

`Mathlib.Algebra.BigOperators.Group.Finset.Basic`, `Mathlib.Basic.Real.Basic`,
`Mathlib.Combinatorics.SimpleGraph.Acyclic`, `Mathlib.Combinatorics.SimpleGraph.Metric`,
`Mathlib.Data.ENat.Lattice`, `Mathlib.Data.Finset.Prod`, `Mathlib.Data.Finset.Sum`,
`Mathlib.Data.Fintype.Perm`, `Mathlib.Data.Nat.Choose.Cast`, `Mathlib.Data.Nat.Factorial.Basic`,
`Mathlib.Logic.Equiv.Basic`, `Mathlib.MeasureTheory.Measure.Dirac.Basic`,
`Mathlib.MeasureTheory.Measure.ProbabilityMeasure`, `Mathlib.MeasureTheory.Measure.Typeclasses.Probability`,
`Mathlib.Probability.Distributions.Uniform`, `Mathlib.Tactic`.

## Adjustments needed beyond verbatim copying (the first diagnostic failed:
## `Const does not match between challenge and target 'Freezing1.RootedForest.join._proof_8'`)

Using a script that continues past the first mismatch (a copy of Lake's `compareAt` that collects all
failures), exactly three independent problems were found; everything else matched on the first try.

1. **Private auxiliary lemmas carry the module name.** The proof of the field `depth_parent` of
   `RootedForest.join` and the proof of `RootedForest.depth_eq_zero_iff` use `omega`, which stores an auxiliary
   lemma in a private context. In the module system its name is `_private.<module>.0.<name>`; in the
   development this is `_private.Freezing1.RootedForest.0.Freezing1.RootedForest.join._proof_7` and
   `..depth_eq_zero_iff._proof_1_1`, which cannot be produced by a file named `Challenge.SameLaw`. Both are
   reachable from the statement through the *value* of `join` (and so Comparator requires them to agree).
   Fix used: around the `RootedForest` block only, the file runs
   `open Lean in run_cmd modifyEnv (·.setMainModule `Freezing1.RootedForest)` and restores
   `` `Challenge.SameLaw`` right after the block. This changes no declaration or statement, but it is
   environment metaprogramming inside a Challenge file: it is documented by a comment at the place of use and
   the maintainers should decide whether it is acceptable for the Palomar submission. Without it the
   `RootedForest.join` constant cannot match. A hack-free alternative would require a project change
   (proofs of `join`/`depth_eq_zero_iff` that create no private auxiliary lemma, e.g. term-mode or
   `Nat.add_right_cancel`-style arguments instead of `omega`), which this task forbade.
2. **Matcher reuse inside one file.** `Forward.treeLaw`, `Reverse.lawAfter` and `ReverseStamped.lawAfter` all
   use the same matcher (`Nat.casesOn`, patterns `0` and `k+1`). In the development each module creates its own
   `match_1` (`Forward.treeLaw.match_1`, `ReverseStamped.lawAfter.match_1`) since Lean reuses matchers only within a
   file; in the single Challenge file `ReverseStamped.lawAfter` reused `Forward.treeLaw.match_1`, so
   `ReverseStamped.lawAfter._f` differed and `ReverseStamped.lawAfter.match_1` was missing.
   Fix used: `set_option bootstrap.genMatcherCode false in` on `ReverseStamped.lawAfter` (the matcher cache key
   contains this code-generation flag; the kernel constants are unchanged).
3. Instances of `Prop` classes (`forwardLaw_probability`, `reverseLaw_probability`) are theorems in the
   environment; they are written `theorem ... := by sorry` in the Challenge (no instance attribute needed).

Other (harmless) differences: docstrings are new; `@[simp]` is not copied onto the extra target theorems (they
are stated, not used); a few source declarations that are not reachable from the statements were not copied
(e.g. `root_mem_roots`, `join_vertices`, `join_depth`).

## Statement-fidelity observations (reported, not fixed; see the final report of the worker)

1. Both random trees are encoded by the canonical `Observable` (ids = birth times/incoming edge times; the root
   has id `0`; edge labels are not stored but equal the larger endpoint id). Theorem `thm:samelaw` is therefore
   formalized as equality of the laws of these canonical encodings rather than literally of isomorphism classes of
   rooted edge- and vertex-labelled trees; the encoding is faithful (pinned by the extra targets above), but the
   identification is part of the formalization, not of the statement.
2. Tex line 312 (introduction) describes Algorithm 2 with the roles of `+1` and `-1` swapped (adding a one-vertex
   tree on `+1`, merging on `-1`); Algorithm 2 itself (tex 527-538) and the Lean formalization add the tree on `-1`
   and merge on `+1`, which is the only choice compatible with `S_{i-1} = S_i - X_i`.
3. Fallbacks outside the theorem's hypothesis (invalid choices in `Forward.step`, fewer than two roots in
   `ReverseStamped.joinLaw`, `invalid pair` in `joinChoice`, `.toNat` of a negative `S_n`) never occur for
   `n <= extinctionTime x`; the theorem is only claimed under that hypothesis, matching the paper's `0 <= n <= tau`.

## After the independent review (30 October 2026)

* Added the pin `extinctionTime_le_iff` (review F3); the config has 24 names. Reviewer items F4-F7 (a reverse `joinLaw_apply`
  analogue, an edge-time monotonicity statement, a reverse count target, the canonical-id/isomorphism bridge) are *not* done:
  the statements are faithful without them (review sections 4-5) and the bridge is argued in the review, not proved in Lean.
* The review rates the `setMainModule` device (lines near 192 and 408) and `bootstrap.genMatcherCode false` (near 502) as a
  possible reason for a Palomar reviewer to object (F1 medium, F2 low). They are kept, disclosed in `formalization.yaml` and
  `../OPEN_OBLIGATIONS.md`; the alternative is a refactor of the development so that reachable definitions create no
  tactic-generated private auxiliaries.
