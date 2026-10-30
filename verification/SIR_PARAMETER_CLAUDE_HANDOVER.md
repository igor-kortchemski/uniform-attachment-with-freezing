# Checkpoint for Claude: parameter worker

Stopped at the user's request on 2026-10-30. No proof process or imported probe is running in this worker. No A07 implementation was started. Do not rerun completed checks merely because this worker stopped.

## Build ownership and trust

The integrating agent alone writes Lake artifacts. This worker only runs direct checks with `lake env lean -DautoImplicit=false FILE`, without `-o`. Preserve the pinned Lean/Mathlib versions and frozen proof modules. No holes, custom axioms, or native evaluation are allowed. Mathematical Markdown uses `$...$` and standalone `$$` delimiters.

## A77: finished and checked

The ten `SIRCaptureCoefficient*.lean` modules are frozen. The final source interfaces prove unconditional same-epsilon reverse-birth and chronological uniform-vertex capture, including two conditionally independent samples from the same actual tree, for every $0<\varepsilon<t_0$ and the literal source rate-ratio assumption. Product sampling is formed before tree/environment mixing; no unconditional independence is claimed. Reverse recovery-label birth clocks and chronological membership remain explicitly distinguished.

Root artifact evidence: `verification/capture-source-pairs-one-susceptible-build.log`, PASS 4114 jobs, root session 94060 closed. The ordinary imported authored probe `verification/SIRCaptureCoefficientStatements.lean` passed with exit code zero: eight expanded examples and 31 axiom queries, all exactly `[propext, Classical.choice, Quot.sound]`. Its log is `verification/sir-capture-coefficient-statements.log`; worker session 23545 closed. The earlier source-combined probe also passed eight examples / 31 queries.

`verification/SIR_CAPTURE_COEFFICIENT_PROOF_NOTES.md` has been updated from pending to this real evidence. Root independently checked six expanded examples / 12 closures. The source-review worker independently reviewed pair semantics in `verification/SIR_CAPTURE_PAIR_INDEPENDENT_AUDIT.md`; keep that independent semantic review distinct from this worker's authored mechanical probe.

This worker also independently reviewed root `CanonicalReverseBirthClock.lean` while consuming it. Exact clock transport, held-after-extinction behavior, active fallback, and all-vertex sampling are covered by the A77 notes and probe.

## RecursiveTreeLaw: independent probe prepared, not run

Root `Freezing1/RecursiveTreeLaw.lean` is frozen and direct-check PASS with zero diagnostics. Root reported it included in global build session 44711; this worker received no artifact-ready notification before stopping and has not compiled against that artifact.

Unbuilt/draft review files owned by this worker:

- `verification/RecursiveTreeIndependentStatements.lean`: five expanded examples and six axiom queries. It checks full-state equality with an independently specified fresh uniform-parent recursive law, actual vertex/active cardinalities, independently derives the old-state/new-parent product recursion, checks the one-step two-vertex count, and transports the newest-parent marginal to the original forward law.
- `verification/RECURSIVE_TREE_LAW_INDEPENDENT_AUDIT.md`: complete source/body semantic review; evidence paragraph correctly remains pending an ordinary imported compile. No mechanical PASS is claimed there.

After the root confirms the artifact, run:

```sh
lake env lean -DautoImplicit=false verification/RecursiveTreeIndependentStatements.lean > verification/recursive-tree-independent-statements.log 2>&1
```

If necessary, repair only the probe. In particular the independent product-recursion example has not yet elaborated. Then update the audit with actual evidence and report to the integrating agent. The correct size is $n+1$ vertices after $n$ steps, including the root; this is the existing S05 correction. The separate finite symmetric-sign, extinction-conditioned uniform-plane example remains an A03 obligation owned by the source-review worker. This recursive-law module does not close all A03.

## Next assigned obligation A07: inspection only

Root assigned the actual all-positive reverse forest projected onto partitions of its $n+1$ original labels: independently specify the uniform unordered-block-pair merge kernel, prove the genuine forest projection, and identify the entire embedded Kingman jump-chain law. No continuous-time holding-time claim is intended. Preserve S05's introductory sign reversal and count correction. The precise Algorithm 2 merges on positive steps and inserts on negative steps.

Read source lines 311, 523–536, and 2346 and these existing modules:

- `ReverseForest.lean`: `Reverse.initial`, `transitionLaw`, `lawAfter`, `lawAfter_valid`; all-positive reverse transitions are actual `RootedForest.joinLaw`.
- `ReverseHistory.lean`: genuine coherent history law `lawAfter`, `fullLaw`, `stage`, `push`, exact marginal and history-length identities.
- `RootedForest.lean`, `RootedForestLaw.lean`: actual `root`, `roots`, `join`, `joinChoice`, `joinLaw` and validity/support lemmas.
- `RootedForestCoalescence.lean`: `root_eq_iff_reachable`, exact `joinChoice_root`, merge/coalescence characterization.
- `UniformRootPair.lean`: actual ordered-root-pair uniform law and exact unordered-pair mass $1/\binom{S}{2}$.

Installed Mathlib has `Mathlib.Order.Partition.Finpartition`: genuine finite partitions with finite nonempty pairwise-disjoint blocks, `ofSetoid`, `ofExistsUnique`, `part`, and discrete partitions. A possible carrier is a `Finpartition` of `Finset.univ : Finset (Fin (n+1))`, projected from equality of actual component roots; a genuine block-union merge and uniform unordered pair law still need construction and proof. This is only an inspected route, not a theorem or a settled design. No `KingmanPartition*.lean` or `ReverseKingman*.lean` file was created by this worker.

## Other completed independent evidence

Root late-Bennett modules were independently reviewed against source 2326–2330 in `verification/SIR_LATE_BENNETT_INDEPENDENT_AUDIT.md`. Ordinary imported probe `verification/SIRLateBennettIndependentStatements.lean` passed six expanded examples / eight standard-axiom closures; log `verification/sir-late-bennett-independent-statements.log`, session 41763 closed. Scope is the exact scalar rate-function asymptotic and positive-small-mean consequence plus corrected actual fixed-word tail with threshold $1+D+a$, factor $2n+2$, and the zero-charge branch. It does not certify the still-open conditional per-vertex Bernoulli domination or all A87.
