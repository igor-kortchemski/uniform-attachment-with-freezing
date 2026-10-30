# Negative controls for the local comparison diagnostic

Two deliberately wrong copies of the Heights Challenge were exported with `leanexport` and compared to the
unchanged Solution export with the same diagnostic (Lake's own `compareAt`), using the same target list:

| Mutant | Change | Result |
| --- | --- | --- |
| A | the statement of `maximum_height_window_tendsto_one`: lower bound `1 - ε` replaced by `1 + ε` | `COMPARE FAILED: Challenge and solution theorem statement do not match: 'Freezing1.maximum_height_window_tendsto_one'` |
| B | the definition `heightScale`: `1 / activeCount x (i+1)` replaced by `1 / activeCount x i` | `COMPARE FAILED: Const does not match between challenge and target 'Freezing1.heightScale'` |

Both detections were observed on 30 October 2026 (exit code 1). They show that the diagnostic distinguishes a
changed target statement and a changed reachable definition; they do not replace the official Comparator.
The mutant modules were deleted after the run.

## Further controls (30 October 2026, later run)

`run-controls.py` (same directory) builds deliberately wrong copies of `Challenge/Heights.lean` as temporary modules, runs the
diagnostic against the unchanged `Solution.Heights` and deletes them. The checks below concern definitions *inside* the forward process
and a Solution that contains a hole, which the first two controls did not cover:

| Mutant | Change | Result |
| --- | --- | --- |
| C | `transitionLaw`: uniform choice over all vertices instead of the active ones | `COMPARE FAILED: Const does not match between challenge and target 'Freezing1.Forward.transitionLaw'` |
| D | `forwardPairKernel`: second vertex uniform among active vertices only | `COMPARE FAILED: Const does not match between challenge and target 'Freezing1.CanonicalTree.forwardPairKernel'` |
| E | `step`: attachment and freezing swapped | `COMPARE FAILED: Const does not match between challenge and target 'Freezing1.Forward.step'` |
| S | the Solution module is the Challenge itself (its target proofs are `sorry`) | `AXIOMS FAILED: Illegal axiom detected: 'sorryAx'` (statements and reachable constants match, as they should) |

All four were rejected. Control S was run by pointing `solution_module` of a copy of `comparator/heights.json` at `Challenge.Heights`.
They still show only that the local diagnostic (Lake's own comparison code) discriminates; they do not replace the official Comparator.
No control for a non-standard axiom other than `sorryAx` was run.

