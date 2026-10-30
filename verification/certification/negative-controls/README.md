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
