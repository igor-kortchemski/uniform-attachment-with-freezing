# Heights interface (Theorems `thm:height` and `thm:lineaire`): certification notes

Files:

- Challenge: `Challenge/Heights.lean` (module `Challenge.Heights`; about 390 lines, 17 KB, imports only Mathlib).
- Solution: `Solution/Heights.lean` (module `Solution.Heights`; `public import Freezing1`).
- Configuration: `comparator/heights.json` (9 theorem names, no definition holes, permitted axioms
  `propext`, `Classical.choice`, `Quot.sound`).
- Evidence: `compare.log`, `run.log`, `leanchecker.log` (local diagnostic, see below), `INDEPENDENT_REVIEW.md`
  (independent statement review), `non-vacuity/` (machine-checked witnesses that the hypotheses are satisfiable).
- File hashes of the exact candidate files are recorded in the candidate manifest
  (`MANIFEST.sha256`, written by `scripts/export_candidate.py`).

## Targets

| Lean name | Manuscript item |
| --- | --- |
| `Freezing1.uniform_active_height_tendsto_Lp` | Theorem `thm:height` (I), tex 297-300 |
| `Freezing1.maximum_height_window_tendsto_one` | Theorem `thm:height` (II), tex 302-304 |
| `Freezing1.maximum_height_tendsto_Lp` | Theorem `thm:height` (III), tex 305-308 |
| `Freezing1.linear_heightScale_tendsto` | Theorem `thm:lineaire` (I), tex 323 |
| `Freezing1.linear_uniform_height_tendsto_Lp` | Theorem `thm:lineaire` (II), height assertion |
| `Freezing1.linear_uniform_distance_tendsto_Lp` | Theorem `thm:lineaire` (II), distance assertion |
| `Freezing1.linear_maximum_deviation_tendsto_zero` | Theorem `thm:lineaire` (III) |
| `Freezing1.linearHeightFactor_existsUnique` | uniqueness of the solution `f(c) > 1` of `f(ln f - 1) = (c-1)/(c+1)` |
| `Freezing1.linearHeightFactor_spec` | the defining property of `linearHeightFactor` |

The last two are proved inside the Challenge (they are reachable from the statement of the (III) target through
the definition of `linearHeightFactor`, a `Classical.choose`); every other body is `sorry`.

## Reading guide (matters for a reviewer)

* `hτ : ∀ n, n < extinctionTime (x n)` is the manuscript's standing assumption `τ(x^n) > n`.
* `limsup`/`liminf` in `NearOriginLimsup`/`BulkLiminf` are taken of bounded real sequences (independent review,
  section 3.1), so they are the genuine limits superior/inferior.
* Uniform-active sampling is used only in `thm:height` (I); `thm:lineaire` (II) samples among all vertices
  including frozen ones, two independent conditionally uniform vertices, diagonal included.
* `Lᵖ` convergence is `eLpNorm … (ENNReal.ofReal p) → 0` for real `p ≥ 1`.

## Independent review and non-vacuity

`INDEPENDENT_REVIEW.md`: no blocking finding; seven statements and two pinning theorems faithful
(four linear-regime statements "with documentation caveat", now documented in the Challenge docstrings).
`non-vacuity/NonVac2.lean` (all-plus rows, `c = 1`), `NonVac3.lean` (alternating rows: `ln n = o(h_n^+)`, so
`thm:height` (III) has genuine instances, and `BulkLiminf` fails there), `NonVac4.lean` (period-3 rows `c = 1/3`)
check, against the compiled `Challenge.Heights`, that all hypotheses of the statements are satisfiable.
They are ported to the `module` format. They are verification evidence, not part of the Challenge.

## Local diagnostic (NOT the official Comparator)

`scripts/local-comparator-diagnostic.sh comparator/heights.json <scratch>` exports the Challenge and the
Solution with `leanexport` and runs Lake's own `Check/Compare.lean` code (`compareAt` and `checkAxioms`) from a
compiled executable, followed by `leanchecker --from-export` on the Solution export. The official
`lake comparator` needs the Linux (bubblewrap) sandbox and was not run on this macOS machine.
The logs `compare.log`, `run.log`, `leanchecker.log` (and `kernels.log` for the kernel replays) in this directory are
those of the final candidate; they record the commit they were produced from in
`../candidate/SUMMARY.md`.

## Negative controls

See `../negative-controls/README.md` (two mutants: a changed target statement and a changed reachable definition;
both detected). Limits: two mutants only, not a substitute for the official tool.

## After the independent review (30 October 2026)

* Added a pinning target `Freezing1.extinctionTime_le_iff` (`τ ≤ n` iff the walk vanishes at some `k ≤ n`): the config now
  has 10 names, 8 of which have `sorry` bodies (the 7 main statements and this pin).
* Docstrings only (no definition or statement changed): `hτ` is the standing assumption `τ(x^n)>n`; `limsup`/`liminf` of bounded
  sequences; the `step` docstring; the pair kernel. Reviewer items F1, F3 (this file), F5, F7 are addressed.
* `non-vacuity/`: ported `module` versions of the reviewer's witnesses (all-plus rows, alternating rows with `ln n = o(h_n^+)`,
  period-3 rows with `c = 1/3`); they import `Challenge.Heights` and are verification evidence, not part of the interface.
* Not addressed (minor, documented in the review): F6 (`ℝ≥0` encoding of `|·|` and the `backward.isDefEq.respectTransparency`
  option, copied from the development), F8, F9.
