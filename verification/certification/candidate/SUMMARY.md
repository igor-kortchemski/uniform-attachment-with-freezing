# Evidence summary of the local candidate

All results below are LOCAL runs on one macOS machine (Darwin 23.6, no Linux sandbox). None of them is the official
`lake comparator`, the official NanoDa/kernel replay of the Palomar pipeline, or the Palomar mechanical report.

## Identity

* Source commit of the candidate that was built: `ab3d936089e44a44ec3e13cc5f354b29b6ed92c1`; tree `b0cf2f15ca3e2ad7b06693dc20f1ca842067fd30`.
* Toolchain: `leanprover/lean4:v4.35.0`. Collected 2026-10-30T15:48:31Z to 2026-10-30T17:03:25Z.
* Git status at collection time (must be empty): empty

## Fresh build

`lake build Freezing1 Challenge Solution` from an empty `.lake/build` (pinned Mathlib packages symlinked): 4645 jobs, exit 0, 1391.80 s wall time. `declaration uses sorry` warnings occur only in `Challenge/*` (73 = the number of Challenge targets with a hole).

## Source scan and axioms

* `scripts/check-sources.py`: exit 0.
* `scripts/AxiomAudit.lean`: exit 0; Checked 8683 Freezing1 declarations; all transitive axioms belong to propext, Classical.choice, Quot.sound.
* `scripts/MainResultsAxioms.lean` + `scripts/check-axiom-log.py`: exit 0; 26 entries, 0 with axioms other than ['Classical.choice', 'Quot.sound', 'propext']

## Local comparison and kernel replays

| Interface | compare | axioms | leanchecker | NanoDa | leanchecker-paranoid | lean4lean | con-leche | con-ron | solution export SHA-256 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| heights | match | permitted only | exit 0 | exit 0 | exit 0 | exit 0 | exit 0 | exit 0 | `b112b3701a08aba0…` |
| locallimits | match | permitted only | exit 0 | exit 0 | exit 0 | exit 0 | exit 0 | exit 0 | `e9194ff2398a2cc2…` |
| samelaw | match | permitted only | exit 0 | exit 0 | exit 0 | exit 0 | exit 0 | exit 0 | `845be3b9664f49e9…` |
| sir | match | permitted only | exit 0 | exit 0 | exit 0 | exit 0 | exit 0 | exit 0 | `589d95b599ea3d22…` |
| auxiliary | match | permitted only | not run | not run | not run | not run | not run | not run | `-…` |

(The `auxiliary` row is the old `comparator.json`; kernel replays are not run for it. NanoDa and the other checkers are invoked as in Lake's own `Check.lean`; leanchecker is Lean's own kernel.)

## Probes

All top-level module-headed probes `verification/*.lean` (including the nine ports of `verification/candidate-ports/`) compiled against the candidate: 156 files, 156 exit 0.
