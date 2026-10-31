# Four passing full Palomar mechanical checks

**All four passed**, at public source commit
`82f0ad45a60ec785a725fc419082c7d1d779b222`.

Repository: [igor-kortchemski/uniform-attachment-with-freezing](https://github.com/igor-kortchemski/uniform-attachment-with-freezing).
The checked snapshot is preserved by tag `palomar-checked-2026-10-31`.
Later report/documentation commits do not change the identity of these runs.

| Interface | Source results | Targets | Full run | Lean | NanoDa | con-ron |
| --- | --- | ---: | --- | --- | --- | --- |
| [heights](heights/mechanical-report.json) | T03–T04 | 10 | [Pass](https://github.com/igor-kortchemski/uniform-attachment-with-freezing/actions/runs/41158872177) | Accept | Accept | Accept |
| [locallimits](locallimits/mechanical-report.json) | T01–T02 | 28 | [Pass](https://github.com/igor-kortchemski/uniform-attachment-with-freezing/actions/runs/41158875891) | Accept | Accept | Accept |
| [samelaw](samelaw/mechanical-report.json) | T05 | 24 | [Pass](https://github.com/igor-kortchemski/uniform-attachment-with-freezing/actions/runs/41158879881) | Accept | Accept | Accept |
| [sir](sir/mechanical-report.json) | T06–T07 | 13 | [Pass](https://github.com/igor-kortchemski/uniform-attachment-with-freezing/actions/runs/41158883732) | Accept | Accept | Accept |

The 75 selected targets include twenty manuscript conclusions and supporting
model/definition pins. They are not 75 manuscript theorems. Each raw report is
retained byte-for-byte, alongside the GitHub workflow-run metadata.
[AUDIT_RESULTS.json](AUDIT_RESULTS.json) records report hashes and inspected identities.

## What was checked

Each report has `status: pass`, `stage: complete`, and no errors. Inspection
matched the repository, full source SHA, selected configuration and its SHA-256,
exact theorem list, permitted axioms, Challenge/Solution source hashes, metadata,
Lakefile and dependency-manifest hashes to the checked snapshot. GitHub run metadata
authenticates the referenced official reusable workflow at pipeline commit
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`.

All runs use mode `full` and the official `palomar-standard-v1` profile
(profile SHA-256 `94fcd7906a1b6c076c0036d742e1c5add8625e49bb474818ec8924576dbf0caa`).
The submitted toolchain remains Lean/Mathlib v4.35.0. The official pipeline supplies
a separately authenticated con-ron update from Lean v4.36.0-rc1; this does not
change the submitted compiler, Lake, NanoDa, exporter or dependency pins.

Each report records all 826 Lean sources checked, high-trust allowlisted Challenge
dependencies and no untrusted statement sources. The Comparator log explicitly
records NanoDa acceptance, Lean default-kernel acceptance and `Your solution is okay!`.
The independent con-ron replay was accepted with exit zero in every run.

The sole warning in each report is that the Challenge exceeds the preferred
32 KiB / 300-line review surface. All satisfy the mandatory 100 KiB / 1,000-line
limits. The full mechanical pipeline accepted the existing private-name/matcher
devices; this does not establish an editorial or registration outcome.

The ordinary build and axiom-audit [CI run](https://github.com/igor-kortchemski/uniform-attachment-with-freezing/actions/runs/41158682496)
also passed on this exact source commit. The earlier standalone Linux checks
remain in [../linux/SUMMARY.md](../linux/SUMMARY.md).

## Repository preservation and initial input failures

The previous repository, including its manuscript and old history, remains private
as `igor-kortchemski/uniform-attachment-with-freezing-private`, repository ID
1438224608, with its original main commit `ee1aa1228a49b4df2432b696ee65bd188e482353`.
The fresh public repository has a different ID, 1440417932, and contains only
the reviewed candidate history. Anonymous Git access to the checked public SHA
and preservation of the private repository were verified.

The four initial attempts stopped before Lean because a descriptive authorization
string was not one of the fixed accepted categories. Their reports are preserved
under [initial-input-rejections/](initial-input-rejections). The corrected runs use
`I have approval from a responsible author or maintainer`, recorded as `approved`.
Igor Kortchemski explicitly authorized publication and these checks. No mathematical
source changed between the rejected-input attempts and the passing runs.

## Scope and remaining obligations

These are full official mechanical preflights. No registry intake, editorial
decision or registration has occurred. The selected scope remains seven main
theorems and twenty conclusions, subject to the
[statement qualifications](../MAIN_RESULTS_CORRESPONDENCE.md). Automated statement
audits are not human peer review.

Whole-manuscript coverage is incomplete: A85–A86, literal L13, A06 GHP/dendron,
A87 stochastic domination/future-conditioning and explicit A24/A67/A73 couplings
remain open. L03, L04 and the upper part of P03 retain corrected formalizations
because their printed versions are false. Alternative proof routes do not validate
the bypassed paper arguments. See [../OPEN_OBLIGATIONS.md](../OPEN_OBLIGATIONS.md).
