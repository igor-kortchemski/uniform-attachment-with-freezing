# Metadata filename rejection at 174e765

All four full checks stopped during input validation, before Lean ran.
The exact error was `Formalization metadata path must name formalization.yaml`.
The rejected paths were `metadata/<entry>.yaml`. They are corrected in the
new local candidate to `metadata/<entry>/formalization.yaml`.

Checked source: `174e765a41ebc36e01ee3d37630a4617a5073295`.
Pipeline: `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`.

| Interface | Failed run | Raw report |
| --- | --- | --- |
| heights | [Run](https://github.com/igor-kortchemski/uniform-attachment-with-freezing/actions/runs/41192033092) | [heights.json](heights.json) |
| locallimits | [Run](https://github.com/igor-kortchemski/uniform-attachment-with-freezing/actions/runs/41192036483) | [locallimits.json](locallimits.json) |
| samelaw | [Run](https://github.com/igor-kortchemski/uniform-attachment-with-freezing/actions/runs/41192039962) | [samelaw.json](samelaw.json) |
| sir | [Run](https://github.com/igor-kortchemski/uniform-attachment-with-freezing/actions/runs/41192043737) | [sir.json](sir.json) |

No registry request was withdrawn, replaced or created as a result of these
failed checks. The user-approved batch required all four checks to pass first.
The exact approved titles, selected targets, statement definitions, proofs and
toolchain/dependency pins are unchanged by the filename correction.
The corrected source must pass its own full preflights before intake.
