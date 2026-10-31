# Public candidate and full Palomar mechanical checks

Publication destination: [igor-kortchemski/uniform-attachment-with-freezing](https://github.com/igor-kortchemski/uniform-attachment-with-freezing).

On 31 October 2026, Igor Kortchemski authorized preserving the old repository
and its manuscript history privately as `uniform-attachment-with-freezing-private`,
then creating a fresh public repository at the original name, pushing the
reviewed candidate, and running all four full Palomar mechanical checks.

At this source snapshot, publication and those checks are pending execution.
The reports will identify the exact 40-character source commit and the selected
configuration; this file does not predict their outcome. The completed standalone
Linux verification remains in [../linux/SUMMARY.md](../linux/SUMMARY.md).

| Interface | Configuration | Workflow |
| --- | --- | --- |
| Heights, T03–T04 | `comparator/heights.json` | `palomar.yml`, mode `full` |
| Local limits, T01–T02 | `comparator/locallimits.json` | `palomar.yml`, mode `full` |
| Same law, T05 | `comparator/samelaw.json` | `palomar.yml`, mode `full` |
| SIR, T06–T07 | `comparator/sir.json` | `palomar.yml`, mode `full` |

All runs use the pinned official pipeline
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7` and the official
`palomar-standard-v1` execution profile. Policy HEAD
`28bd48b9b71bbb2a82c718ce761d5a4220ef8e60`, the toolchain policy and
Challenge dependency allowlist were refreshed on 31 October 2026 and remain
unchanged from the content review.

The recorded relationship is: “Running on behalf of Igor Kortchemski, the
responsible maintainer and a coauthor of the source article, with his explicit
authorization to publish the candidate and run these mechanical checks.”
No human review is inferred from that authorization.

Completion requires inspecting every `mechanical-report.json`, including its
source/configuration/pipeline identities, completed statuses, and mandatory
Lean and NanoDa outcomes. A successful workflow label alone is insufficient.
These checks do not submit or register results in Palomar.

The mathematical scope remains seven selected theorems and twenty conclusions,
with the [statement qualifications](../MAIN_RESULTS_CORRESPONDENCE.md) and
[whole-paper obligations](../OPEN_OBLIGATIONS.md). The source TeX is omitted
from this public candidate and its reachable history.
