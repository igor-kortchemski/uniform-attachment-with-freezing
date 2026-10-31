# Metadata for the four approved entry titles

The root `formalization.yaml` describes the whole formalization project. Each
file here describes one selected result group and uses its user-approved title.
The compared statements, definitions, proofs and dependencies are unchanged.

| Group | Metadata path | Comparator configuration | Source results |
| --- | --- | --- | --- |
| Heights | `metadata/heights/formalization.yaml` | `comparator/heights.json` | T03–T04, seven conclusions |
| Local limits | `metadata/locallimits/formalization.yaml` | `comparator/locallimits.json` | T01–T02, three conclusions |
| Constructions | `metadata/samelaw/formalization.yaml` | `comparator/samelaw.json` | T05, one conclusion |
| SIR | `metadata/sir/formalization.yaml` | `comparator/sir.json` | T06–T07, nine conclusions |

`formalization_metadata_path` must select the matching file in both the full
mechanical preflight and registry intake. The local workflow maps the selected
Comparator configuration to the matching metadata file automatically.

All mathematical qualifications and project-wide obligations remain in
[the source correspondence](../verification/certification/MAIN_RESULTS_CORRESPONDENCE.md),
[open obligations](../verification/certification/OPEN_OBLIGATIONS.md) and
[FORMALIZATION_REPORT.md](../FORMALIZATION_REPORT.md).

The existing passing reports identify earlier commits and metadata paths.
These new metadata files require full verification at their own exact source
commit before intake. The user requires checking the exact proposed actions
before any further Palomar submission or change; title approval does not
register a result or authorize publication of a private review.
