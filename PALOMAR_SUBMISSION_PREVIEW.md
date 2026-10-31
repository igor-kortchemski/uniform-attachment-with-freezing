# Four approved titles: candidate for the user's action check

The user approved these four titles on 31 October 2026. These files are local
preparation. No new workflow dispatch, registry intake, withdrawal, replacement
or registration is authorized by this preview itself.

| Selected source results | Approved title | Metadata path | Comparator configuration |
| --- | --- | --- | --- |
| T03–T04; seven conclusions | **Uniform attachment with freezing: height and distance asymptotics** | [metadata/heights.yaml](metadata/heights.yaml) | `comparator/heights.json` |
| T01–T02; three conclusions | **Uniform attachment with freezing: local limits and geometric Bienaymé trees** | [metadata/locallimits.yaml](metadata/locallimits.yaml) | `comparator/locallimits.json` |
| T05; one conclusion | **Uniform attachment with freezing: equivalence in law of the forward and reversed constructions** | [metadata/samelaw.yaml](metadata/samelaw.yaml) | `comparator/samelaw.json` |
| T06–T07; nine conclusions | **Uniform attachment with freezing: SIR epidemic and infection-tree limits** | [metadata/sir.yaml](metadata/sir.yaml) | `comparator/sir.json` |

All four entries use the same candidate commit of
`igor-kortchemski/uniform-attachment-with-freezing`. The source commit is fixed
by the local publication-candidate commit shown with the proposed action packet;
it must be a full immutable SHA in every actual request. The requested
relationship in registry intake is `maintainer`, describing Igor Kortchemski.

The request for each entry must include its matching
`formalization_metadata_path` and `comparator_config_path`. The prepared
`palomar.yml` maps each configuration to its matching metadata file. No
Challenge, Solution, compared target, proof or dependency pin was changed.

## Proposed next actions, awaiting the user's check

1. Publish the prepared candidate commit to the existing public GitHub repository.
2. Dispatch the four full mechanical preflights at that commit, selecting the
   metadata paths shown above, with the existing pinned official pipeline.
3. Inspect each resulting `mechanical-report.json` for the exact source,
   metadata/configuration hashes, selected targets and required kernel outcomes.
4. If all pass, withdraw the stale Heights registry request tied to the earlier
   title/source, then submit the four entries sequentially with these titles,
   this candidate commit and the approved maintainer relationship. Respect all
   service cooldowns and stop for inspection on an unexpected outcome.

This proposed batch excludes registration and publication of private reviews.
The user decides on those actions after seeing the returned reviews and their
exact review digests. Any material change to this proposed source or action
packet requires a fresh check by the user.

## Evidence and limits

The existing four passing reports identify source commit
`82f0ad45a60ec785a725fc419082c7d1d779b222` and the root metadata file. They are
historical evidence for the unchanged mathematical interfaces, not full
verification of these new metadata variants. Separate checks of the intermediate
single-title commit `5b57accc46299972e1569cffd328f8cfe3ee6677` were already
started before the user imposed the action-check requirement; those do not
check these new per-entry files either.

The [statement correspondence](verification/certification/MAIN_RESULTS_CORRESPONDENCE.md),
[open obligations](verification/certification/OPEN_OBLIGATIONS.md) and
[coverage report](FORMALIZATION_REPORT.md) retain every representation
qualification, proof departure and remaining whole-paper obligation. Seven
selected theorems and twenty conclusions are covered by the four interfaces;
no whole-manuscript completion or human mathematical peer review is claimed.
