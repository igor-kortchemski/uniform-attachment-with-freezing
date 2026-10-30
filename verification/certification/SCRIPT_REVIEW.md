# Independent review of verification failure propagation and Linux preparation

Scope: the local script/CI patch on candidate baseline
`4b3e78c6b9cd9db80f1b63fd85046e2805589123`. The reviewer did not author the
patch and did not change script, workflow, configuration or mathematical
source. This is a code review, not a mathematical or Palomar certificate.

Reviewed `verification.py`, the three existing shell wrappers,
`run-linux-checks.sh`, `check-axiom-log.py`, `summarize-evidence.py`,
`test_verification.py` and the CI/Comparator workflows.

## Verdict

No unresolved concrete failure-propagation defect was found in the final
reviewed version. The original success-masking shell pipelines have been
replaced with a single subprocess runner that records and propagates actual
child statuses. Missing executables, failed exports/compilation/comparison,
failed selected kernels and missing expected success records fail closed.
This verdict does not establish that the unrun Linux workflow will succeed.

## Confirmed properties

- Shell entry points use `exec` rather than masking a child behind `tee` or
  a final successful `echo`. Arguments are passed as subprocess vectors;
  paths with spaces and configuration contents are not shell-evaluated.
- Export stdout is written to the NDJSON file, while stderr goes to a
  separate diagnostic log. A successful export must also be nonempty.
  Comparison must return zero and provide both expected confirmations.
- Every one of the six selected replay programs is required. The first
  failure or missing binary stops the command and produces a failed
  completion record. NanoDa uses strict unpermitted-axiom errors.
- A new or empty output directory is required. Existing evidence is
  rejected and preserved instead of being overwritten or silently reused.
- Collection and Linux checks require a clean identified checkout both
  before and after checking, with unchanged commit and tree. Evidence
  directories for those commands must be outside the checkout.
- Comparison records SHA-256 identities for both exports and the
  configuration; comparison/replay also recheck their inputs at the end.
  The summarizer rehashes the current exports and requires agreement with
  both comparison and replay records and the replay log.
- The summary requires complete per-command status sets, completed success
  markers, valid commit/tree and configuration digests, exact comparison
  confirmations and all selected kernel exits. It prints a passing table
  only after validating the whole run. Empty or subset standard-axiom
  closures are allowed; forbidden axioms, duplicate reports, missing names
  and Lean error output are rejected.

## Independent findings fixed during this review

1. The first patch checked source identity only at the start. An edit or
   branch move during the long run could otherwise receive a final
   passing record under the old identity. The final patch adds
   `finish_identity` to collection and Linux modes, plus dirty-checkout
   and moved-commit failure injections.
2. The first summary patch did not compare its recorded solution digest
   to the actual export. The reviewer reproduced the problem with the
   existing fake-checker fixture: after a successful collection, replacing
   `heights/solution.ndjson` still produced a passing summary. The final
   code binds both exported files to comparison records and binds replay
   to the same solution/configuration, rejecting missing or changed files.
3. The intermediate digest comparison permitted two absent configuration
   digests to compare equal as `None`. The final code requires valid
   64-hex digests for every comparison, including the auxiliary interface,
   and for every replay before accepting equality.

The failure-injection suite exercises the real process boundaries with
fake external programs. It includes failures at export, compilation,
linking, comparison, every selected checker, source/axiom checks, stale
output, changed exports and changed checkout identity. These tests verify
script behavior; they do not run mathematical proof checkers. The root
coordinator separately records the final suite result and actual narrow
comparison/replay smoke checks.

## Linux and claim boundaries

The Linux entry point refuses non-Linux execution and never bypasses the
sandbox. It invokes the official `lake comparator` separately for the four
main interfaces and the auxiliary configuration. Runtime configurations
retain the submitted targets and permitted axioms and explicitly set
`enable_nanoda` to true. This is necessary: the pinned Lake v4.35.0
`lake/Lake/CLI/Check.lean:649–656` defaults the optional flag to false.

The manual Comparator workflow installs the pinned, hash-checked Palomar
Bubblewrap, checks the committed manifest, runs the script, and preserves
exact-commit diagnostics even on failure. CI and Comparator jobs have
read-only repository permissions. Preparing these files neither dispatches
a workflow nor pushes, publishes or changes visibility.

Local replay, an official sandboxed Lake comparison and the complete
Palomar mechanical report remain distinct evidence levels. The scripts
set `official_palomar_report` to false; neither a future successful Linux
run nor the local smoke checks is labelled as the complete Palomar report.
No remote run, Linux run or publication was performed by this reviewer.
