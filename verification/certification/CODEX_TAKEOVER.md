# Codex takeover: interface audit and verification repairs

Base candidate: `4b3e78c6b9cd9db80f1b63fd85046e2805589123`, taken over on
30 October 2026. Its mathematical source was built at
`ab3d936089e44a44ec3e13cc5f354b29b6ed92c1`. Existing proof implementations,
Challenge/Solution files, comparison targets, toolchain and dependency pins
were preserved. No upload, push, workflow dispatch or visibility change occurred.

## Four-interface audit

The reviewers reconstructed the source statements, read the definitions and
relevant implementation dependencies, and wrote new imported statement probes.
They did not author the audited interfaces. These are automated independent
reviews, not human peer review or an official Palomar editorial decision.

| Interface | Compared targets | Verdict and qualification |
| --- | --- | --- |
| Heights | 10 | No blocking mismatch in T03/T04, including real powers, joint sampling, nested assumptions and boundaries. [Audit](heights/CODEX_AUDIT.md). |
| LocalLimits | 28 | No blocking mismatch in the selected chronological T01/T02 version. The full ambient closed-embedding/weak-limit bridge is genuinely proved in the library and independently checked, but is not a selected comparison target. [Audit](locallimits/CODEX_AUDIT.md). |
| SameLaw | 24 | No blocking mismatch in T05 on the faithful canonical observable, including extinction. The dictionary to the literal isomorphism-class reading remains a disclosed representation qualification. [Audit](samelaw/CODEX_AUDIT.md). |
| SIR | 13 | No blocking mismatch in all nine T06/T07 conclusions or the positive-rate data-existence construction. The chronological/age-indexed physical representation and eventual data assumptions remain explicit. [Audit](sir/CODEX_AUDIT.md). |

The target counts include supporting model checks: they are not counts of
manuscript theorems. The source scope is seven theorems/twenty conclusions;
the main-results axiom script queries 26 distinct principal/support names.
The new independent probes pass 16 expanded examples and 24 queried closures
in total. Their logs are beside the four audit records.

The reviewers inspected the pinned Lean environment/private-name/matcher
implementations and Lake's exporter/recursive comparison code. Temporary
`setMainModule` changes metadata and private-name generation, not already
declared kernel constants. Matcher-cache controls do not exempt the resulting
constants from recursive comparison. No demonstrated soundness bypass was
found. SameLaw and SIR use these devices; LocalLimits also uses matcher-cache
controls and explicit auxiliary proofs. Their readability/tooling fragility
and official acceptance remain unverified. No speculative refactoring was
performed solely because these features exist.

## Verification repairs

`scripts/verification.py` is the shared standard-library driver behind the
existing shell entry points. The repairs address confirmed false-success paths:

- Every external command has its real exit status checked; a comparison,
  exporter, compiler, checker or audit failure stops the run. Missing executables
  also fail. No pipeline's `tee` exit can replace a failing checker status.
- Export stdout remains pure NDJSON; stderr has separate logs. Empty exports
  fail. A zero diagnostic exit without both comparison/axiom confirmations fails.
- Old nonempty output directories are refused. Interrupted/incomplete runs have
  no passing completion marker; summaries reject them.
- Comparison and replay record the exact export/configuration hashes, check
  inputs again at the end, and bind the summary to the actual exported files.
  Replacing/removing an export or removing its required metadata fails.
- Collection requires a clean committed checkout and confirms the same clean
  commit/tree after all checks. A mid-run modification or branch move fails.
- The axiom parser handles wrapped lines and axiom-free reports, rejects
  forbidden axioms/duplicates/Lean errors, and checks the exact queried names.
- Summaries validate all required command statuses and child completion markers
  before printing a success table. They do not infer a clean build from a log.

The failure-injection suite is `scripts/test_verification.py`. It exercises real
process boundaries with fake external tools, including each of the six selected
checker failures. It is a script test, never proof evidence for mathematics.
The suite also tests clean-source identity, late export mutation, missing
metadata, stale logs, malformed configuration and non-Linux rejection.

## Current evidence

- The historical full build/comparison/replay evidence in `candidate/SUMMARY.md`
  and the interface logs is unchanged. No mathematical implementation changed,
  so another empty-cache rebuild was unnecessary.
- The 26-name historical axiom output passes the stricter new exact-name parser.
- Fresh source scan and Python/shell/workflow syntax checks pass.
- A real auxiliary comparison was run through the repaired driver, including
  Lean kernel checking: both comparison confirmations and exit zero. Its output
  is under `/private/tmp/freezing1-candidate-codex-auxiliary-20261030`.
- A small genuine `Init` export of `Nat.add_zero` was replayed successfully by
  all six actual bundled checkers, using the strict NanoDa configuration.
  This smoke test validates invocation/positive-status handling; it does not
  claim a fresh replay of the four main interfaces. Its logs are under
  `/private/tmp/freezing1-candidate-codex-kernel-smoke`.
- Local rejection of `run-linux-checks.sh` on macOS exits 2 as intended, with
  a failed result marker; it does not attempt a sandbox bypass.

Compact new evidence is kept in `codex-checks/`; large exported streams stay
outside the repository. Older committed summaries remain historical records,
not outputs retroactively generated by the repaired scripts.

## Prepared Linux checks — not executed

`.github/workflows/comparator.yml` is still manual-dispatch-only and can be
used on a private repository after a separately authorized push/dispatch.
Nothing here requires creating a self-hosted runner. The workflow:

1. Runs the failure-injection suite, installs the pinned Lean environment and
   the pinned Palomar Bubblewrap build, and tests sandbox startup.
2. Verifies `MANIFEST.sha256` for the committed files.
3. Calls `scripts/run-linux-checks.sh "$RUNNER_TEMP/freezing1-linux-checks"`.
   That command requires Linux and a clean checkout; it builds the project,
   scans sources, audits axioms and invokes the official sandboxed
   `lake comparator` on all four main configurations plus the auxiliary one.
4. Explicitly requests NanoDa in copies of the configurations outside the
   checkout. The pinned Lake code defaults `enable_nanoda` to false. Targets,
   mathematical definitions and the permitted axiom set are unchanged.
5. Retains exact-commit diagnostics on both success and failure. No failure is
   marked `continue-on-error`, and the script never dispatches or publishes.

On a Linux machine with the same pinned toolchain/dependencies and a working
Bubblewrap installation, the local command is:

```sh
scripts/run-linux-checks.sh /tmp/freezing1-linux-evidence
```

This is a standalone official Comparator run, not the full Palomar pipeline.
The full mechanical report, public source commit, editorial review and registry
submission remain separate. All whole-manuscript obligations in
`OPEN_OBLIGATIONS.md` remain open; no complete-paper certification is claimed.

Official policy and pipeline heads were refreshed through read-only GitHub
requests: policy `28bd48b9b71bbb2a82c718ce761d5a4220ef8e60`, pipeline
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`. The pinned upload-artifact v4
commit was also verified. No dependency/toolchain pin was upgraded.
