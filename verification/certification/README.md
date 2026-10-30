# Certification interface for the main results T01–T07

**Scope.** This directory documents the Challenge/Solution interfaces and the local evidence for the seven
main theorems T01–T07 of `attachement-uniforme-1-final.tex` (twenty conclusions, see
`MAIN_RESULTS_CORRESPONDENCE.md`). It is **not** a certification of every assertion of the manuscript: the
inventory of what is not covered is `OPEN_OBLIGATIONS.md`.

## Interfaces (one Comparator configuration each)

Palomar accepts a single comparator configuration per submission, so the main results are split explicitly
into four interfaces, with no result omitted:

| Interface | Config | Challenge module | Main results |
| --- | --- | --- | --- |
| Local limits | `comparator/locallimits.json` | `Challenge/LocalLimits.lean` | T01 `thm:cvlocale`, T02 `thm:BGW` |
| Heights | `comparator/heights.json` | `Challenge/Heights.lean` | T03 `thm:height`, T04 `thm:lineaire` |
| Same law | `comparator/samelaw.json` | `Challenge/SameLaw.lean` | T05 `thm:samelaw` |
| SIR | `comparator/sir.json` | `Challenge/Sir.lean` | T06 `thm:SIRlocallimit`, T07 `thm:SIR` |

Each Challenge is a single self-contained module importing Mathlib and Lean core only: it reproduces verbatim every
definition (and every theorem reachable through a definition body) of the development that the statements
use, and states the main results with `sorry` bodies (the only `sorry`s in the Challenge are the targets,
plus two pinning theorems proved inside `Challenge/Heights.lean`). The matching `Solution/X.lean` imports
`Freezing1`, whose theorems have the same names and types. The Comparator checks that every reachable
constant is structurally identical and that the targets have the same statements. Extra targets in each config
are pinning statements (that the model objects are what their names say, that probability measures are
genuine) and non-vacuity witnesses; they are not manuscript statements. The old `comparator.json`
(16 auxiliary results, `Challenge.lean`/`Solution.lean`) remains as a separate auxiliary configuration; it
does not state any main result.

Build the interface modules with `lake build Challenge Solution`. Direct check of one Challenge:
`lake env lean -DautoImplicit=false Challenge/Heights.lean` (only `declaration uses sorry` warnings on the
targets). The recipe followed is `CHALLENGE_RECIPE.md`.

## Reproduction commands (in the candidate checkout)

```bash
lake build Freezing1 Challenge Solution
lake env lean scripts/AxiomAudit.lean              # whole Freezing1 namespace, standard axioms only
lake env lean scripts/MainResultsAxioms.lean       # the 26 exported names (20 conclusions, 5 pins, 1 non-vacuity theorem)
scripts/local-comparator-diagnostic.sh comparator/heights.json OUT/heights
scripts/local-kernel-replay.sh comparator/heights.json OUT/heights/solution.ndjson OUT/heights/kernels
```

and likewise for `locallimits`, `samelaw` and `sir`. On Linux with the Palomar bubblewrap build the official
command is `lake comparator --config comparator/heights.json`. The prepared
workflow now calls `scripts/run-linux-checks.sh` and explicitly enables NanoDa
in copies of all five configurations; the toolchain default is off.

## Codex takeover from `4b3e78c`

**Current Linux evidence:** the official sandboxed Comparator, NanoDa and Lean
accepted all four main interfaces plus the auxiliary configuration at clean
commit `54253ce`. The 4,645-job build and both axiom audits passed. See
[linux/SUMMARY.md](linux/SUMMARY.md) and its raw logs. This was a private local
Linux VM run; no GitHub workflow or full Palomar pipeline was executed.

The four interfaces have a new independent audit in each interface directory
(`CODEX_AUDIT.md`). The selected statements pass within the disclosed chronological
and canonical-observable representations. This does not certify the unrestricted
ambient bridge as a compared target, the whole manuscript or Palomar acceptance.
See [the takeover review and Linux runbook](CODEX_TAKEOVER.md).

The verification scripts now stop with a nonzero status on any failed required
step. Each run needs a **new or empty output directory**. Collection requires a
clean committed checkout, checks its identity again at the end, and writes
`result.json`; summaries reject incomplete runs and changed export files.
Use output directories outside the checkout, for example:

```sh
scripts/collect-evidence.sh /tmp/freezing1-local-evidence
python3 scripts/summarize-evidence.py /tmp/freezing1-local-evidence > /tmp/freezing1-local-summary.md
```

Commit local changes before collecting evidence; the collector deliberately
rejects a dirty checkout. Standalone diagnostics remain available while editing.
The historical summary below and its logs are preserved, not retroactively
presented as output of the repaired scripts.

## Results for the stabilized candidate (local runs, details in `candidate/SUMMARY.md`)

Local commit `ab3d936089e44a44ec3e13cc5f354b29b6ed92c1` (tree `b0cf2f15ca3e2ad7b06693dc20f1ca842067fd30`, no remote), built from an
empty `.lake/build` against the pinned Mathlib v4.35.0 packages: 4645 jobs, success, no hole outside the Challenge targets;
8683 `Freezing1` declarations and the 26 exported names have only the three standard axioms; for each of the four interfaces
the local comparison reports `statements and reachable constants match` and `only permitted axioms`, and the Solution export is
accepted by Lean's `leanchecker`, NanoDa (`nanoda_bin`) and the four other bundled checkers (exit 0). The logs are
`<interface>/{compare,run,leanchecker,kernels}.log`. The Claude evidence commits `7546bcf` and `4b3e78c` add only scripts, documentation and these logs
(no Lean file changes, checked with `git diff --stat`); no rebuild was needed.

## Evidence levels — kept distinct

1. **Verified in Lean (build + axioms).** `lake build` of `Freezing1`, `Challenge`, `Solution` and the
   `#print axioms` closure of each of the 26 exported names (20 conclusions, 5 pinning theorems, 1 non-vacuity theorem)
   (`scripts/MainResultsAxioms.lean`): only `propext`, `Classical.choice`, `Quot.sound`.
2. **Local comparison and replay (not official).** `scripts/local-comparator-diagnostic.sh` exports the
   Challenge and Solution with the toolchain's `leanexport`, applies Lake's own `compareAt` and `checkAxioms`
   (`Lake/Check/Compare.lean`) from a compiled executable, and replays the Solution export with
   `leanchecker`. `scripts/local-kernel-replay.sh` additionally runs NanoDa (`nanoda_bin`) and the other
   bundled checkers with Lake's invocation protocol. All of this runs outside the Linux sandbox.
   Negative controls: `negative-controls/README.md`.
3. **Official standalone Linux comparison and kernel replay.** Passed for all
   five configurations at `54253ce`, with Bubblewrap isolation and NanoDa
   explicitly enabled. See [linux/SUMMARY.md](linux/SUMMARY.md).
4. **Palomar mechanical conformity.** Not obtained: no `mechanical-report.json`
   or public candidate commit. The GitHub workflows remain prepared and unrun;
   the standalone official Comparator does not replace the full pipeline.
5. **Whole-manuscript coverage.** Not claimed; see `OPEN_OBLIGATIONS.md`.

Independent statement reviews of each Challenge (written without reading the proofs):
`heights/INDEPENDENT_REVIEW.md`, `locallimits/INDEPENDENT_REVIEW.md`, `samelaw/INDEPENDENT_REVIEW.md`,
`sir/INDEPENDENT_REVIEW.md`. These are automated reviews; no human review is claimed.

## Candidate and manifest

`scripts/export_candidate.py DEST` copies an explicit allowlist from the development tree into an isolated
directory (the development tree is untouched). `MANIFEST.sha256` in the candidate lists the hash of every
file. The candidate is a local git repository with local commits only (no remote or push).
