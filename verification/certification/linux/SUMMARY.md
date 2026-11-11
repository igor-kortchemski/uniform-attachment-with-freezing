# Linux verification of the main-results candidate

**Passed:** the official sandboxed Lake Comparator, with NanoDa explicitly
enabled, on all four main interfaces and the auxiliary configuration.
This is a standalone Linux verification, **not** a Palomar mechanical report,
GitHub Actions run, editorial acceptance, or whole-manuscript certification.

## Checked snapshot and environment

- Candidate commit: `54253ce4046e1314cf5af6aedb19a278200d168d`.
- Git tree: `5d5484126052e8eb177cff20f15ba6e665671cb2`.
- Lean `v4.35.0`, compiler commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake `5.0.0-src+eb6cafb`.
- Mathlib and all eight other dependencies retained the exact revisions in
  `lake-manifest.json`; their restored worktrees were checked clean before the build
  and again after verification. See [dependencies-final.log](dependencies-final.log).
- Ubuntu 24.04.5 LTS, x86-64, Linux `6.8.0-142-generic`, in a private local
  Lima `v2.2.1` VM with three CPUs and twelve GiB RAM.
- Bubblewrap `0.12.0`, built using the hash-verified installer from
  PalomarSubmission `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`.
  Namespace sandbox startup passed; isolation was enabled throughout.
- Run: `2026-10-30T19:11:23Z` to `2026-10-30T19:50:18Z` (38 minutes 55 seconds).
- All 1,754 files in the checked commit's manifest passed before verification.
  The driver confirmed the same clean HEAD/tree again at the end. See
  [identity.json](evidence/identity.json), [result.json](evidence/result.json),
  and [manifest log](setup/manifest.log).

The project was built in a fresh Linux checkout, using the public Mathlib
dependency cache. No macOS compiled artifact was copied. This is not a claim
that Mathlib or the toolchain was rebuilt from source without caches.

## Results

| Required check | Result |
| --- | --- |
| `lake build Freezing1 Challenge Solution` | Pass, 4,645 jobs, 1,315.705 seconds |
| Maintained source scan | Pass, 826 Lean files |
| Whole `Freezing1` namespace axiom audit | Pass, 8,683 declarations |
| Exact-name main/support axiom audit | Pass, 26 exports; zero forbidden axioms or duplicate names |

All audited transitive axioms belong to `propext`, `Classical.choice`,
`Quot.sound`. Deliberate Challenge holes are distinct from the proved Solution.

| Official Comparator interface | Selected targets | NanoDa | Lean kernel | Final verdict | Seconds |
| --- | ---: | --- | --- | --- | ---: |
| [Heights](evidence/heights.comparator.log) | 10 | Accept | Accept | Pass | 251.617 |
| [LocalLimits](evidence/locallimits.comparator.log) | 28 | Accept | Accept | Pass | 193.675 |
| [SameLaw](evidence/samelaw.comparator.log) | 24 | Accept | Accept | Pass | 73.216 |
| [SIR](evidence/sir.comparator.log) | 13 | Accept | Accept | Pass | 302.681 |
| [Auxiliary](evidence/auxiliary.comparator.log) | 16 | Accept | Accept | Pass | 176.739 |

These target counts include model pins and supporting declarations; they are
not counts of manuscript theorems. The main source scope remains T01–T07,
twenty conclusions, with the qualifications below.

Every command's real exit status is recorded in [evidence.log](evidence/evidence.log).
Each Comparator log includes both kernel acceptances and `Your solution is okay!`.
Logs are preserved byte-for-byte, including terminal carriage returns and
tool-emitted trailing spaces, except that local home, checkout and temporary
paths and the local user name were later replaced by the placeholders
`<home>`, `<repo>`, `<tmp>` and `<user>`. Git attributes disable newline conversion and
source-formatting whitespace checks for these raw `.log` files only.
The [executed configurations](evidence/configs) match the source configurations
except for explicitly setting `enable_nanoda` to `true`. Module names, targets,
definitions and permitted axioms were not changed.

The script regression suite ran on Linux: seventeen tests passed and the one
macOS-only host-rejection test was skipped. See
[regression-tests.log](setup/regression-tests.log). These tests use mock checkers
and are not mathematical evidence. The fresh Linux kernel checks above use
the real bundled Lean and NanoDa binaries. The other four historical macOS
checker results are not relabelled as Linux runs.

Preparation initially stopped with exit 1 after eight cache downloads failed;
9,023 files had been retrieved. A separate retry passed, retrieving the eight
missing files and completing all 9,031. Both the [failed first attempt](setup/cache.log)
and [successful retry](setup/cache-retry.log) are retained. No failed stage was
ignored or reported as passing.

## Reproduction and scope

On Linux, check out the exact commit above, install its pinned toolchain and
the pinned Bubblewrap as described in
[comparator.yml](../../../.github/workflows/comparator.yml), then run:

```sh
lake exe cache get
sha256sum --check MANIFEST.sha256
scripts/run-linux-checks.sh /tmp/freezing1-linux-evidence-new
```

The output directory must be new or empty and outside the checkout. Set
`COMPARATOR_BWRAP` to the installed binary if it is not named `bwrap` on PATH.
The script builds, audits, and compares all five configurations with NanoDa.

The independent statement audits remain applicable: no proof implementation,
Challenge/Solution statement, semantic definition, comparison target, version
pin or verifier script changed after the checked snapshot. Later documentation
and evidence commits do not retroactively change the identity of this run.

LocalLimits compares the chronological carrier; its full ambient bridge is
proved in the library but is not selected. SameLaw compares the canonical
observable; its dictionary to literal isomorphism classes remains a reviewed
representation qualification. The pinned official Comparator accepted the
existing Challenge matcher/private-name devices; this does not establish
Palomar editorial or full-pipeline acceptance. Reviews are automated, not human
peer review.

The full Palomar `mechanical-report.json`, a public candidate commit, workflow
execution, intake and registration remain unobtained. No push, publication,
remote addition or visibility change occurred. Whole-paper obligations remain
open: A85–A86, literal L13, A06's GHP/dendron identifications, A87's stochastic
ordering/future-conditioned argument, and A24/A67/A73's explicit couplings.
The false printed L03/L04/P03-upper versions retain their recorded corrections.
See [OPEN_OBLIGATIONS.md](../OPEN_OBLIGATIONS.md) for the full qualifications.

After collecting evidence, the metadata's verification wording was updated and
validated against the refreshed official schema dispatcher (Git blob
`3c82c7f4580685888ce1719bfc394530c98ebb49`) and its v0.4 schema (Git blob
`19f4a46a1bc0e4798dca7bcb7ed57281b1c8c996`); see
[metadata-validation.log](metadata-validation.log). The policy and pipeline heads
remained `28bd48b9b71bbb2a82c718ce761d5a4220ef8e60` and
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`. Schema validation is not full
Palomar mechanical conformity. Proofs, interfaces, source configurations and
toolchain pins were preserved.
