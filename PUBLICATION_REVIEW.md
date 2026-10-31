# Public-release content review — 31 October 2026

The local candidate's contents and reachable history were reviewed for public
release. No credentials or unwanted binary/build artifacts were detected.
Documentation corrections are recorded below. **Nothing was pushed, published,
submitted, or made public.** The existing private GitHub repository contains
additional material, so its visibility must not simply be changed on the basis
of this candidate review.

## Exact scope

The audit input was local commit `d52e74e770da9c06b88c7b1f0361cbe5f23ce88c`:
1,787 tracked files, 8,006,265 bytes, five reachable commits, and 1,590 unique
reachable blobs (9,285,661 bytes across history). The final documentation
changes were also checked before committing; the regenerated manifest lists
the resulting release contents.

This is a publication-content review by Codex, not a new independent
mathematical review. The prior four independent automated statement audits
are reused because the mathematical sources, elaborated interfaces, defining
dependencies, toolchain pins and verification scripts are unchanged from
the Linux-checked `54253ce4046e1314cf5af6aedb19a278200d168d`.

The mathematical claim remains the seven Introduction theorems/twenty
conclusions through the four selected interfaces, with their documented
chronological-carrier, canonical-observable and SIR-model qualifications.
The full ambient local-limit bridge is proved but not selected; the literal
isomorphism-class dictionary is reviewed rather than an extra Lean theorem.
All source-wide obligations and proof departures remain in
[FORMALIZATION_REPORT.md](FORMALIZATION_REPORT.md) and
[OPEN_OBLIGATIONS.md](verification/certification/OPEN_OBLIGATIONS.md).

## Contents, history and provenance

- Every reachable blob and commit record in the five-commit candidate history
  was scanned for private-key blocks, GitHub/OpenAI/cloud/service-token patterns,
  authenticated URLs and bearer credentials: no matches. The current tree
  contains no submodules, symlinks, Git LFS pointers, compiled outputs, archives,
  dependency caches, VM files or manuscript TeX. All tracked content is text.
- Historical source/evidence retains local filesystem paths: 429 occurrences
  across 39 distinct paths in the reviewed history, using only the known user components
  `igor` and `igor.guest`. These paths are provenance, not credentials; they
  will be visible with the published history. Raw logs were not redacted or
  rewritten to alter the verification record.
- Existing local commits use a synthetic `Local candidate (Claude Code)`
  identity and noreply addresses. This inherited label is not a human-review
  or model-identity attestation. Actual Codex/Claude work and the credited
  maintainer are described by the reports, `NOTICE` and `formalization.yaml`.
  Existing history was preserved.
- Original code/documentation retain the user-selected Apache-2.0 license and
  Igor Kortchemski credit. Copied workflow skills retain their CC BY 4.0
  attribution and bundled MIT/Apache notices. The source-paper authors are
  credited separately; no manuscript relicensing or human endorsement is claimed.
- The manuscript is omitted from the candidate and its history. Its exact
  supplied-source SHA-256 remains
  `88953dd87165a14b0e643c5b3d0075d8ce5ec39cdcfc0c25d313570fc3ab00df`.
  The [public paper reference](https://arxiv.org/abs/2308.00493) was verified by
  title and authors. Equality of that public version with the supplied TeX
  has not been established and is not asserted.

## Corrections made during review

- The Comparator badge now targets `comparator.yml`; it no longer displays the
  build-only CI status as comparison evidence. Both workflows remain unrun for
  this candidate; the successful standalone Linux evidence is linked separately.
- `CITATION.cff` now describes the main-result interfaces and remaining scope
  limits instead of calling the main results unresolved supporting work.
  The public paper reference was added to the citation, README and metadata,
  without changing the formalized source identity or mathematical scope.
- The two broken links to the intentionally omitted TeX were replaced with
  source-identity/report references. All local Markdown links were checked.
- The stale adjacent-swap recommendation was reconciled with the already proved
  A32 route in the coverage report. No new manuscript argument was certified.
- An unsupported exact Claude model tag was removed; Claude Code assistance
  remains credited, with the unknown model identifier disclosed.
- Metadata and citation files were checked against the official v0.4 and
  CFF 1.2.0 schemas. Source scanning, manifest checks and the comparison of
  proof/interface/pin/script bytes with the Linux-checked snapshot passed.

The Challenge bounds remain: Heights 400 lines/18,365 bytes; LocalLimits
846/36,772; SameLaw 680/31,331; SIR 992/56,018. The largest Lean source is 992
lines. All nine dependencies use full commit pins and credential-free public
GitHub HTTPS URLs. The three workflows use pinned actions, read-only repository
permissions, and no publication/intake/registration action. Comparator and
Palomar remain manual; the latter retains its public-repository guard.

Policy and pipeline heads were refreshed read-only and remain
`28bd48b9b71bbb2a82c718ce761d5a4220ef8e60` and
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`. The current toolchain-policy blob
is `9022506963e460170c7f90c3547e85e0891753c0`; the Challenge-root allowlist blob
is `2efc59dfdbb4331b624a71cd43fda07bdf72ca63` (Mathlib release tags and their
pinned manifest closures are admitted). No Lean/Mathlib pin was changed.
These checks do not replace Palomar's full mechanical report.

## Repository inspection at the review checkpoint

Read-only GitHub inspection confirmed that
`igor-kortchemski/uniform-attachment-with-freezing` exists and is private.
Its current tip is `ee1aa1228a49b4df2432b696ee65bd188e482353`, an earlier
supporting-result snapshot. It includes `attachement-uniforme-1-final.tex`
(Git blob `e0efc785f39d1d5f4b7b4b62694ebdaf2268bda5`), which is not included
in this reviewed candidate. Its complete remote history, other branches,
issues and run artifacts are not certified by this local-candidate review.

Keep that existing repository private. The simplest publication route is a
fresh public repository containing only this reviewed candidate and its local
history, with the destination name and README URLs settled before upload.
Reusing the existing repository instead requires a deliberate review/decision
about its additional assets and history; a visibility switch or force-push
must not be treated as equivalent to publishing the selected export.
No remote has been added to the candidate.

The user subsequently authorized preserving the old repository privately as
`uniform-attachment-with-freezing-private`, then creating a fresh public repository
at `igor-kortchemski/uniform-attachment-with-freezing`, pushing this reviewed
candidate and running the four full Palomar mechanical checks. This authorization
does not expose the old history. See the
[publication checkpoint](verification/certification/palomar/README.md).

At the content-review checkpoint, full Palomar mechanical preflight, intake,
editorial outcome and registration were unperformed. A85–A86, literal L13,
A06's GHP/dendron identifications, A87's stronger source claims and
A24/A67/A73's explicit couplings remain open; the false printed L03/L04/P03
versions retain their recorded corrections. Whole-paper certification is not claimed.
