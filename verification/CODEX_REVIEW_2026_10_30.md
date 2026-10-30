# Review of Claude's resumed formalization — 30 October 2026

## Verdict

The checked Lean development builds, and the newly reviewed mathematical
results have meaningful, faithful statements within their stated scope.
**The whole manuscript is not fully formalized, and this tree is not a
verified publication candidate.** Claude's final report itself retains
unresolved obligations. A successful build does not close them.

No mathematical implementation was changed during this review. Changes are
limited to verification probes, review records and corrections to coverage
wording. Reviews are automated independent reviews, not human peer review.

## Fresh mechanical evidence

| Check | Result |
| --- | --- |
| Default `lake build` | PASS, 4,631 jobs; `codex-review-build.log`. |
| Proof modules outside the entry import closure | All three also build: `BernoulliPairCouplingComplete`, `SIRCaptureCoefficientBirthBridge`, `SIRFirstContactIrrelevance`; `codex-review-extra-modules-build.log`. The default target alone did not check these. |
| Existing namespace axiom audit | PASS, 8,618 declarations; `codex-review-axioms.log`. |
| Namespace audit importing every proof module | PASS, 8,639 declarations; `AllProofModulesAxiomReview.lean`, `codex-review-all-modules-axioms.log`. Every transitive axiom is `propext`, `Classical.choice` or `Quot.sound`. |
| Maintained-source/metadata scan | PASS, 648 maintained Lean files; `codex-review-source-metadata.log`. This excludes verification probes and does not certify whole-paper coverage. |
| Manuscript identity/inventory | Unchanged SHA-256 `88953dd87165a14b0e643c5b3d0075d8ce5ec39cdcfc0c25d313570fc3ab00df`, 2,590 lines. All A01–A87 and Q01–Q07 occur once; the previously checked 24-result inventory applies. |
| Pinned environment | Lean/Mathlib remain v4.35.0. No caches or version pins were changed. |
| Fresh Comparator attempt | Exit 2 on macOS: the Linux namespace sandbox is unavailable; `codex-review-comparator.log`. No isolation bypass was attempted. |

The broader axiom total includes the previously omitted leaf modules; it
does not contradict the default import-closure total. Neither audit is an
independent kernel replay.

## Independently reviewed additions

The reviewers reconstructed the corresponding paper claims, inspected the
definitions and relevant proof bodies, then compiled new exact-type probes
against the current artifacts.

| Scope | Verdict and evidence |
| --- | --- |
| A03 extinction-conditioned finite plane trees and uniform sibling reordering | No blocking finding. The carrier contains all finite plane shapes of the prescribed true size. Atom masses, actual first-zero/size joint event, positive odd-time conditioning, even-time nullity and true independent sibling reordering are checked. Six statements/nine axiom closures. [Review](CODEX_REVIEW_A03_2026_10_30.md), `codex-a03-independent-statements.log`. |
| A07 embedded Kingman history; A14/A16 intrinsic support bridge | No blocking finding. Genuine uniform block-pair kernel and complete actual-history projection, with $n+1$ labels; no holding times claimed. The source-class/state bijection and union over schedules are checked; the false fixed-schedule assertion stays separate. Eight statements/nine closures. [Review](CODEX_REVIEW_KINGMAN_SUPPORT_2026_10_30.md), `codex-kingman-support-statements.log`. |
| A06 finite distance samples and GH non-tightness; A87 generating functions | The actual finite-sampling, GH-space and moment statements pass. Their stronger source conclusions remain incomplete, as below. Three statements/seven closures. [Review](CODEX_REVIEW_BUSH_MGF_2026_10_30.md), `codex-bush-mgf-statements.log`. |

Unchanged earlier mathematical reviews remain separately attributed; this
review does not claim an independent rereading of every legacy proof body.

## Blocking whole-paper gaps

1. **A85–A86: the actual reversed SIR iid coupling and localization are
   still open.** Source line 2295 asserts an actual coupling. In
   `SIRReverseCouplingFormulation.lean:84`, `SourceReverseIidCoupling` is
   only a proposition defining its desired existence. The theorem in
   `SIRReverseCouplingNecessary.lean:26` assumes that proposition. The
   one-susceptible modules supply partial marginals, without the general
   domination and actual-history wrapper. The forward alternative proves
   the main conclusion but does not certify this source construction.
2. **Literal L13 is neither proved nor formally refuted.** The source at
   lines 2003–2006 conditions only on the current occupancy.
   `SignedUrnInfinite.lean:49–57` assumes full finite path laws, a stronger
   condition. Those path laws are proved for the intended actual component
   applications; the broader literal arbitrary-process assertion remains
   a separate obligation.
3. **A06 does not yet identify the GHP and long-dendron statements.** Genuine
   GH non-tightness and every finite sampled-distance matrix are proved.
   The measured GHP carrier/forgetful-map bridge and the identification
   with the named long dendron and sampling topology are absent. Matrix
   formulas named after a dendron do not provide that identification.
4. **A87's new moment bound is not a stochastic-order theorem.**
   `ForwardActiveHeightMgf.lean:319–325` bounds generating functions for
   $c\geq1$, with an explicit extra edge and corrected indices. It exports
   neither a tail-order/coupling statement nor the source conditional law
   given the future SIR extinction/count history. The bold claim that
   per-vertex stochastic domination is proved overstated the formal
   conclusion; coverage wording was corrected. The stronger source bridge
   and random-mean argument remain open, without refuting their targets.

The explicit all-row/path coupling claims retained under A24/A67/A73 also
remain separate from their proved marginal conclusions. These are not
erased by the completion of the Introduction's main results.

## Publication blockers

- `comparator.json:4–20` selects only 16 older auxiliary results, with no
  comparison interface for the main advertised theorems. The existing
  Challenge/Solution pair therefore does not yet verify that advertised
  publication scope.
- No successful current Comparator/NanoDa replay or full Palomar mechanical
  report exists. The fresh local attempt still fails on the platform before
  any comparison. A local build and axiom scan cannot substitute for these.
- `git rev-parse --verify HEAD` fails: this working repository has no local
  commit identifying the candidate. Much of the development is untracked
  or staged. The older private remote is not evidence for these local files.
- **Nine verification `.lean` files lack `module`.** The 648-file maintained
  scan excludes them. They include `verification/A14IntrinsicStatements.lean`
  and `verification/A14ConverseStatements.lean`. The current full tree would
  fail the repository-wide module-header requirement if deposited as is.
  Port and recheck them, or prepare a clearly scoped publication export
  retaining the verification evidence elsewhere; do not discard local work.

For the last finding the official policy was checked through the GitHub
connector at commit `28bd48b9b71bbb2a82c718ce761d5a4220ef8e60`:
[source-layout requirements](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md#21-lean-and-lake-files).
The rule covers unused and verification Lean source files in the submitted
repository, not just the default import closure. No file exceeds the local
1,000-line bound. No upload, release, visibility change or submission was made.

The accurate status is a substantially advanced, checked **partial
formalization** with independently reviewed additions, not finished
whole-paper formalization or final GitHub/Palomar verification.
