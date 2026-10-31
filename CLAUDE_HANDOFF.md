# Corrected metadata filenames: local candidate awaiting user check

All four full checks of approved source `174e765` stopped at intake, before
Lean, because the metadata basename must be `formalization.yaml`. Raw reports
are in `verification/certification/palomar/path-correction-174e765/`.
The old Heights registry request was not withdrawn and no replacement intake
was created. The full-pass condition in the approved batch was not met.

The corrected local layout is `metadata/<entry>/formalization.yaml`. File
contents, the four approved titles and every mathematical source/pin are
unchanged. The workflow and action preview use the corrected paths. Follow
`PALOMAR_SUBMISSION_PREVIEW.md` and obtain the user's check of this corrected
candidate before further external changes. Keep existing registration and
private-review-publication restrictions in force.

# Four approved entry titles: local candidate awaiting action check

The four user-approved titles now have separate metadata files under `metadata/`.
Their scopes and request paths are in
[PALOMAR_SUBMISSION_PREVIEW.md](PALOMAR_SUBMISSION_PREVIEW.md). The workflow
locally selects the matching file per comparator configuration. All Lean proofs,
statements, comparison targets and pins are unchanged. Existing mathematical
audits remain applicable; new metadata requires fresh exact-source preflight.

The user requires checking exact proposed Palomar actions before external changes.
This milestone prepares locally only. Do not push, dispatch checks, withdraw the
old Heights request, create replacement intakes or register anything until the
user checks and approves the concrete candidate/action packet. An approved batch
can proceed without repeated questions for the same approved steps. Never publish
private reviews before the user's review-dependent registration decision.

# Publication title updated — 31 October 2026

The user requested the exact publication title **Uniform attachment with freezing**.
The metadata and citation titles are updated; all scope qualifications remain.
The first registry request (Heights) is frozen to source `82f0ad4`
and retains its old title. The remaining old-source intakes are held. The
private intake checkpoint outside this checkout records the replacement guard;
never resume the old sequencer against `82f0ad4` without resolving that guard.
This title change does not change any mathematical statement or proof, and does
not give a new source SHA the status of the existing four mechanical reports.

# Four full Palomar mechanical checks passed — 31 October 2026

The reviewed candidate is public at `igor-kortchemski/uniform-attachment-with-freezing`.
The old repository and its manuscript/history remain private under the `-private`
suffix. All four full official mechanical reports pass at source commit
`82f0ad45a60ec785a725fc419082c7d1d779b222`, preserved by tag
`palomar-checked-2026-10-31`. Lean, NanoDa and con-ron accepted every interface.
Ordinary GitHub build/axiom CI also passed. See the
[archived reports](verification/certification/palomar/README.md).

This subsequent commit archives evidence and updates documentation only; the
mathematical source/configuration/pin/script bytes remain unchanged. No registry
intake or registration occurred. Every previously listed mathematical obligation,
representation qualification and proof departure remains in force. Earlier
checkpoints below are historical and their pending-publication statements are
superseded by this section.

# Authorized public-candidate checkpoint — 31 October 2026

The user authorized preserving the existing GitHub repository privately as
`uniform-attachment-with-freezing-private`, creating a fresh public repository
at `igor-kortchemski/uniform-attachment-with-freezing`, pushing the reviewed
candidate, and running the four full Palomar mechanical checks at one commit.
The old manuscript/history must stay in the private repository. Mathematical
sources, statement interfaces, dependency pins and verification scripts are
unchanged from the Linux-checked `54253ce`.

The [publication checkpoint](verification/certification/palomar/README.md)
records the source-snapshot status. Earlier dated checkpoints below are
historical. Whole-paper gaps and representation qualifications remain in force.

# Current publication-content review checkpoint — 31 October 2026

The user authorized step 1 only: final review of the public-release contents.
No push, publication, remote addition or visibility change is authorized or
performed. Read [PUBLICATION_REVIEW.md](PUBLICATION_REVIEW.md) before any
external action. It covers the local candidate/history through `d52e74e` and
the subsequent documentation fixes. No credential-pattern matches or unwanted
binary/build artifacts were detected; known local paths in raw history remain
disclosed. Proof/interface/pin/script bytes remain those checked at `54253ce`.

Fixed the Comparator badge target, stale citation scope, two missing-manuscript
links, the stale A32 recommendation and an unsupported exact Claude model tag.
Added the verified public paper reference while preserving the supplied TeX's
SHA-256 identity and explicitly declining to assert version equality.
No new mathematical result or manuscript argument was certified in this review.

Important destination finding: the existing private GitHub repository's older
tip `ee1aa1228a49b4df2432b696ee65bd188e482353` includes the manuscript TeX.
That material is excluded from the reviewed candidate. Keep that repository
private; decide a public destination for the selected export before publishing.
Its complete remote history and other repository assets are not covered by the
local-candidate review. Do not force-push or flip visibility as a substitute.
The earlier Linux evidence and all whole-manuscript obligations remain valid.

---

# Linux verification checkpoint — 30 October 2026

The user authorized a private local Linux run while continuing to prohibit
push/publication. The exact candidate `54253ce4046e1314cf5af6aedb19a278200d168d`
passed the full Linux build (4,645 jobs), source scan (826 files), namespace
axiom audit (8,683 declarations), exact-name export audit (26 names), and all
five official sandboxed `lake comparator` invocations. NanoDa and Lean accepted
every Solution. The clean source commit/tree was verified unchanged at the end;
all nine locked dependency checkouts were also checked clean afterward.

Read [the Linux summary](verification/certification/linux/SUMMARY.md) and its
raw logs. The script suite executed seventeen passing tests and one expected
non-Linux-host test skip. Eight initial cache-download failures stopped
preparation; their separate retry passed. Both logs are retained.

The run was entirely local in an Ubuntu VM. No GitHub workflow was dispatched,
no remote was added, and nothing was pushed or published. The full Palomar
mechanical report, public candidate commit, intake and registration are still
pending. The existing chronological/observable scope qualifications and every
whole-manuscript obligation remain in force. No proof, mathematical interface,
comparison target, version pin or verifier script changed in this milestone;
only documentation, verification-status metadata, evidence and Git attributes preserving the raw logs were
added after the checked commit.

The VM was stopped after evidence collection. Its reusable workspace is
`../.freezing1-linux/`; its README records setup
and lifecycle commands. Do not include its SSH keys, VM disk or binary downloads
in a publication. Repository evidence contains only the selected text logs.
Earlier sections below are historical checkpoints, superseded by this one.

---

# Initial Codex takeover checkpoint — 30 October 2026

The user authorized takeover of `freezing1-candidate` from local commit
`4b3e78c6b9cd9db80f1b63fd85046e2805589123`, four-interface audit, repairs
to verification failure propagation and Linux preparation. Push/publication
remain expressly prohibited. No remote, workflow dispatch or visibility change.

Read `verification/certification/CODEX_TAKEOVER.md` and `SCRIPT_REVIEW.md`.
All four interfaces passed an independent audit within their disclosed
chronological/canonical-observable scope; no model, Challenge, Solution,
comparison target or version pin was changed. The new independent probes
passed 16 expanded examples/24 closures in total. Main-result proof evidence
from the original rebuilt candidate is preserved; no empty-cache rebuild.

Verification scripts now fail on failed/missing stages, stale exports,
missing metadata and changed source identity. Eighteen regression tests pass,
with separate real auxiliary-comparison and six-checker small-export smoke
checks. These are not official Linux/Palomar results. Compact logs are in
`verification/certification/codex-checks/`. The prepared manual Linux workflow
uses `scripts/run-linux-checks.sh`, explicitly requests NanoDa in copied
configs, verifies the manifest and retains logs even on failure. It has not
been dispatched. Local macOS refusal is an expected exit 2, not a pass.

Local changes were reviewed against the 4b3e78c base. Use `git log -1` and
`git status --short` for the current local checkpoint. Future full collection
requires a clean committed checkout and a new evidence directory outside it.
No old log has been relabelled as a result of the repaired scripts. The rest
of this file is historical Claude context, superseded where noted here.

---

# Certification-interface preparation for T01–T07 (30 October 2026, Claude Code)

Task: prepare a verifiable certification candidate for the seven main results and their twenty conclusions, for GitHub
and Palomar, *without* presenting it as a certification of the whole manuscript. No push, visibility change, upload or
external repository was made; Lean/Mathlib v4.35.0, pins and caches are unchanged.

- Interfaces (self-contained Challenge modules importing only Mathlib; Solution modules `public import Freezing1`):
  `Challenge/{LocalLimits,Heights,SameLaw,Sir}.lean`, configs `comparator/{locallimits,heights,samelaw,sir}.json` (Palomar
  accepts one config per submission, hence four interfaces). The old `comparator.json` (16 auxiliary results) remains.
- Read `verification/certification/README.md` first, then `MAIN_RESULTS_CORRESPONDENCE.md` (20 conclusions ↔ tex ↔ Lean ↔
  Challenge) and `OPEN_OBLIGATIONS.md` (everything not covered). `CHALLENGE_RECIPE.md` explains how a pair is built and
  checked; `*/NOTES.md` and `*/INDEPENDENT_REVIEW.md` hold per-interface details.
- New proofs: `Freezing1/SIRPoissonExistence*.lean` (non-vacuity of `PoissonSIRData`: independent exponential periods and Poisson
  contact paths exist for every positive rate; false at rate 0). Three previously unimported proof modules
  (`BernoulliPairCouplingComplete`, `SIRCaptureCoefficientBirthBridge`, `SIRFirstContactIrrelevance`) are now imported by `Freezing1.lean`.
  Nine verification probes without a `module` header were ported to `verification/candidate-ports/` (originals untouched).
- Scripts: `scripts/export_candidate.py DEST` (isolated candidate), `scripts/local-comparator-diagnostic.sh`
  (local comparison with Lake's own comparison code, outside the sandbox), `scripts/local-kernel-replay.sh` (toolchain checkers
  incl. NanoDa), `scripts/MainResultsAxioms.lean`. Workflows `.github/workflows/{ci,comparator,palomar}.yml` are prepared, unrun.
- Known risks: `Challenge/SameLaw.lean` and `Challenge/Sir.lean` use `setMainModule`/`bootstrap.genMatcherCode` devices (see
  OPEN_OBLIGATIONS section 4); the local diagnostic is not the official Comparator; no Linux, no public commit, no NanoDa run by
  the official pipeline, no Palomar mechanical report.
- Suggested next steps: (1) commit the candidate publicly only when the user decides; (2) run `comparator.yml` on a Linux runner;
  (3) refactor the development so that reachable definitions create no tactic-generated private auxiliaries, removing the
  Challenge devices; (4) the open manuscript obligations of OPEN_OBLIGATIONS section 3.

# Claude resumption log (supersedes stale items below)

After the handover the user asked Claude to continue and then to do everything feasible. Facts now true (30 October 2026, later session):

- `lake build`: PASS 4631 jobs (`verification/build.log`); `scripts/AxiomAudit.lean`: PASS 8618 declarations, standard axioms only (`verification/axioms.log`); metadata scan PASS 648 Lean files.
- PROVED and integrated: A03 chronological conditional uniform plane law and uniform sibling reordering (`FinitePlane*`, `FinitePlaneShuffle*`); A07 embedded Kingman jump chain for the whole reverse history (`KingmanPartition`, `ReverseKingman*`); A06 finite sampled-distance matrices and Gromov--Hausdorff non-tightness (`LinearBush*`; GHP and the dendron identification are NOT formalized); A14/A16 intrinsic union over schedules with a bijection class $\leftrightarrow$ intrinsic increasing states (`ForwardIntrinsicSupport`, `RootedForwardEncoding*`, `ForwardStateDecoding*`); A87 per-vertex conditional domination for the fixed word, corrected with the $+1$ (`ForwardActiveHeightMgf`). Details in `FORMALIZATION_REPORT.md` (rows A03, A06, A07, A14, A16, A87 and the final "Claude resumption milestone").
- Provenance: four of these were authored by delegated workers and only read and re-run by the root; no independent audit of the new modules exists yet. Notes: `verification/A03_*`, `A06_NOTES.md`, `A07_KINGMAN_SELF_REVIEW.md`, `A14_*_NOTES.md`.
- Still open: A85--A86 (actual reversed iid coupling; research-level multivariate domination), literal L13 (current-state-only urn hypothesis; heuristic obstruction recorded), the printed shifted-mean A87 bound and future-conditioned random-mean argument, A24/A67/A73 explicit joint couplings (bypassed), publication steps (Challenge/Comparator interface refresh, Linux/kernel replay, Palomar). U1 draft modules A85 domination not done.
- Workflow notes: artifact builds were serialized with a lock wrapper `bl.sh` (a `mkdir` lock around `lake build`); direct checks never take the lock. Draft check commands keep `import` lists minimal (never `import Mathlib`). A `rw` on `Finset.filter` card lemmas often fails from DecidablePred instance mismatch; state lemmas with indicator sums instead.

# Continuation checkpoint — whole-paper formalization

Checkpoint: 30 October 2026. The user explicitly requested STOP and handover
to Claude. Proof development has stopped; resume only when asked. The intended
continued scope is the WHOLE manuscript, not merely T01–T02 or one helper. Do not upload or publish before
mathematics, inventory reconciliation and final publication verification.
The private remote contains an older partial snapshot.

## Workspace and rules

Work in `/Users/igor/LeanFormalization/freezing1`. Read AGENTS.md and local
lean-workflow, lean-statement-audit, lean-project-architecture and
lean-orchestrator skills. Preserve Lean/Mathlib v4.35.0, pins and caches.
Only root schedules artifact-writing `lake build`, one invocation at a time.
Workers check actual files with `lake env lean -DautoImplicit=false`.
No custom axioms, holes, native_decide or bv_decide. Only propext,
Classical.choice and Quot.sound. Every maintained Lean file <=1000 lines,
with module/public visibility. Markdown math uses dollar delimiters.

Source SHA256 is unchanged:
`88953dd87165a14b0e643c5b3d0075d8ce5ec39cdcfc0c25d313570fc3ab00df`.
2590 lines; 24 named environments, A01–A87, Q01–Q07. The coverage report
is authoritative. Keep false printed statements and substantive departures
explicit. Questions Q01–Q07 are research questions, not unproved theorems.

## Completed integrated evidence

- `verification/build.log`: PASS4596 jobs, all default targets.
- `verification/axioms.log`: PASS7986 Freezing1 declarations; all transitive
  axioms belong to propext, Classical.choice, Quot.sound. Fresh imported
  audit exited zero after the4596-job build.
- This includes full unordered A20 topology, root all-vertex A24 obstruction,
  all-row A36 boundedness, repaired geometric A37–A38, exact source positive
  good-index filter/graph chains, actual conditional covariance, Chebyshev,
  tower/normalized finite growth, bare geometric reconstruction and generic
  probability-law closed embeddings.
- MainConditionalGoodChainForest, MainLocalAmbientDegreeNecessity, repaired
  Poisson/positive urn modules, InterleavedSourceFactorization, source A64
  urn/union route, IidHalfSlope and S24 are now imported and globally checked.
- Source-metadata scan passes624 maintained Lean files, including current
  unimported drafts. It checks text/metadata only; it does not certify drafts.
  Script `/private/tmp/freezing1-source-metadata-check.py`, bundled Python
  `/private/tmp/parking-palomar-python/bin/python`, cached official v0.4 schema.
- Whole inventory source/scope unchanged. Full read-only source reconciliation:
  verification/FULL_INVENTORY_RECONCILIATION_2026_10_30.md (all24/A01–87/Q01–07).
  Reconcile new progress and repeat the final omission check before completion.

All T01–T07 conclusions, P01 and C01 have proofs in their recorded models.
IMPORTANT affected dependency: broad source ambient A20 is now genuine
unordered labelled graph-isomorphism classes. Earlier main local results use
chronological record balls. The faithful closed embedding and weak-law
transport are now proved and independently audited; T01/T02 have full ambient
consumers. This does not replace final publication checks.

## New verified source-argument scope

A20 `UnorderedTreeTopology`: actual quotient of ALL plane locally finite
vertex/edge labelled trees by genuine rooted graph isomorphism, repeated
labels allowed; all coherent towers realized; finite isomorphism reflection
proved both directions; actual complete separable metric, exact positive-ball
sequence criterion. Independent root audit A20_UNORDERED_TOPOLOGY_INDEPENDENT_AUDIT,
probe10examples/10closures PASS. Author12/12 separately.

A24 root modules LocalBallTightness, ForwardDegreeDivergence/Coupling,
MainLocalDegreeNecessity prove all-vertex degree escape and marginal ball-tail
contradiction without the freezing-series theorem, including root/absorption.
Strictly increasing prefix extraction and actual full-history PAIR couplings
are proved. No single common family of all rows is asserted. Final proof uses
marginal tightness, not the printed nonmonotone diagonal union inference.
Sourceworker independent A24_ALL_VERTEX_INDEPENDENT_AUDIT/probe9/12 PASS;
root authored4/8 kept separately. Conclusion still chronological LocalTree.

A27 literal nonnegative subtree expectations, gn normalization and actual
plane/limit/null-leaf specialization proved. Sourceworker independent audit
A27_SUBTREE_INTEGRAL_INDEPENDENT_AUDIT5/13 PASS. Rectangle induction behind
finite-child law replaces printed conditional-expectation proof order.

A32 actual adjacent swaps/sorting/harmonic source argument independent9/10.
A33 actual unmasked independent Bernoulli law + Bennett/moments independent10/10.
A34 actual real layercake/split7/dilation/tail source moment route independent5/8;
log envelope replaces printed integration by parts. A36 one common late rank
for ALL C>=2, actual tail-integral real moments/Lp and all early-row boundedness
independent8/10. All integrated.

A37–A38 seven modules (IntervalFreezingCounts + six GeometricHeight modules)
prove repaired original geometric strategy through exact nested-limit L08.
1<beta<C, actual integer cutoffs, empty blocks allowed, exact U/L, eventual
actual eta_n lower positivity. Last endpoint needs +1/A_n and beta^m denominator.
Three literal false steps formally refuted. Root independent A37_A38_GEOMETRIC_
INDEPENDENT_AUDIT5/10 PASS; author9/18 PASS. No Abel estimate used in new route.

A47 corrected full augmented forest product/exchangeability/uniform actual
matching reconstruction proved; bare forest independent of past. S17 bare
all-star convention loses root clocks, formal [+,-] witness. Bare geometric
fields can reconstruct with correct matching; full clocks cannot. Independent
FULL_FOREST_INDEPENDENT_AUDIT6/7 and conditional mean/variance3/9 PASS.

A48 exact finite positive cutoff max1(ceil logA/logC), terminal historical
predicate, source N/M meanings proved. A49 one actual graph ancestor chain
with parent iterates, historical active vertices, graph distances and height
bound proved. A52 actual complete-bare-forest conditional negative covariance,
including old marked roots, and common same-component mark proved. Root
independent FOREST_SOURCE_GEOMETRY_INDEPENDENT_AUDIT/probe3/8 PASS.

A53 finite actual full-forest CE Chebyshev +observed-event tower integration
+N/M independence +normalized cond completed. True S_a<=a+1 yields mean>=3b
for a>=3 and error3M/b (source false factor4 not asserted). Final
MainConditionalGoodChainForest gives uniform source limsup/liminf window
with eta in(0,1), max1 cutoff, same constants before rows/indices, no old
growth consumer. Focused PASS3959. Root independent final audit/probe2/7 PASS;
author3/7 PASS. Included in the latest whole build.

Root generic ProbabilityMeasureClosedEmbedding frozen/build PASS:
closed state embedding induces closed probability-law embedding; map has
range exactly supported laws; weak-limit existence equivalent in either
space. Support of ambient limit is DERIVED, not added as premise. Normal/Borel/
HasOuterApproxClosed target conditions are supplied by intended Polish space.

Earlier verified scopes remain: A21/A22 conditional attachments/Borel–Cantelli,
A28 raw iid extinction/drift and unique consecutive relabelling, A40–A43
random-mean source argument with S21 correction, actual P01 bijection and full
C01 tangent/Bernoulli count, both SIR physical rate branches A65 and complete
joint original-forward word/count/tree prefix adapter A66. See prior audits
and report for their detailed evidence. Do not redo them without changes.

## Latest verified source arguments and active ownership

The 4570-job default build and 7703-declaration axiom scan include:

- A60/A61: all BernoulliPairCoupling modules through Conclusions. Actual
  complete-history marginal, full independent driver words, before-step
  current-merge formula, independent thinning, exact mismatch expectation,
  actual product of two true marginal tails and uniform L/a bound. Authored
  probe5/24 PASS; independent A60_A61_BERNOULLI_PAIR_INDEPENDENT_AUDIT12/20 PASS.
  S24 current-merge boundary formally refuted; the correct formula survives.
- A63: ForwardComponentUrnPath/Infinite/Positive/Maximal. Actual infinite
  continuation disintegration, every finite joint component record, AE
  original complete past and genuine actual-component infinite maximal
  estimate. Path-law hypotheses are derived. Authored8/13; separate root
  independent A63_JOINT_COMPONENT_PATH_INDEPENDENT_AUDIT3/7 PASS.
- A84: SIRCountsExtinctionIndex supplies total measurable firstzero, with
  cap correctness proved under actual law. SIRReverseHalfWindow proves
  corrected pre-step charge reduction and supplies early/log n negligible
  uniformly over all endpoints from genuine triangle fluid control.
  Authored4/7; independent SIR_REVERSE_HALF_WINDOW_INDEPENDENT_AUDIT5/10 PASS.
  Printed shifted identity remains false on the actual (+,-,-) word.
- IidHalfSlope: all-time iid half-slope probability tends1 and literal
  unconditional harmonic expectation; independent4+reindex helper/8 PASS.
  No actual reverse coupling is inferred.
- A85: SIRReverseCouplingWord/WindowGap/Formulation/SourceGap/Necessary
  define the exact measurable actual-history/unconditional-iid coupling
  target and prove a necessary marginal bound and positive-probability
  forward-hazard inheritance gap at actual n6,tau9. Existence is OPEN.
  Authored ordinary imported progress probe5/10 PASS. Weak unconditional
  coupling may correlate with gate/epidemic; counterexamples to stronger
  conditional reverse hazards do not refute it. Numerical discovery
  checks are not proof. See SIR_REVERSE_COUPLING_PROGRESS.md.

## Latest completed mathematical milestone

A04 is COMPLETE under an explicit existence coupling. The seven new
ConditionalSurvivalCoupling*/IidLinear* modules construct exact rows with
laws iidSignLaw p conditioned on {tau>n}, a common true survivor with law
conditioned on {tau=infinity}, and AE eventual equality of WHOLE rows.
Positive survivor mass comes from the actual iid extinction formula.
UniformTailRatio iff the literal full finite maximum→0, and both literal
nested near/bulk assumptions follow for any positive diverging sublog cutoff.
Do not claim independent rows or arbitrary-coupling AS convergence.
Export ForwardAnnealed.exists_conditioned_iid_linear_coupling.
Author8 examples/15 closures PASS; root independent4/11 PASS.
Audits A04_CONDITIONED_IID_SELF_REVIEW.md and
A04_CONDITIONED_IID_INDEPENDENT_AUDIT.md. All in the4596-job build.

A77 is COMPLETE for every0<eps<t0 with the SAME eps cutoff/error coefficient.
All ten SIRCaptureCoefficient*.lean modules frozen, artifact checked and
included in the4596-job build. Scalar strict slack2(1−1/lambda)<t0 and
actual unconditional survival/cardinality/deadline estimates give eventual
expected reverse-missing fraction<eps, with no assumed capture estimate.
Exact feasible-word firstzero/recovered counts identify the source reverse
birth law. CanonicalReverseBirthClock transports it to actual Forward
terminal uniform vertices and their frozenAt−1 clock (active horizon true
extinction); chronological birth is a DIFFERENT clock. Their order is proved.
Native treeFullLaw actual prefix-membership capture is proved. BOTH pair
interfaces draw two independent uniform vertices given the SAME actual tree
before mixing, include diagonal pairs, and prove equal true marginals.
Literal rate-ratio wrappers include source_same_epsilon_two_reverse_births
and source_same_epsilon_two_uniform_captures. Author ordinary imported8/31
PASS, root independent7/15 PASS, separate pair semantic review. See
SIR_CAPTURE_COEFFICIENT_PROOF_NOTES.md,
SIR_CAPTURE_COEFFICIENT_INDEPENDENT_AUDIT.md and
SIR_CAPTURE_PAIR_INDEPENDENT_AUDIT.md. Clock dependency was authored by root
and independently reviewed by the capture author; preserve this provenance.

A87 scalar/corrected-tail scope COMPLETE: RateFunctionAsymptotics proves
exact g(u)/(u logu)→1 and IsEquivalent; BennettSmallMean proves g(u)/u→infinity,
r*g(eps/r)→infinity and n exp(−m_n*g(eps logn/m_n))→0 for EVERY eventually
positive deterministic mean m_n=o(logn). SIRLateBennett proves genuine actual
fixed-word cut-maximum Bennett tail with EXPLICIT threshold1+D+a and factor
2n+2. Zero late charge gives zero tail above1, without dividing byzero.
Independent SIR_LATE_BENNETT_INDEPENDENT_AUDIT6 examples/8 closures PASS.
The original per-vertex conditional Bernoulli domination, literal shifted
mean/unshifted-threshold bound and future-conditioned random-mean argument
are NOT certified. The earlier forward maximum conclusion remains proved.
All three root modules included in4596-job build.

A03 recursive example COMPLETE with n+1 correction: RecursiveTreeLaw.lean
constructs an independently specified fresh uniform-parent law on{0,...,n};
actual all-positive Forward.treeLaw equals its ENTIRE State law. Actual active
and vertex sets equal range(n+1), and newest_parent_law is exactly uniform.
Direct PASS0, zero diagnostics, and artifact in4596-job default build.
Parameter independently read source/definitions/bodies and found no mismatch;
verification/RecursiveTreeIndependentStatements.lean has a drafted5-example/
6-closure independent probe including a derived product recursion. At STOP
it has NOT been run against imported artifacts. Do not call this probe PASS.
No finite-conditioned plane uniformity follows from this specialization.

## Stopped proof tasks and draft ownership

All workers confirmed STOP. No new proof work or artifact build is running.
Their final checkpoint notes below take precedence over older task messages:
[A03 finite planes](verification/A03_FINITE_PLANE_HANDOVER.md),
[A85 one-susceptible coupling](verification/A85_ONE_SUSCEPTIBLE_HANDOVER.md),
[A77/recursive/Kingman](verification/SIR_PARAMETER_CLAUDE_HANDOVER.md).
Do not automatically message/restart workers or create new chats.

sir_source_audit: remaining A03 finite-conditioned uniform plane law.
FinitePlaneConditionalGeometry.lean FROZEN/direct PASS0 and focused artifact
PASS3956 (verification/finite-plane-conditional-geometry-build.log). It gives
true finite vertex cardinality, child finiteness, disjoint graft vertex sets,
cardinality addition and first-child/rest identity. It is not yet imported
by the entry point. FinitePlaneConditionalBounds.lean is an UNBUILT draft whose direct check
FAILED with two errors (line24: infer T; line43: unfold local C); session9845
finished exit1. See verification/a03-finite-plane-bounds-active-failure.log
and [A03_FINITE_PLANE_HANDOVER.md](verification/A03_FINITE_PLANE_HANDOVER.md).
It is not imported by the verified entry point. No mass/conditional-law
module has yet been created.
Plan: intrinsic ALL finite Ulam plane trees of size m form a finite carrier
by bounded addresses/offspring; geometric atom mass q^m p^(m−1) then implies
conditional uniformity. Still prove actual JOINT firstzero tau=2m−1 iff
chainLimit has m vertices, then transport conditioning. The source's uniform
child-order kernel must be justified separately; chronological order cannot
simply be called uniform child order. No Catalan enumeration is needed merely
to prove uniformity. No conditional finite-plane theorem yet.

sir_fluid_analytic: A85 actual reversed iid coupling remains OPEN in general.
New SIROneSusceptibleLaw.lean and SIROneSusceptibleLastNegative.lean are
FROZEN/direct PASS0, artifact PASS4114 and included in4596 default build.
Law derives ACTUAL arbitrary-start U1 stopped history from firstTimeLaw,
for every rate and initial infectious m including0; firstTime probabilities
are conclusions. LastNegative derives exact index masses from genuine iid
coordinate independence. New SIROneSusceptibleFirstTime.lean,
SIROneSusceptibleTimeCoupling.lean and
SIROneSusceptibleCouplingMarginals.lean are later draft/direct-check work;
consult [A85_ONE_SUSCEPTIBLE_HANDOVER.md](verification/A85_ONE_SUSCEPTIBLE_HANDOVER.md)
for exact status before importing them. Some newest direct/concatenated checks
have empty logs but uncollected exits: they are NOT certified as PASS.
U1 viable route: p=r/(1+r), q=1−p, first infectionT masses p*q^(T−1),
no infectionq^m; unique reverse-birth positionJ=m+3−T. Eligible J<=m has
q^2 times genuine iid last-negative mass. Thin iid last-negative byq^2,
fill leftover probability at T0/1/2 (outside window), then transport to
actual histories. General susceptible-count induction and actual late gate
remain substantial. Forward hazard bounds alone do not prove reverse iid
coupling; conditional reverse hazards can fail without refuting the weak
unconditional joint coupling. Numerical discovery checks are NOT proofs.

sir_parameter: A77 done and independent restricted A87/Clock reviews done.
Recursive independent source review done; imported probe pending as above.
A07 actual Kingman partition specialization was assigned just before STOP,
but no implementation was started. Inspect [SIR_PARAMETER_CLAUDE_HANDOVER.md](verification/SIR_PARAMETER_CLAUDE_HANDOVER.md)
for API search findings only. Intended exact target: actual all-positive reverse
forest projected to partitions of its original n+1 labels, genuine uniform
unordered-block-pair merge kernel, then entire embedded jump-chain law.
Do not define Kingman as the actual process or assert holding-time identity.

## Immediate Claude resumption commands

First read AGENTS.md, local lean-workflow/statement-audit/orchestrator skills,
FORMALIZATION_REPORT.md, the full inventory reconciliation and stopped worker
notes. Preserve all local files: much of the development is UNCOMMITTED or
UNTRACKED, and the private remote is older. Do not reset, clean or discard it.
All root build, imported-audit and metadata checks finished; no build is left
running. Worker A03 direct failure also finished. Some older U1 scratch
checks have uncollected exit evidence and must be treated as unverified.

Existing evidence commands, always from this project directory:

```sh
lake build
lake env lean scripts/AxiomAudit.lean
lake env lean -DautoImplicit=false verification/RecursiveTreeIndependentStatements.lean
```

Only run the third after the new recursive artifact exists (it does in the
latest4596 build); fix its probe if necessary without weakening the theorem.
Reuse all unchanged successful scoped evidence instead of repeating every
old probe. Scanner command:

```sh
/private/tmp/parking-palomar-python/bin/python /private/tmp/freezing1-source-metadata-check.py
```

This cached local script/schema are available at checkpoint; its text scan
includes unimported drafts and does NOT prove their compilation or coverage.

## Remaining scope and publication

Retain every genuine remaining obligation: A03 finite-survival-conditioned
uniform plane example and uniform ordering; A06 actual GHP non-tightness/
long-dendron sampling convergence; A07 actual embedded Kingman partition;
possible A14/A16 intrinsic all-schedules support bridge; literal weaker L13
current-state conditioning; A85/A86 actual reverse iid coupling/localization;
original A87 conditional domination and future-conditioned random-mean route.
Explicit joint coupling claims A24/A67/A73 remain distinct from proved
marginal consequences and bypassed proof tools. Main theorems do not erase
these obligations. A04/A77 and A87 scalar/corrected fixed-word scope are now
closed as detailed above; old "active" labels are stale. Source unchanged,
all24/A01–87/Q01–07 reconciled. Repeat final full omission reconciliation
before claiming whole-paper completion.

Apache-2.0; Igor Kortchemski contributor/maintainer; private remote
igor-kortchemski/uniform-attachment-with-freezing is an older snapshot.
No uploads. Current Challenge/Comparator interface covers older supporting
scope. Final source interface, fixed candidate revision, Linux Comparator,
independent kernel replay and complete official Palomar mechanical report
remain outstanding. Palomar requires a public exact commit. This is a checked
partial development, not a verified complete publication candidate.
