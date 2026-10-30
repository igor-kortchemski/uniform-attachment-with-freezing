> **Superseded (30 October 2026, resumption):** the finite-conditioned uniform plane law and the uniform sibling reordering are proved; see `FORMALIZATION_REPORT.md` (A03) and `A03_FINITE_CONDITIONED_PLANE_SELF_REVIEW.md`. The text below is the stopped checkpoint.

# A03 finite-conditioned plane-tree checkpoint

Work stopped at the user's request for a Claude handover on 2026-10-30. This is an authored checkpoint, not an independent statement audit. No new proof or build was started after the stop instruction. The master coverage report remains root-owned.

## Exact outstanding source claim

Source `attachement-uniforme-1-final.tex`, lines 271–274, second Examples bullet: symmetric independent signs, conditioned on the first active-zero time $\tau=n$, give a uniform plane tree after uniformly choosing sibling orders. This requires the actual joint extinction-time/tree law and a justified uniform ordering operation. The marginal geometric tree law alone does not establish it.

Only odd $n=2m-1$ have positive extinction probability, and the terminal tree then has $m$ actual vertices, including the original root. Conditioning on an impossible even extinction time needs explicit treatment. The first Examples bullet is handled independently by root's `RecursiveTreeLaw.lean`; do not edit that file.

## Files and current verification

- `Freezing1/FinitePlaneConditionalGeometry.lean` is frozen. Actual direct Lean check passed with no diagnostics: `/tmp/finite-plane-conditional-geometry3.log`. Root artifact build passed; durable evidence is `verification/finite-plane-conditional-geometry-build.log`, and its current `.olean` exists. It proves actual finite vertex counts, leaf/child bounds, graft vertex-set decomposition and additivity, and first-child/remainder splitting.
- `Freezing1/FinitePlaneConditionalBounds.lean` is active and **does not compile yet**. Its first direct check exited 1, session 9845 has finished. Failure log is preserved at `verification/a03-finite-plane-bounds-active-failure.log` (original `/tmp/finite-plane-conditional-bounds1.log`). No artifact build was requested for this file. There are exactly two errors: line 24, `present_cons _ _ _` cannot infer `T` in the inserted-root subset proof; line 43, `rw [C, ...]` treats a local `Finset` value as a rewrite lemma instead of unfolding the let. One unused-simp warning at line 98. No fixes were attempted after the stop instruction.
- No finite-shape mass or conditioned-law module has been created. No A03 closure, final authored probe, or independent A03 audit is claimed.

The active Bounds file already contains the proposed exact finite carrier: `FinitePlaneClass m := {T // FiniteVertices T ∧ finiteVertexCount T = m}`. It codes all such trees by offspring values on `boundedAddresses m m`, with a `Fintype.ofInjective` construction, and a star-tree witness for every positive $m$. Its declarations after the two errors were elaborated in this failed check, but the whole file must pass before use. Intended exports include child-count strictness, address-length/entry bounds, coordinate injectivity, and nonemptiness.

## Proposed remaining proof route

1. Repair the two local Bounds elaboration errors, direct-check the actual whole file, freeze it and ask root for the sole artifact build. Do not change toolchain pins or frozen geometry.
2. Derive the actual finite-shape atom formula from `ForwardAnnealed.planeLimitLaw_fixedPoint` in `MainGeometricLimit.lean` and `ForwardAnnealed.planeLimitLaw_leaf` in `ForwardPlaneLeafMass.lean`. For a finite tree with $m$ vertices the target is $(1-p)^m p^{m-1}$. Prove graft-pair injectivity using child-one and drop-first identities, then induct on the actual finite vertex count. Restrict to $0<p<1$ when positivity is required. No assumed atom-mass premise.
3. Use the exact finite carrier to show conditioning the actual limit law on $m$ vertices is the uniform law on **all** finite plane trees with $m$ vertices. No Catalan count is needed; a star witness gives positive mass.
4. Prove the missing actual joint process bridge: first active-zero time $2m-1$ corresponds to terminal/limit vertex count $m$. The natural deterministic invariant before absorption is $2|V|-|A|-1=$ elapsed effective steps. Use actual legal steps, holding after absorption and finite-limit/absorption equivalence; do not add a history-law hypothesis to the final source consumer.
5. Transfer to the source's raw iid-sign conditioning using genuine finite iid-sign mixtures of the original fixed-schedule forward process. Relevant modules: `ForwardAnnealedHistory`, `ForwardPlaneHistory`, `ForwardAnnealedSigns`, `IidScheduleExtinction`, `PlaneChainLimit`, `PlaneFiniteExtinction`. In particular, `fullLaw_finite_chainLimit_iff_absorbed` supplies only finiteness versus some absorption, not the missing exact time/size equality.
6. Justify independently uniform sibling ordering. The chronological plane model and a uniformly reordered source tree must have the same conditional law by a proved operation, not by terminology. Possible route: prove that every fixed sibling permutation is a bijection of the finite size class, then implement the independent degree-dependent local permutations on a finite bounded-address universe and prove uniform-law invariance. A uniform unordered-orbit kernel cannot simply be called the original ordering procedure without its law proof.

These are retained obligations. In particular, neither the finite carrier nor a future marginal atom calculation alone closes A03.

## Adjacent completed work to preserve

A04 finite-conditioned iid rows is complete in seven `ConditionalSurvivalCoupling*` / `IidLinear*` modules. The source-facing theorem is `ForwardAnnealed.exists_conditioned_iid_linear_coupling`: an existence coupling of exact conditional row laws, with eventual whole-row equality to one surviving iid path, and hence source uniform slope assumptions. It does not assert almost-sure uniform slopes for arbitrary independent conditional rows. Authored imported evidence: `verification/a04-conditioned-iid-author-statements.log`, 8 expanded examples / 15 closures. Root independent evidence: `verification/a04-conditioned-iid-independent-statements.log`, 4 examples / 11 closures; audit `A04_CONDITIONED_IID_INDEPENDENT_AUDIT.md`.

Final A77 pair semantics was independently read in `verification/SIR_CAPTURE_PAIR_INDEPENDENT_AUDIT.md`. Source, ObservedPairs and OneSus artifacts passed 4114; authored imported probe passed 8 examples / 31 closures, and root independent final interface probe passed 7 / 15. Both uniform samples are conditionally independent on the same actual terminal tree; unconditional survival mixture is retained.

Parent owns the latest whole-project build and axiom evidence. Do not infer a current global pass or publication readiness from these focused records.
