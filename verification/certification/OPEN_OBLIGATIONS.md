# Open obligations and limits of the main-result certification interface

This file is the complete inventory of what the T01–T07 certification interface (`Challenge/*`,
`Solution/*`, `comparator/*.json`) does **not** establish. The interface concerns the seven main
theorems T01–T07 and their 20 conclusions only. It is not a certification of the manuscript
`attachement-uniforme-1-final.tex` (SHA-256 `88953dd87165a14b0e643c5b3d0075d8ce5ec39cdcfc0c25d313570fc3ab00df`,
2590 lines, unchanged). The per-assertion status of A01–A87, Q01–Q07 and the 24 named environments
stays in `FORMALIZATION_REPORT.md`. All of these items were already open before this task and none was
closed by it, except where stated.

## 1. Proof routes that differ from the manuscript's argument

A proof of a main result by another route does **not** validate the manuscript's own argument. The
Challenge/Solution comparison certifies the *statement* proved; for these results the manuscript's printed
argument is not what Lean checks:

| Result | Manuscript argument | What Lean proves it with |
| --- | --- | --- |
| T03 (thm:height) | reverse growth-coalescent representation | direct forward MGF/Jensen/Hölder argument; the reverse representation is proved separately (T05) |
| T04 (thm:lineaire) | L09–L13 (conditional forest arguments, Pólya urn maximal inequality L13) | forward cut-forest counts, finite MGF, true forward continuation; L13 is bypassed, see 3 |
| T06/T07 (SIR) | embedded chain, Skorokhod representation, reversed-increment iid coupling (A85–A86) | exact adaptive finite-word mixtures, frozen-ball transfer, forward harmonic charge budgets; Skorokhod and the reversed coupling are bypassed |
| T01 | Borel–Cantelli on a printed post-step reciprocal series | true pre-step hazards with a proved comparison to the printed series; the printed nonmonotone union-event inference is replaced by marginal finite-ball tails |

## 2. Manuscript assertions that are false as printed

Corrected versions are proved; the printed text is not. None of them enters T01–T07 as stated in the
Challenge interface.

* L03 (coalescence-time law) false for coinciding vertices (S02); distinct-vertex version proved.
* L04 (forward-tree probability on the displayed class) false on the printed support (S01); corrected
  support version proved.
* P03 upper half false at n = 1 (S16); corrected bound with the true vertex count proved.
* Introduction sentence at tex line 312 swaps the roles of +1 and −1 with respect to Algorithm 2.

## 3. Open obligations of the manuscript

1. **A85–A86 (SIR reversed iid coupling and localization).** The source construction (tex 2287–2321)
   needs a multivariate stochastic domination of reversed infection indicators; no proof is available.
   `SIRReverseCouplingFormulation.SourceReverseIidCoupling` is only a proposition stating the target.
   The convergence needed by T07 (II)(b) is proved by the forward alternative; the source argument is not
   certified.
2. **L13 literal.** `SignedUrnInfinite` assumes full finite path laws (a stronger hypothesis than the
   source's current-occupancy conditioning); those path laws are proved for the intended component
   applications. The literal arbitrary-process assertion is open.
3. **A06.** GH non-tightness and finite sampled distance matrices are proved. GHP non-tightness, the
   identification with Janson's long dendron and the characterization of the distance-sampling topology
   are not Lean statements.
4. **A87.** Only an inequality of exponential moments (`ForwardActiveHeightMgf`) and the corrected
   fixed-word Bennett estimate are proved. *A bound on exponential moments is not a stochastic-domination
   theorem*, and the source's conditional law given the future SIR extinction/count history is not
   formalized.
5. **A24/A67/A73 joint couplings.** The marginal conclusions that T01/T06 use are proved; the explicit
   all-row/path coupling claims are separate and open.

## 4. Scope limits of the interface itself

* **Carrier of T01/T02.** The Challenge states T01 and T02 on the *chronological* local space
  (`LocalTree.Tree`: vertices identified by birth times), which is the closed subspace of the paper's local
  space containing every `T_n(x)`. The statements in the unrestricted unordered ambient space
  (`Freezing1.source_local_convergence_*`, `MainLocalAmbient`, `source_diagonalLocalConvergence_iff`) are
  proved in the project but their statement closure (about 1800 lines) exceeds the Palomar Challenge limit, so
  they are not part of any Challenge. Independent review found the chronological reading equivalent to the
  paper's topology on the relevant objects (weak limits transfer by the portmanteau theorem for the closed
  subspace) but the argument itself is not in the Challenge.
* **Topology.** T01 is about the double-labelled (vertex- and edge-labelled) local topology; plane or
  unlabelled variants of (I) are not asserted. T02 concerns the plane tree obtained with children ordered by
  birth time.
* **Annealed history.** T02 is stated for `ForwardAnnealed.fullLaw`, the marginal law of the tree history with
  the signs integrated out (equivalent for the conclusions stated).
* **Absorbing convention.** Rows of T01 are extended by holding after extinction (as in the manuscript's
  Algorithm 1); there is no hypothesis `τ(x^n) > n` in T01.
* **T06/T07: physical model.** The statements concern the full-contact physical SIR model driven by
  `PoissonSIRData` (independent exponential recoveries and pairwise contact processes with Poisson counting
  marginals). Non-vacuity of this hypothesis is proved (item 5 of section 5).
* **T06/T07: limit laws.** Annealed convergence in distribution on `ProbabilityMeasure`; the population path
  space is the non-separable space of all real functions with the topology of uniform convergence on compacts
  and its Borel σ-algebra (the limits are step/continuous functions).
* **T05 observable.** Equality of laws is stated on the canonical observable (vertex ids, graph, active ids,
  frozen times), which was reviewed to be in bijection with labelled-tree isomorphism classes; the bridge to
  isomorphism classes is argued in the review, not proved in Lean.
* **Proof-term devices in Challenges.** `Challenge/SameLaw.lean` and `Challenge/Sir.lean` use
  `run_cmd Lean.modifyEnv (·.setMainModule …)` and `set_option bootstrap.genMatcherCode false in` (and
  hand-written matcher/auxiliary-proof declarations in `Challenge/Sir.lean`) so that the names of private
  auxiliary declarations created by `omega`/`simp`/`deriving` agree with those of the multi-module development.
  They change no statement and no kernel term of a reachable constant (checked by the local and pinned official Linux comparisons), but
  they are metaprogramming inside an interface file and full mechanical acceptance is now confirmed by the four reports; editorial
  and registration outcomes remain unconfirmed. The alternative
  is a development refactor so that reachable definitions avoid these internals.
  `Challenge/LocalLimits.lean` also uses `bootstrap.genMatcherCode false` and explicit auxiliary
  proofs. The Codex audit inspected the pinned environment, matcher, exporter and recursive-comparison
  implementations: these devices do not exempt constants from comparison; the subsequent full official mechanical runs accepted the interfaces.
  No editorial or registration acceptance is inferred.

## 5. Verification status and remaining limits

1. **Full Palomar mechanical reports: obtained and passed.** All four main
   configurations passed at public commit `82f0ad45a60ec785a725fc419082c7d1d779b222`,
   with Lean, NanoDa and con-ron acceptance. Source/configuration/target/pipeline
   identities were inspected; see [palomar/README.md](palomar/README.md). The
   earlier standalone Linux evidence, including the auxiliary configuration,
   remains separately identified in [linux/SUMMARY.md](linux/SUMMARY.md).
2. The reviewed candidate is public, with the exact checked snapshot tagged
   `palomar-checked-2026-10-31`. The old manuscript/history repository remains
   private. Registry intake, editorial outcome and registration remain pending.
3. The local diagnostic (`scripts/local-comparator-diagnostic.sh`) reproduces Lake's own comparison functions
   outside the sandbox on `leanexport` output. It is not the official tool.
4. Reviews are automated independent reviews; no human mathematical review is claimed.
5. SIR non-vacuity (formerly open): proved in Lean by `Freezing1.SIR.PoissonSIRData.exists_data` and
   `exists_family` (`Freezing1/SIRPoissonExistence*.lean`, notes `sir/EXISTENCE_NOTES.md`), and exported as a target of
   `comparator/sir.json`. The counts history `(U, I)` of the fluid statements is not pinned by a target (only the tree
   history is); the reading (susceptibles, active tree vertices) rests on the definitions.
