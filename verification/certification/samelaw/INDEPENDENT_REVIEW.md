# Independent statement review: `Challenge/SameLaw.lean` (T05, Theorem `thm:samelaw`)

Reviewer: independent (did not write the Challenge, Solution or NOTES). Date: 30 October 2026.
Source: `attachement-uniforme-1-final.tex`, SHA-256 `88953dd8...ab00df` (verified with `shasum -a 256`).
Reviewed: `Challenge/SameLaw.lean` (675 lines, mtime 15:04; build artifact `Challenge/SameLaw.olean` 15:05, so the
olean matches the file), `comparator/samelaw.json` (23 targets), `verification/certification/samelaw/NOTES.md`.
Not reviewed: proofs, `Solution/SameLaw.lean`, `Freezing1/*` (out of scope), earlier project audits (deliberately unread).
Scope: statement fidelity only. Not a Palomar or Comparator verdict.

## 1. Verdict

* Main target `CanonicalTree.construction_laws_eq` (line 671): **faithful**, with one documented caveat (section 4: the
  statement compares laws of canonical encodings, not literally isomorphism classes of labelled trees). Covers
  every `0 <= n <= tau`, including `n = tau` finite. No hidden premise. No junk fallback is used under the hypothesis.
* Extra targets (22): all are true statements about the right objects as far as I can tell by reading. They pin the forward
  law well and the reverse law only partly (section 5).
* Workarounds: `setMainModule` hack is a real reviewer risk (remove it). `bootstrap.genMatcherCode` is low risk (section 7).
* No blocker found for the statements. Findings F1 to F8 below are Medium or lower.

## 2. What the theorem says (reconstructed from the tex alone, before reading Lean)

* Input: deterministic `X in {-1,+1}^N`; `S_0 = 1`, `S_n = 1 + sum X_i`, `tau = inf{n>=1 : S_n = 0}` (tex 291-300).
* `T_n` (Algorithm 1, tex 424-436): start with one active root labelled `a`. Step `n`: if no `a`-vertex, stay; else pick a
  uniform active `V_n` (independent of the past); `X_n=-1` replaces its label by `n`; `X_n=+1` adds a child labelled `a`
  with edge labelled `n`. The result is a rooted tree, with edge labels (attachment times) and vertex labels (freezing time
  or `a`). Edge labels are pairwise distinct.
* `T^n` (Algorithm 2, tex 523-540), `0 <= n <= tau`: `F^n_n` = `S_n` one-vertex trees `a_1..a_{S_n}`. For `i = n,...,1`
  (reading `X_n` first): `X_i=-1` adds a one-vertex tree labelled `i`; `X_i=+1` picks a uniform ordered pair `(T_1,T_2)` of
  distinct trees, joins the roots by an edge labelled `i`, rooted at `r(T_1)`. `T^n` is the unique tree of `F^n_0`.
  `hat T^n` relabels the `S_n` active vertices `a`.
* Theorem (tex 655-664): `T_n` and `hat T^n` have the same distribution on rooted double-labelled trees (non-plane,
  up to labelled-tree isomorphism). The proof (tex 685-720) shows both give each tree of `T^+_{S_n,N_n}` the mass
  `prod 1/S_{i-1}`. Intro line 312 swaps `+1`/`-1` (known manuscript error, recorded in
  `MANUSCRIPT_RECOMMENDATIONS.md:21`; there the line is cited as 311, it is 312). Lean follows Algorithm 2 proper.

## 3. Definitions read (following definitions, not names)

* `activeCount` (58-59) is `S_n` in `Z` (`x (i+1)` = sign `X_{i+1}`; index 0 unused anywhere). `extinctionTime` (62-64) is
  `Nat.find` of `S_k = 0` or `top`; `k=0` cannot satisfy it since `S_0 = 1`, so it equals the tex `tau`.
  `(n : N-infty) <= tau` is therefore exactly `0 <= n <= tau`.
* Forward: `State`/`initial`/`attach`/`freeze`/`step` (75-112), `transitionLaw` (146-149), `treeLaw` (152-154). Vertex `t`
  is created at step `t` with parent edge labelled `t`; freezing at step `t` stores `some t`. Uniform choice by
  `Measure.uniformOfFinset active`. Empty active set: `dirac`, which is the tex rule "T_n = T_{n-1}". Matches Algorithm 1.
* Reverse: `Reverse.initial` (447-448): `S_n` roots `inl 0..inl (S_n-1)`. `ReverseStamped.transitionLaw x i` (495-496)
  reads `x (i+1)`; `lawAfter x n (k+1)` applies it with `i = n-(k+1)` (504-508), so `x n` is read first and `x 1` last.
  `+1`: `joinLaw` (489-492) maps `uniformRootPair` = `uniformOfFinset roots.offDiag` (423-424, uniform ordered pair of
  distinct roots) through `joinChoice` (470-475): `join a b` makes `b = p.2` a child of `a = p.1` (rooted at `a`) and stores
  the label `i+1` at `p.2`. `-1`: `insertLabel F i` (484-486) adds `inr i`, displayed `i+1` (`reverseLabel`, 586-588).
  Matches Algorithm 2 (roles, order, labels, rooting).
* Observable (542-546): vertex-id set, graph on `N`, active ids, pairs (id, freezing time). `forward` (579-583): ids are
  birth times. `reverse` (591-595): id of `v` is `edgeTime v` (label of its parent edge, `0` for the root); active labels
  `inl _` are erased (`reverseLabel = none`), frozen `inr j` shows `j+1`. `edgeTime` (552, `max`) is used by no
  definition; it only appears in the target `forward_edge_time`.
* `Measurable` structure: `State`, `ReverseStamped.Forest`, `Observable` carry `MeasurableSpace := top` (143, 463, 549),
  so equality of the two `Measure Observable` is equality on all subsets (strongest reading; both are finitely supported).
  `Measure.map`/`bind` are measurable because the domains are discrete or countable, so no silent `0` measure
  (also pinned by the two probability targets).

## 4. Is `forwardLaw x n = reverseLaw x n` the theorem? (main question)

Yes, under the following reading, which is the only reading possible (trees have no ambient vertex set):

* Encoding map `E`: (rooted double-labelled tree with pairwise distinct edge labels) to Observable, by `id(root) = 0`,
  `id(v) = label of the edge to its parent`. `E` is a function of the isomorphism class, so equal tree laws imply equal
  observable laws. Conversely `E` is injective on the supports: from `(V, G, active, frozen)` one recovers the root `0`,
  each edge label as the id of the endpoint farther from `0`, and the vertex labels (`a` or the freezing time). So the
  Lean equality implies equality of the laws on isomorphism classes. No information is lost and none is added
  (the ids are not extra data; they are the edge labels). The graph being a `SimpleGraph N` rather than a graph on `V` does
  not matter: forward edges lie in `vertices` (target `treeLaw_valid.adj_mem`), reverse edges come from `transportGraph`.
* Both sides use the same vertex labels: forward `(v, t)` for `frozenAt v = some t`; reverse `(edgeTime v, j+1)` for `inr j`.
  The tex requires `a_1..a_{S_n}` to be erased only; frozen labels are kept. Correct.
* Boundary cases: `n = 0` (checked in Lean: for every `x`, `forward initial = reverse (ReverseStamped.initial x 0)`,
  scratch `Probe2.lean`, no `sorry`); `n = tau` finite (empty initial forest, last read sign is `-1`); `tau = infinity`.
* Independent exact check (outside Lean): `scratchpad/samelaw_enum.py` enumerates both tex algorithms with exact
  rationals for all schedules of length <= 6 (N=6: 47 pairs `(x, n)` with `n <= tau`, incl. `n = tau`; N=5 repeated with more
  assertions). For each pair it asserts: observable laws equal; laws on canonical iso classes of double-labelled trees equal;
  observable <-> iso class is a bijection across both supports; reverse ids are injective, root id `0`, edge label = max
  endpoint id with `id(parent) < id(child)`; vertex-id set `{0} u attachment times`; forward counts `S_n`, `plusCount+1`;
  at each `+1` step at least 2 roots (no junk branch). All passed. Caveat: this encodes my reading of the tex and of the Lean
  definitions, it does not execute the Lean terms.
* Non-vacuity (scratch `Probe1.lean`, compiled against the olean, no `sorry`): `extinctionTime (fun _ => true) = top` so the
  hypothesis holds for every `n`; for `x = (+,-,-,-,...)` (`x i = decide (i = 1)`) `extinctionTime x = 3`, so `n = 3 = tau`
  satisfies it and `n = 4` does not. Both laws are nontrivial (several atoms, e.g. `x=(+,+)`, `n=2`: path and star, mass 1/2 each).

## 5. Do the extra targets pin the meaning? What is missing?

Group verdicts (all read, none found false or misleading in statement):

| Group | Targets | Verdict |
| --- | --- | --- |
| Probability | `forwardLaw_probability`, `reverseLaw_probability`, `uniformRootPair_isProbabilityMeasure` | good: excludes the zero measure from `Measure.map` |
| Forward law | `transitionLaw_apply`, `treeLaw_valid`, `treeLaw_isTree`, `treeLaw_counts` | good, exact one-step law and support |
| Reverse deterministic ops | `join_roots`, `join_graph`, `adjoin_roots`, `adjoin_graph`, `joinChoice_edgeTime` | good: fixes which root becomes the child, where the label is stored |
| Reverse support | `treeLaw_canonical_ids`, `treeLaw_forest_isTree`, `reverseLaw_vertices`, `treeLaw_reverse_graph_isomorphic` | good |
| Observable | `forward_frozen_iff`, `reverse_frozen_iff`, `reverse_adj_iff`, `transportGraph_adj_iff`, `forward_edge_time`, `forwardLaw_vertices` | good |
| Main | `construction_laws_eq` | faithful |

Missing or weak (none blocks; ordered by usefulness):

* **F3 (Low). No target pins `extinctionTime`** (62-64). Only reading and my probe confirm it is the first zero. If it were
  too small the theorem would be silently weaker. Suggest `(n : N-infty) <= extinctionTime x <-> forall k < n, activeCount x k <> 0`
  (and optionally `extinctionTime x = top <-> forall k, activeCount x k <> 0`).
* **F4 (Low). No reverse analogue of `Forward.transitionLaw_apply`.** The uniform ordered pair is correct by inspection
  (`uniformOfFinset offDiag`) but is not a target; neither is the reading order of `lawAfter` (502-508), except indirectly
  through the main theorem (a wrong order would falsify it, so this is a transparency gap, not a soundness gap).
  Suggest `joinLaw_apply` (for `2 <= roots.card`, mass of `A` = card of pairs landing in `A` over `r*(r-1)`).
* **F5 (Low). No reverse analogue of `forward_edge_time`.** The header (33) and `edgeTime` (551) state that every edge label is
  the larger endpoint id, for both trees, but only the forward case is a target. True (my enumeration), and not needed for
  injectivity (decode by "farther endpoint"), but the justification of "edge labels need not be stored" is then only half
  pinned. Suggest a.s. `forall v in vertices, edgeTime v <> 0 -> edgeTime (parent v) < edgeTime v`.
* **F6 (Low). No reverse count target** (`active` ids count `= S_n`, as in `treeLaw_counts`). Follows from the main theorem
  plus the forward target, so only documentation.
* **F7 (Low, documentation). The encoding bridge is not a Lean statement** (section 4). It is argued in the docstring (29-40) but a
  skeptical reader cannot check it in Lean. Add the caveat text below to `formalization.yaml` / README. An optional
  target would be injectivity of `forward`/`reverse` on their supports; not required.
* Optional (Low): a concrete small anchor (e.g. `x = (+,-,-)`, `n = 3`: two atoms of mass 1/2) would pin edge-label
  conventions and reading order by example. Costly measure computation; only if cheap for the Solution authors.

## 6. Junk fallbacks and ill-defined cases (never reached for `n <= tau`)

| Line | Fallback | Why unreachable under `n <= tau` |
| --- | --- | --- |
| 111-112 `step` | inactive `v` leaves state | `v` is drawn from `active` |
| 146-149 `transitionLaw` | empty active set: `dirac s` | `S_{k-1} >= 1` for `k <= n <= tau`; for `n > tau` it is the tex rule, not junk |
| 447-448 `Reverse.initial` | `toNat` truncates `S_n < 0` | `S_n >= 0` for `n <= tau` (`S_tau = 0` gives the empty forest, a genuine case) |
| 470-475 `joinChoice` | invalid pair leaves forest | pair drawn from `roots.offDiag` |
| 489-492 `joinLaw` | `< 2` roots: `dirac F` | `#roots(F^n_i) = S_i >= 2` at each `+1` step (`S_{i-1} = S_i - 1 >= 1`) |
| 484-486 `insertLabel` | label already present | `inr i` inserted once, at step `i` |
| 506-508 `lawAfter` | `k >= n` branch | only `k < n` is used by `treeLaw = lawAfter x n n` |

My enumeration asserts the `>= 2 roots` property in every `+1` step of the 47 cases. For `n > tau` the Challenge makes no claim
(and the tex does not define `T^n`), so the `toNat` truncation is harmless; its docstring (446) does not say so (F9, Info).

## 7. Opinion on the two workaround devices

* **`run_cmd modifyEnv (.setMainModule ...)` (191-192, 408): Medium risk of rejection; remove it (it is being removed).**
  The Challenge is the trusted specification. `modifyEnv` runs arbitrary code on the environment and Comparator replays only
  the Solution, so an auditor must read it to be sure nothing else changes; here it is two lines and commented, but a policy
  or a reviewer that forbids metaprogramming in the Challenge, or just wants a "small, readable" statement file, would reject
  or at least query it. It also hard-codes two module names (restoring `Challenge.SameLaw` is only right if the pipeline
  builds under exactly that name) and depends on private-name mangling of `omega`, an implementation detail. Semantically
  it only renames auxiliary private lemmas; no statement changes. The project-side fix (proofs without `omega`-private
  lemmas) is the right resolution; afterwards `Challenge/Sir.lean` has the same lines (59-61, 135, 179, 235, 248) and
  needs the same treatment.
* **`set_option bootstrap.genMatcherCode false in` (502): Low risk.** It only suppresses code generation for the auxiliary
  matcher of a `noncomputable` definition (no code is generated anyway), and the comment explains why. It cannot change
  the meaning of `lawAfter`. It is an internal Lean option and cosmetically odd, so prefer a matcher-free recursion
  (`Nat.rec`/shared combinator) in the development if cheap. If kept, mention it in the metadata. After the first device
  is gone it is the only remaining non-statement construct; a reviewer is unlikely to reject over it.
* Both devices are visible, commented and statement-neutral (the local diagnostic reports statement and constants match).
  Neither is a soundness risk for the conclusion; the exposure is process or readability.

## 8. Findings list

| ID | Severity | Where | Finding |
| --- | --- | --- | --- |
| F1 | Medium | 191-192, 408 | `setMainModule` environment hack in the trusted Challenge: remove (project fix in progress); hard-coded module names |
| F2 | Low | 498-502 | `bootstrap.genMatcherCode false`: benign, internal option; document or remove |
| F3 | Low | 62-64 | `extinctionTime` is not pinned by any target; add `n <= tau <-> forall k<n, S_k <> 0` |
| F4 | Low | 489-496, 504-508 | no exact one-step law (and no reading-order anchor) for the reverse process |
| F5 | Low | 33, 551-552, 618-622 | "edge label = larger endpoint id" pinned for forward only; `CanonicalTree.edgeTime` is used by no definition |
| F6 | Low | 625-630 | no reverse analogue of `treeLaw_counts` |
| F7 | Low | 29-40 | encoding bridge (canonical ids vs isomorphism classes) is argued in prose only |
| F8 | Info | `MANUSCRIPT_RECOMMENDATIONS.md:21` | cites the swapped-sign sentence as line 311; it is line 312 |
| F9 | Info | 446-448, 458-460, 552 | docstring gaps and name overloads: `Reverse.initial` truncates negative `S_n` (undocumented); `edgeTime` is both a field of `ReverseStamped.Forest` and a function `max` in `CanonicalTree`; `initial`, `Forest`, `transitionLaw`, `treeLaw` are each defined in 2 or 3 namespaces |

## 9. Caveats to document (suggested wording for `formalization.yaml` / README)

1. "The theorem is formalized as equality of the laws of two canonical encodings in a common finite-support type
   `Observable` (vertex ids = labels of parent edges, root `0`; graph; active ids; pairs (id, freezing time)). The encoding
   is injective on the supports of both constructions and forgets only the distinction between the reverse active labels
   `a_1..a_{S_n}`; edge labels are recovered as the id of the endpoint farther from the root (equal to the larger endpoint id)."
2. "The statement is for fixed `x` and every `0 <= n <= tau(x)` (`tau` possibly infinite), as in Algorithm 2; nothing is
   claimed for `n > tau`."
3. "Algorithm 2 is formalized as in its precise definition (tex 523-540): `+1` merges, `-1` adds a tree. The introduction
   (tex 312) states the opposite and is a manuscript typo."
4. "The Challenge reproduces the definitions of the development verbatim; proof-bearing structure fields (`RootedForest`)
   are part of the compared closure." plus the status of the two devices.
5. "The 22 extra targets are consistency checks on the encoding and on each construction (support, counts, normalization);
   they are not claims of the manuscript and are not additional manuscript results."

## 10. Evidence produced by this review

* `lake env lean -DautoImplicit=false Probe1.lean` (imports `Challenge.SameLaw` only): non-vacuity proofs, `#check`
  of the main target (`forall x n, n <= extinctionTime x -> forwardLaw x n = reverseLaw x n`), and the expected
  `sorryAx` in `#print axioms` (Challenge). `Probe2.lean`: `n = 0` observables coincide for all `x` (full proof, no `sorry`).
  Both in a local scratch directory (not retained).
* `samelaw_enum.py`, `samelaw_enum2.py` (same directory): exact enumeration, run with `python3 -I`. 
* No edit to any existing file; no `lake build`; no `import Mathlib`.
