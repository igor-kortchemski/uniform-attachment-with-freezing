# Independent review of `Challenge/Sir.lean` (T06 and T07, physical SIR epidemic)

Reviewer: independent (did not write the Challenge, the development, or the notes). Read-only review.
Source: `attachement-uniforme-1-final.tex`, SHA-256 `88953dd8...ab00df` (verified). Challenge: 964 lines, 54,188 bytes,
module `Challenge.Sir`, config `comparator/sir.json`. Method: the source statements were reconstructed from the tex
first (section 1), then the Challenge definitions were read by what they compute, not by their names (section 2).
Evidence run by me: `lake env lean -DautoImplicit=false Challenge/Sir.lean` gives exactly the 11 expected
`declaration uses sorry` warnings (40 s); a probe importing `Challenge.Sir` confirmed that the instance
`MeasurableSpace PlaneTree.Tree` is `borel` (by `rfl`) and that `infectionProbability lam 1 = lam / (1 + lam)`.
Not done: official Comparator, kernel replay, proofs (the review is statement-only).

## 0. Verdict summary

No statement is unfaithful and none is false as far as I can tell. Nothing is blocking for statement fidelity.
Two items should be fixed before a Palomar deposit: non-vacuity of `PoissonSIRData` is not shown in Lean (F1), and
the `setMainModule` metaprogramming is a deposit risk (F2).

| Target (Lean name, lines) | Manuscript item | Verdict |
| --- | --- | --- |
| `physical_sir_geometric_local_limit_of_source_ratio` (881-887) | T06 (I) | faithful with caveat (C1) |
| `physical_sir_not_tight_of_source_ratio` (890-895) | T06 (II) | faithful with caveat (C1) |
| `physical_sir_fluid_limit_of_source_ratio` (900-906) | T07 (I)(a) | faithful with caveat (C2) |
| `physical_sir_uniform_height_limit_of_source_ratio` (851-857) | T07 (I)(b), height | faithful |
| `physical_sir_uniform_distance_limit_of_source_ratio` (861-867) | T07 (I)(b), distance | faithful |
| `physical_sir_strong_uniform_fluid_limit_of_source_ratio` (909-916) | T07 (II)(a) | faithful |
| `physical_sir_strong_terminal_uniform_height_of_source_ratio` (919-925) | T07 (II)(b), $H(V_1)/\ln n \to 1$ | faithful |
| `physical_sir_strong_terminal_uniform_distance_of_source_ratio` (928-934) | T07 (II)(b), $d/\ln n \to 2$ | faithful |
| `physical_sir_strong_terminal_maximum_of_source_ratio` (937-944) | T07 (II)(b), $\mathrm{Height}/\ln n \to e$ | faithful |
| `PoissonContact.first_law` (634-637) | sanity pin | adequate for what it pins |
| `PoissonSIRData.treePathLaw_eq` (958-960) | sanity pin | adequate for tree and susceptibles; incomplete (F1, F3) |

## 1. Reconstruction from the tex only (lines 2023-2104)

* Model: $n+1$ individuals, one infectious at time 0 (just infected), $n$ susceptible. Infectious periods iid Exp(1).
  During its period an infective contacts each given individual at the points of a Poisson process of intensity
  $\lambda_n$; contacting a susceptible infects it at once; all processes independent of each other and of the periods.
  A step is an infection or the end of an infectious period; $\tau_n$ steps until no infective is left.
* $\mathscr T^n_k$: infection tree after $k$ steps, vertices = individuals (necessarily the infected ones, since it is a
  tree), edges infector-infectee; $\mathscr T^n=\mathscr T^n_{\tau_n}$.
  $(U^n_k,I^n_k)$ is the embedded chain from $(n,1)$, infection w.p. $\lambda_n U/(1+\lambda_n U)$, absorbing at $I=0$;
  $\mathscr T^n_k \overset{d}{=} \mathcal T_k(\XXb^n)$ (Algorithm 1: $+1$ attaches a new vertex to a uniform active vertex,
  $-1$ freezes a uniform active vertex).
* T06 (I): $\lambda_n\sim\lambda/n$, $\lambda>0$: $\mathscr T^n \to$ Bienaymé tree with offspring $\mathcal G(1/(1+\lambda))$,
  i.e. $\mu(k)=(1-p)p^k$ with $p=\lambda/(1+\lambda)$ (tex 2046), locally, in distribution. (II): $\lambda_n\gg 1/n$:
  $\mathscr T^n$ not tight for the local topology.
* T07 (I): $\lambda_n\sim\lambda/n$, $\lambda>1$, $A$ = survival of the $\mathcal G(1/(1+\lambda))$ Bienaymé process.
  (a) $(I^n_{\lfloor nt\rfloor}/n)_{t\ge0}\to (\max(2-2g_\lambda(t)-t,0)\mathbf 1_A)_{t\ge0}$ in distribution, uniform topology on
  compacts, $g'=-\lambda g/(1+\lambda g)$, $g(0)=1$. (b) $V_1,V_2$ independent uniform vertices of $\mathscr T^n$ given $\mathscr T^n$:
  $H(V_1)/\ln n\to \frac{\lambda}{\lambda-1}\mathbf 1_A$ and $d(V_1,V_2)/\ln n\to\frac{2\lambda}{\lambda-1}\mathbf 1_A$ in distribution.
  (II): $\lambda_n\gg1/n$: (a) $\sup_{0\le t\le2}|I^n_{\lfloor nt\rfloor}/n-\min(t,2-t)|\to0$ in probability;
  (b) $H(V_1)/\ln n\to1$, $d/\ln n\to2$, $\mathrm{Height}(\mathscr T^n)/\ln n\to e$ in probability.
* Constants cross-check: Theorem `thm:lineaire` with $c=(\lambda-1)/(\lambda+1)$ gives $(c+1)/(2c)=\lambda/(\lambda-1)$ and
  $(c+1)/c=2\lambda/(\lambda-1)$; $c=1$ gives $1,2$ and $f(1)=e$. All match the Challenge constants (866, 856, 943).
  The closed form $g$ solves $\log g+\lambda g=\lambda(1-t)$, equivalent to the ODE; it matches the Lambert form (tex 2119).

## 2. What the Challenge actually defines (by computation)

* Clock slots (385): `(v, none)` = infectious period of $v$ (real); `(v, some w)` = contact path $v\to w$ (an `ArrivalPath`,
  indexed by the infection age of $v$). `PoissonSIRData` (748-755): measurable, `iIndepFun` over all $(n+1)(n+2)$ slots,
  periods law `expMeasure 1`, every contact path has $\mathrm{Poisson}(\mathrm{rate}\cdot t)$ counting marginal for each fixed $t$.
* Protocol (647-727): from frame $(z,T,b)$ the live slots are infectious sources times {recovery, susceptible target}
  (401-406). Remaining value = delay minus current age, with delay = period, or the first path point strictly after the
  current age (`nextArrival`, 711; `count` = number of points $\le t$, 628). The strictly earliest live slot fires: recovery
  freezes the vertex, a contact infects $w$, which gets birth time = event time and the next child address of the infector
  (409-413). No strict winner (tie or no live slot): frame unchanged (680-684).
* Why this is the SIR epidemic: a live pair $(v,w)$ starts live with age $0<a_0$ ($a_0$ = first point, positive by
  `ArrivalPath`); the run takes the minimum over live slots, so time never passes $a_0$ without firing, and the slot dies when
  $v$ recovers or $w$ is infected. Hence only the first point $a_0$ of each path is ever used (outside null ties), and
  contacts to non-susceptibles are ignored. Memorylessness then gives infection probability $\mathrm{rate}\,U/(1+\mathrm{rate}\,U)$ with a
  uniform infective acting. This is the manuscript's chain, and the development proves exactly this
  (`independent_poisson_fullContact_eq_preassigned`, SIRPoissonFullContactLaw 28).
* Age-indexed versus calendar-time Poisson processes (manuscript): same law of the epidemic, because $b_v$ is a function of data
  that never involve the outgoing paths of $v$ (not yet infectious), so the shifted path is again a Poisson process independent of $b_v$.
* Tree (`PlaneForward`, 183-233): vertices = addresses of ever-infected individuals (root `[]`), child index = chronological
  rank among the infector's children (`newChild`, 200), recovery keeps the vertex and removes it from `active`. Parent = infector,
  vertices = ever-infected, plane order = infection order: correct. A terminal state needs at most $n$ infections and $n+1$
  recoveries, so step $2n+1$ is the terminal tree (a.s.).
* Uniform sampling (253-274, 315-318): uniform over all of `s.vertices` (root and frozen vertices included); pairs are two
  independent uniform draws (diagonal allowed); height = address length = depth; distance = `SimpleGraph.dist` of the
  parent graph, which is the tree metric on a valid state. Annealed law (given tree, then sample), as in the manuscript.
* Limit objects: `geometricBienaymeLaw p` = pruned iid offspring field with $\mu=$ `geometricMeasure (1-p)`, i.e.
  $\mu(k)=(1-(1-p))^k(1-p)=p^k(1-p)$ with Mathlib's convention $(1-q)^kq$ (checked in Mathlib source); `p = infectionProbability lam 1 = lam/(1+lam)`. Survival $A$ =
  `¬FiniteVertices` (infinite tree). `geometricSurvivalPath lam T` = profile if $T$ infinite else $0$; scalar version $c\mathbf 1_A$.

## 3. Answers to the specific questions

**(a) `hratio` / `hlam`.** `rate n / (lam/n) -> 1` is $\lambda_n\sim\lambda/n$ (`lam : NNReal`, `0 < lam` for T06 (I), `1 < lam` for
T07 (I)); `rate n / (1/n) -> infinity` is $n\lambda_n\to\infty$, i.e. $\lambda_n\gg1/n$ (any growth, e.g. constant, allowed).
Faithful. Division by $0$ at $n=0$ is junk but irrelevant (`atTop`).

**(b) Protocol and tree.** Correct operational definition (section 2). Residual conventions: ties halt the run (null event);
self slots `(v, some v)` carry data but are never live; the protocol is total (junk values only off the support).

**(c) Sampling and normalisation.** Faithful: all vertices including root, independent pair with diagonal, $\ln n$ = `Real.log n`
(natural log; $n+1$ individuals, $n$ susceptible as in the manuscript). Height of tree = `Finset.sup vertices List.length` (max depth).

**(d) Limit objects and topologies.** Mixture $c\mathbf 1_A$ is encoded exactly (law of $c\cdot\mathbf 1_{\{\text{tree infinite}\}}$, Dirac at $0$ on
extinction). For the path, `PopulationPath` = all functions $\mathbb R_{\ge0}\to\mathbb R$ with uniform convergence on $[0,m]$, $m\in\mathbb N$
(metrisable, complete, non-separable), Borel $\sigma$-algebra. Not vacuous and not degenerate: prelimit laws are carried by countably
many step paths (`scaledPopulationPath` has countable range, so it is measurable), the limit is a two-point law; weak convergence
(`ProbabilityMeasure` topology) is the usual one, Portmanteau holds in any metric space, and by Tietze it coincides with weak
convergence in the closed subspace of right-continuous functions with the topology of $\mathbb D$ with locally uniform distance, i.e. the
manuscript's notion; so it is neither stronger nor weaker. T07 (II)(a) is stated directly as $\mu_n\{\exists t\in[0,2]:|\cdot|\ge\varepsilon\}\to0$
for every $\varepsilon>0$ on the counts history (no path space), the exact meaning of "in probability, uniform topology" against a
deterministic limit (the event is a cylinder over finitely many coordinates, hence measurable).

**(e) Non-vacuity of `PoissonSIRData`.** Mathematically satisfiable (F1). Construction: on a product space carry iid Exp(1) variables
$(E_{c,i})$ for contact slots and one Exp(1) per recovery slot. For contact slot $c$ let $a_k=(E_{c,0}+\dots+E_{c,k})/\mathrm{rate}$ on the
measurable full-measure set where all $E>0$ and $\sum E=\infty$, and $a_k=k+1$ elsewhere; this meets `ArrivalPath` at every $\omega$
(strictly increasing, positive, $\to\infty$), independence holds because slots use disjoint coordinates, and the count at $t$ is
$\mathrm{Poisson}(\mathrm{rate}\,t)$. Observations: (i) rate $=0$ is *inconsistent* with the structure (count $=0$ a.s. at every $t=m$ would give
$a_0>m$ for all $m$), so `PoissonSIRData` implies $0<$ rate, `hr` in 958 is redundant and the docstring 743-747 ("positivity kept separate") is misleading (F7);
(ii) marginal-only `HasPoissonCounts` cannot make a target false or vacuous: the protocol only reads the first point of each path
(section 2), `first_law` shows this point is Exp(rate) from the count marginals alone, and the periods and first points are independent
by `iIndepFun`; so every admissible family gives the same epidemic law as true Poisson processes. The admissible class is larger than
"Poisson processes" but equivalent for all 11 targets. (iii) No existence theorem is in the Challenge (F1).

**(f) `∀ᶠ n` and probability instances.** `hdata` only for large $n$ makes each theorem stronger, not junk. `∀ n, IsProbabilityMeasure (mu n)`
is a genuine requirement (satisfiable). T06 (II) ranges over all $n$ in `Set.range`: adding finitely many probability measures on the Polish
space `Tree` cannot change tightness, so this equals the tail statement.

**(g) Sanity targets.** `first_law` pins the parametrisation (Exp(rate), not mean-rate), the `count` convention and `HasPoissonCounts`.
`treePathLaw_eq` pins protocol = chain on $(U,\text{tree})$ with $P(\text{infection})=\mathrm{rate}\,U/(1+\mathrm{rate}\,U)$ (this also pins period rate 1,
the uniform choice, the plane order, and, for $n\ge1$, measurability of the tree history, since the right side is not a Dirac mass). Not pinned:
(1) existence/non-vacuity; (2) $I$: `physicalCountsPathLaw` (764-768) reads `population.active.card`, used in T07 (I)(a),(II)(a), and nothing in the
Challenge ties it to the chain; (3) nothing else is missing (terminal step $2n+1$ is implied by the chain: every step from a non-terminal state attaches or freezes).

**(h) Metaprogramming devices.** See F2: statement-neutral (they only rename private auxiliary declarations and drop matcher sharing), the
local diagnostic confirms identical reachable constants, but a Palomar reviewer may reject or query them.

## 4. Findings

| ID | Severity | Where | Finding |
| --- | --- | --- | --- |
| F1 | should-fix (highest) | 748-755, 634-637, 958-960; header 50-55 | Satisfiability of `PoissonSIRData` is not established in Lean, and both sanity targets are implications from it. If it were unsatisfiable all 11 targets would be vacuous. I believe it is satisfiable (construction in (e)). Add an existence target when the worker's proof lands: `0 < rate -> ∃ (Ω : Type) (_ : MeasurableSpace Ω) (mu : Measure Ω) (_ : IsProbabilityMeasure mu) (X : (c : ClockSlot n) -> Ω -> ClockDatum c), PoissonSIRData mu n rate X` (about 8 lines), and preferably the family version matching the main hypotheses (`Ω : ℕ -> Type`, `∀ n, 0 < rate n -> ...`). Until then document the gap. |
| F2 | should-fix (deposit risk, medium) | 179, 235, 248, 286, 309, 348, 489, 964 (`run_cmd Lean.modifyEnv (·.setMainModule …)`); 135, 691 (`bootstrap.genMatcherCode false`); 666-670, 533-536 (hand-written `advanceClockFrame.match_1`, `geometricSurvivalScalarLaw._proof_1`) | Statement-neutral, as far as I can see: `setMainModule` only changes the module prefix of private auxiliary names (`_private.<Module>.0…`) created afterwards and is restored at 964 (needed, else the olean carries the wrong module name); the matcher options/aux copies only prevent sharing of identical matchers and proofs. The hand-written `match_1` is `Option.casesOn`, the generated shape, and the local diagnostic reports all reachable constants identical. Risks: (i) `Lean.modifyEnv` is arbitrary meta code in the trusted statement file, so an auditor must read all nine lines; (ii) hard-coded module names (`Challenge.Sir` restore) and reliance on private-name mangling of `omega`/`simp`/`deriving`; (iii) the earlier independent review of `Challenge/SameLaw.lean` rated the same device Medium and asked for removal; (iv) the file is far from "small and readable" for Palomar. Mitigation: fix at source (reachable definitions without tactic-generated private auxiliaries, explicit `Countable` instances, avoid identical matchers inside one module) so that the Challenge is plain text; or obtain Palomar confirmation. Disclose in `formalization.yaml` if kept. |
| F3 | should-fix (minor-moderate) | 764-768 vs 958-960 | The counts history `(U,I)` used by T07 (I)(a) and (II)(a) is not pinned. By inspection $I$ = `active.card` of the infectious individuals = number of active tree vertices (infection inserts one individual and one vertex; recovery erases one of each), so the target is faithful, but the verification rests on reading. Cheapest pin (about 10 lines): `physicalCountsPathLaw mu n X = (physicalTreePathLaw mu n X).map (fun H k => ⟨(H k).susceptible, (H k).tree.active.card⟩)` (needs a development lemma). The worker's `countsPathLaw_eq` costs about 70 lines. Margin to the 1000-line cap is 36 lines (F9). |
| F4 | minor | 527, 540, 761, 766, 773, 779 (and 584, 783-791, 823, 831) | In this Mathlib `Measure.map f` for non-a.e.-measurable `f` is a Dirac junk value and `ProbabilityMeasure.map` takes no measurability argument, so the `IsProbabilityMeasure` instances do not certify measurability. Every pushforward here is in fact measurable: countable range with measurable fibres (`scaledPopulationPath`, `shape`, terminal tree), Borel two-valued maps (`geometricSurvivalPath/Scalar`, development lemmas `measurable_geometricSurvivalPath`, `measurable_scaledPopulationPath`, `measurableSet_finiteVertices`), discrete-source maps, and the run map from `measurable` of the data (`aemeasurable_poissonFullContactTreePath`, `measurable_clockFrameStep`). Record this in the account. |
| F5 | minor (caveat C1) | 93-96, 154-163, 770-774 | See C1. |
| F6 | minor (caveat C2) | 499-501, 509-529 | See C2. |
| F7 | minor | 743-747 | Docstring says positivity of the rate is "kept separate"; in fact rate $=0$ contradicts `HasPoissonCounts` on `ArrivalPath` (e). Reword; `hr` at 958 is harmless but redundant. |
| F8 | minor | 631-632, 748-755 | `HasPoissonCounts` is a marginal specification, not "is a Poisson process". Say explicitly that the epidemic law only depends on first points, hence the class is equivalent to true Poisson contact processes (see `first_law`). |
| F9 | minor | file size | 964 lines (cap 1000, "aim comfortably below"), 54 KiB (cap 100 KiB). Any new target (F1, F3) must fit in about 36 lines; docstrings (header 34-64) can be shortened if needed. |
| F10 | info | 680-684 | Totalisation: a tie or an empty live set holds the frame forever. Only null events; terminal step $2n+1$ is exact a.s. Mention in the account. |
| F11 | info | 77, 290, 380, ... | `set_option backward.isDefEq.respectTransparency false` appears in many blocks (copied from the development); it affects elaboration only and the final terms are the ones checked; a reviewer may ask. |

## 5. Caveats to document (suggested wording, for `formalization.yaml` / README / report)

* C1 (trees). The infection tree is encoded as a rooted locally finite plane tree (Ulam-Harris offspring field, product topology =
  local topology), with children ordered by infection time. The manuscript's local topologies include labelled and unlabelled
  (plane) versions and the manuscript does not fix the plane order of $\mathscr T^n$. Its proof gives convergence of the
  edge-labelled tree (Theorem `thm:cvlocale`), which implies the chronological plane convergence, which implies unlabelled non-plane
  convergence: so T06 (I) is implied by what the paper proves and implies the coarser reading; the limit is the plane Galton-Watson tree
  (iid subtrees, ordering by birth time does not change this law). For T06 (II), non-tightness in the plane topology is implied by
  non-tightness in the coarser non-plane topology (which holds, since the root degree tends to infinity in probability) and implies
  non-tightness for labelled trees; so the formal statement is the natural reading and is true in every reading.
* C2 (paths). Weak convergence of the scaled infectious count path is on the non-separable space of all functions with locally uniform
  distance and Borel $\sigma$-algebra; the prelimit laws are countably supported and the limit is $q\delta_{\text{profile}}+(1-q)\delta_0$,
  $q=1-1/\lambda$; this is equivalent to the manuscript's convergence in $\mathbb D$ with the uniform topology on compacts.
* C3 (model). Contact paths are indexed by the infection age (not calendar time), with the same law of the epidemic; the contact data is a
  random element of the space of entire strictly increasing paths with Poisson counting marginals, independent over all ordered pairs and of
  the periods; only the first point of each path matters.
* C4 (hypotheses). `PoissonSIRData` is assumed only for large $n$; each $\Omega^n$ is a separate probability space; $\lambda_n$ is `rate n`.
* C5 (status). Non-vacuity of `PoissonSIRData` is not proved in the Challenge (until F1 is closed); the two extra targets are consistency
  checks, not manuscript statements.
* C6 (devices). Challenge uses `setMainModule`, `bootstrap.genMatcherCode false` and hand-written auxiliary declarations to align private
  auxiliary names with the multi-module development (F2); Palomar acceptance of these is unconfirmed.

## 6. Residual checks I did not do

Official Comparator in the Linux sandbox, independent kernels, `#print axioms` of the Solution, the proofs themselves, and a Lean proof of
non-vacuity. The argument for F1 and for the first-point reduction is mathematical, supported by the development theorem
`independent_poisson_fullContact_eq_preassigned`, which I read but did not re-verify. Source-level (manuscript) remarks: the statements are
consistent with Theorem `thm:lineaire` constants; the proof of T06 (I) passes from $\mathcal T_n(\XXb^n)$ to the terminal tree in one sentence
(tex 2059), which is plausible (a local ball is finalised at times $O(1)$) but not detailed.
