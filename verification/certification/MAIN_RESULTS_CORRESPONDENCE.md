# Correspondence: main results T01–T07 ↔ manuscript ↔ Lean export ↔ Challenge

Manuscript `attachement-uniforme-1-final.tex`, SHA-256 `88953dd87165a14b0e643c5b3d0075d8ce5ec39cdcfc0c25d313570fc3ab00df`
(2590 lines, unchanged). Every Lean name is in the namespace `Freezing1` unless it starts with `SIR.` or
`ForwardAnnealed.`/`CanonicalTree.` (all inside `Freezing1`). "Challenge" gives the module of `Challenge/` that
states the theorem verbatim with a `sorry` body and the Comparator configuration that selects it. Each Lean
export has the same name and the same type in the Challenge and in the project (`Solution`); the local
comparison checked this (`verification/certification/*/compare.log`; local diagnostic, not the official tool).

There are 20 conclusions: T01 (2), T02 (1), T03 (3), T04 (4), T05 (1), T06 (2), T07 (7).

| # | Result | Manuscript (tex lines) | Conclusion | Lean export | Challenge / config |
| --- | --- | --- | --- | --- | --- |
| 1 | T01 | `thm:cvlocale`, 257–268 | (I)⇔(II)⇔(III): local convergence in distribution of `T_n(x^n)`, a.s. local convergence of `T_n(x)` and divergence of `Σ 1_{X_i=−1}/S_i(x)`, given `τ(x)=∞` and pointwise eventual agreement of the rows with `x` | `local_convergence_equivalences` | `LocalLimits` / `locallimits.json` |
| 2 | T01 | idem, last sentence | `T_∞(x)` is the local limit of `T_n(x^n)` (a.s. limit measurable; weak limit of every approximating array) | `local_convergence_common_limit` | `LocalLimits` / `locallimits.json` |
| 3 | T02 | `thm:BGW`, 277–280 | for iid signs, `p∈[0,1)`: `T_∞(X)` exists a.s. and (as a plane tree) is a Bienaymé tree with offspring law `μ(k)=(1−p)p^k` | `ForwardAnnealed.iid_signs_geometric_local_limit` (supporting targets: `planeLimitLaw_isBienayme`, `planeLimitLaw_eq_geometricBienaymeLaw`, `planeLimitLaw_offspring_mass`) | `LocalLimits` / `locallimits.json` |
| 4 | T03 | `thm:height` (I), 297–301 | `H(U^n)/h_n^+ → 1` in `L^p`, every real `p≥1`, `U^n` uniform active vertex of `T_n` | `uniform_active_height_tendsto_Lp` | `Heights` / `heights.json` |
| 5 | T03 | `thm:height` (II), 302–305 | for every `ε∈(0,1)`, `P(1−ε ≤ Height(T_n)/h_n^+ ≤ e+ε) → 1` | `maximum_height_window_tendsto_one` | `Heights` / `heights.json` |
| 6 | T03 | `thm:height` (III), 306–309 | if `ln n/h_n^+ → 0`, `Height(T_n)/h_n^+ → 1` in `L^p`, every real `p≥1` | `maximum_height_tendsto_Lp` | `Heights` / `heights.json` |
| 7 | T04 | `thm:lineaire` (I), 316–325 | `h_n^+/ln n → (c+1)/(2c)` under (eq:assumptions) | `linear_heightScale_tendsto` | `Heights` / `heights.json` |
| 8 | T04 | `thm:lineaire` (II), height, 326–334 | `H(V_1^n)/ln n → (c+1)/(2c)` in `L^p`, `V_1^n` uniform among all vertices of `T_n` | `linear_uniform_height_tendsto_Lp` | `Heights` / `heights.json` |
| 9 | T04 | `thm:lineaire` (II), distance, 326–334 | `d^n(V_1^n,V_2^n)/ln n → (c+1)/c` in `L^p`, two conditionally independent uniform vertices (diagonal included) | `linear_uniform_distance_tendsto_Lp` | `Heights` / `heights.json` |
| 10 | T04 | `thm:lineaire` (III), 335–339 | `Height(T_n)/ln n → ((c+1)/(2c))·f(c)` in probability; `f(c)>1` the unique root of `f(ln f−1)=(c−1)/(c+1)` | `linear_maximum_deviation_tendsto_zero`; the constant is pinned by `linearHeightFactor_existsUnique`, `linearHeightFactor_spec` | `Heights` / `heights.json` |
| 11 | T05 | `thm:samelaw`, 655–664 | `T_n` and `T̂^n` have the same distribution (every `0≤n≤τ`, including `n=τ`) | `CanonicalTree.construction_laws_eq` | `SameLaw` / `samelaw.json` |
| 12 | T06 | `thm:SIRlocallimit` (I), 2047–2054 | `λ_n∼λ/n`: the infection tree `𝒯^n` converges locally in distribution to a Bienaymé tree with offspring `𝒢(1/(1+λ))` | `SIR.physical_sir_geometric_local_limit_of_source_ratio` | `Sir` / `sir.json` |
| 13 | T06 | `thm:SIRlocallimit` (II), 2047–2054 | `λ_n ≫ 1/n`: `𝒯^n` is not tight for the local topology | `SIR.physical_sir_not_tight_of_source_ratio` | `Sir` / `sir.json` |
| 14 | T07 | `thm:SIR` (I)(a), 2080–2087 | `λ_n∼λ/n`, `λ>1`: fluid limit `max(2−2g_λ(t)−t,0)·1_A` in distribution, uniform on compacts | `SIR.physical_sir_fluid_limit_of_source_ratio` | `Sir` / `sir.json` |
| 15 | T07 | `thm:SIR` (I)(b), height, 2088–2093 | `H(V_1^n)/ln n → (λ/(λ−1))·1_A` in distribution | `SIR.physical_sir_uniform_height_limit_of_source_ratio` | `Sir` / `sir.json` |
| 16 | T07 | `thm:SIR` (I)(b), distance, 2088–2093 | `d^n(V_1^n,V_2^n)/ln n → (2λ/(λ−1))·1_A` in distribution | `SIR.physical_sir_uniform_distance_limit_of_source_ratio` | `Sir` / `sir.json` |
| 17 | T07 | `thm:SIR` (II)(a), 2095–2101 | `λ_n ≫ 1/n`: `I^n_{⌊nt⌋}/n → min(t,2−t)` in probability, uniformly on `[0,2]` | `SIR.physical_sir_strong_uniform_fluid_limit_of_source_ratio` | `Sir` / `sir.json` |
| 18 | T07 | `thm:SIR` (II)(b), height, 2102–2104 | `H(V_1^n)/ln n → 1` in probability | `SIR.physical_sir_strong_terminal_uniform_height_of_source_ratio` | `Sir` / `sir.json` |
| 19 | T07 | `thm:SIR` (II)(b), distance, 2102–2104 | `d^n(V_1^n,V_2^n)/ln n → 2` in probability | `SIR.physical_sir_strong_terminal_uniform_distance_of_source_ratio` | `Sir` / `sir.json` |
| 20 | T07 | `thm:SIR` (II)(b), maximum height, 2102–2104 | `Height(𝒯^n)/ln n → e` in probability | `SIR.physical_sir_strong_terminal_maximum_of_source_ratio` | `Sir` / `sir.json` |

All 26 exported names (the 20 conclusions plus `planeLimitLaw_isBienayme`, `planeLimitLaw_eq_geometricBienaymeLaw`,
`planeLimitLaw_offspring_mass`, `linearHeightFactor_existsUnique`, `linearHeightFactor_spec` and the non-vacuity theorem
`SIR.PoissonSIRData.exists_data`) have the axiom
closure `[propext, Classical.choice, Quot.sound]` (`scripts/MainResultsAxioms.lean`; log in
`verification/certification/candidate/`).

## What each statement is, and where it differs from a literal reading of the manuscript

Sources: the independent statement reviews `heights/`, `locallimits/`, `samelaw/`, `sir/` `INDEPENDENT_REVIEW.md`
(automated, written from the manuscript before reading the Lean, without reading the proofs) and the limits in
`OPEN_OBLIGATIONS.md`. No review found an unfaithful or vacuous statement; the caveats below are the exact
points a reader must be told.

* **#1–#3 (T01, T02).** Stated on the *chronological* local space `LocalTree.Tree` (vertices identified by birth
  time), the closed subspace of the paper's double-labelled local space containing every `T_n(x)` (the docstring says
  so). The unrestricted unordered statements are proved in the project (`source_local_convergence_*`) but their
  statement closure (~1800 lines) exceeds the Challenge limit. Rows are extended by holding after extinction
  (Algorithm 1) and carry no hypothesis `τ>n`. T01 is about the double-labelled topology (plane/unlabelled variants of
  (I) are not asserted). T02 is about the plane tree with children ordered by birth time and labels erased, for the
  annealed history law (signs integrated out); `p=0` included, `p<1` exact; `fullLaw_tendsto_localLimit` and
  `aemeasurable_localLimit` are extra pins (labelled a.s. convergence and genuine, non-junk push-forward).
  `ProbabilityMeasure.map` of a non-a.e.-measurable function is a junk Dirac measure in Mathlib; T01 states
  a.e.-measurability as its first conjunct, and T02's limit is shown a.e.-measurable by the pin.
* **#4–#10 (T03, T04).** Rows `x^n` satisfy `τ(x^n)>n` (the manuscript's standing assumption; forces `S_i≥1`);
  eq:assumptions is reproduced with real `limsup`/`liminf` of bounded sequences (no junk values). Uniform active
  sampling in #4, uniform all-vertex sampling (frozen vertices included) in #8–#9, pair law conditionally independent
  with the diagonal. `L^p` is `eLpNorm … (ofReal p) → 0`, real `p≥1`. Satisfiability of the hypotheses is checked in
  `heights/non-vacuity/` (all-plus rows, period-3 rows, alternating rows).
* **#11 (T05).** The two laws are compared on the canonical observable (vertex ids = birth times of incoming edges, graph,
  active ids, frozen times), not literally on isomorphism classes; the review argues the observable is injective on
  both supports and in bijection with labelled-tree isomorphism classes (an exact enumeration of both algorithms up to
  schedule length 6 agrees). Algorithm 2 follows the manuscript's Algorithm 2, not the swapped-sign sentence of tex line 312.
* **#12–#20 (T06, T07).** Physical full-contact SIR dynamics driven by `PoissonSIRData` (iid exponential recoveries,
  pairwise contact paths with Poisson counting marginals, all independent; contact paths indexed by infection age;
  only the first point of each path is read, and `first_law` pins its law). `λ_n ∼ λ/n` / `λ_n ≫ 1/n` are encoded by
  `rate n/(1/n)` having the limit λ / diverging. The infection tree is a plane tree with children ordered by
  infection time (the manuscript does not fix the plane order; the formal statements are true in every reading, see
  review C1). Limit laws are annealed (mixtures with the survival event `A`) on `ProbabilityMeasure`; the population path
  space is the non-separable space of all real functions with the locally uniform distance and Borel σ-algebra, which
  gives the same weak convergence as the manuscript's `𝔻` (review C2). **Non-vacuity of `PoissonSIRData` is proved in
  Lean** (`SIR.PoissonSIRData.exists_data`: for every `n` and every rate `>0`; `exists_family` for eventually positive
  rate sequences); at rate `0` the hypothesis is unsatisfiable, so the physical theorems implicitly require a positive
  rate, which they derive from the ratio hypothesis. The counting history `(U, I)` used by #14 and #17 is read as
  (susceptibles, active tree vertices); only the tree history is pinned (`treePathLaw_eq`), not the counts history. The
  proofs bypass the manuscript's embedded-chain/Skorokhod arguments.
