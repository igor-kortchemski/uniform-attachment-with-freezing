# Formalization report

## Source, scope, and audit identity

- **Paper:** *Uniform attachment with freezing*, supplied as `attachement-uniforme-1-final.tex`; the unchanged manuscript is intentionally omitted from this candidate export.
- **Source SHA-256:** `88953dd87165a14b0e643c5b3d0075d8ce5ec39cdcfc0c25d313570fc3ab00df` (2,590 lines).
- **Scope:** every theorem, proposition, lemma, corollary, and substantive mathematical assertion in the supplied source. The Introduction supplies the main results. No mathematical section is excluded. Explicit conjectures and research questions are catalogued separately.
- **Project:** `freezing1`; entry point [Freezing1.lean](Freezing1.lean). Lean and Mathlib remain pinned to `v4.35.0`, with exact dependencies in `lake-manifest.json`.
- **Destination:** private GitHub repository `igor-kortchemski/uniform-attachment-with-freezing`, with Palomar preparation. License: Apache-2.0 for code and original documentation; contributor and responsible maintainer: Igor Kortchemski. A private repository cannot satisfy Palomar intake.
- **Publication order:** the user has clarified that formalization must precede publication. Further repository uploads and publication operations are suspended. The private remote contains an earlier partial snapshot; the local development below has advanced beyond it.
- **Current milestone:** T01–T07 main theorem conclusions, P01 and C01 are proved. The actual unordered bijection and full tangent/Bernoulli enumeration are checked. A21/A22, A27, A28, A32–A34, A36 and the paper's random-mean height argument A40–A43 are proved, including conditional moments and corrected harmonic tails. Both physical SIR rate branches and the complete joint original-forward history adapter A65–A66 are proved. Scoped independent audits and current build/axiom evidence are listed below. Remaining intermediate obligations are retained explicitly; no whole-paper completion or verified final publication candidate is claimed. Uploads remain suspended.
- **Initial independent source audit:** 29 October 2026, by the inventory reviewer, before reading implementation proofs. The entire mathematical prose, all result environments, and all displayed proof arguments were read. Figure drawing commands and bibliography entries are not mathematical obligations. Commented-out TeX and struck-out editing remnants are not new assertions; live surrounding assertions remain in scope.

The source has **24 named result environments**: 7 theorems, 13 lemmas, 3 propositions, and 1 corollary. The one `remark` environment is an open question. The tables below split compound results into separate conclusions and retain substantive unnamed claims, including those asserted inside proofs. Source locators refer to the fixed source hash above. Stable IDs are for correspondence, not a claim that a row is proved.

## Current proof and publication status

At the current milestone, **all three parts of the Introduction's universal height theorem T03 are proved**, together with **all parts of T04, L01, L02, L05, L06, L07, L08, L09, L10, L11, L12, T05 and P02**. The **lower half of P03** is proved. Corrected distinct-vertex L03 and corrected P03 upper bounds are proved separately from the false literal statements. A05, A09, A11, A17, A39, A44 and A46 are covered. **T01 is proved, including its three equivalences and common limit law. T02 is proved for the actual iid-sign history and chronological plane limit. Every T06 and T07 conclusion is proved for the embedded model and transferred to the actual full-contact protocol under the source's eventually valid independent process data. Both finite-rate terminal weak mixtures and all strong-regime terminal geometry limits are proved. P01 and C01, unique consecutive reindexing and the source random-mean height proof A40–A43 are also proved. Both physical rate branches and the complete joint history identity A65–A66 are checked. The retained intermediate obligations remain open.** L02 and L09 use actual conditional uniform sampling. The literal source contains false assertions identified below; they are not marked proved by adding hypotheses or changing indices.

The isolated main-results candidate at `54253ce` now has a successful clean
Linux build, axiom audits, and official sandboxed Comparator/NanoDa/Lean
acceptance for all four main interfaces plus the auxiliary one. See
[the Linux evidence](verification/certification/linux/SUMMARY.md). This verifies
the audited interface scope, not paper-wide coverage or a complete Palomar
publication candidate. No full Palomar mechanical report or publication is
claimed. Earlier dated checkpoints below are retained as history.

The resumed local development constructs both actual graph laws, their structural invariants, and a coherent reverse history. L01's conditional probability given the entire preceding history is now proved, as is the birth-truncated independent Bernoulli law of each reverse vertex height. The reverse maximum lower tail in P03 and a corrected upper tail with the true vertex count are proved. Stamped reverse forests retain every edge time and frozen label; their increasing-label invariant, canonical graph coordinates, legal-history uniqueness and actual one-step probabilities are checked. Equality in law of the two constructions is now proved on the full canonical states and on their rooted, edge-timestamped, frozen-label-preserving observable. T03 uses a direct forward MGF argument with arbitrary real powers and varying probability spaces; all of its probabilistic premises are discharged from the actual constructed laws.

## Main results and named obligations

Rows remain open unless explicitly marked below. A range in the source column includes the statement; referenced proof sections are listed where useful. `—` means no proved Lean declaration has been identified. Proof status is distinct from whether the paper’s own argument was checked.

| ID | Source locator | Mathematical obligation | Lean declaration / coverage | Principal dependencies or fidelity issue |
| --- | --- | --- | --- | --- |
| T01 | 257–268, `thm:cvlocale`; proof 891–921 | For pointwise eventually equal schedules with limiting schedule never hitting zero: equivalence of distributional local convergence of the diagonal trees, almost sure local convergence under the fixed schedule, and divergence of the freezing reciprocal sum; identify the common limit law. | `Freezing1.local_convergence_equivalences`, `local_convergence_common_limit` / **proved** | Actual infinite trajectory, Polish locally finite labelled trees and exact source sum over $1\le i\le n$. No survival condition on approximating schedules. Corrected pre-step hazards are compared to the printed post-step reciprocal series. Necessity uses root-degree marginal tails instead of the source conditional-independence argument. |
| T02 | 277–280, `thm:BGW`; proof 978–1012 | For every $0\le p<1$, iid signs with attachment probability $p$ yield the geometric Bienaymé tree with offspring mass $(1-p)p^k$. | **Proved:** `ForwardAnnealed.iid_signs_geometric_local_limit`, `planeLimitLaw_isBienayme`, `planeLimitLaw_eq_geometricBienaymeLaw`, `planeLimitLaw_offspring_mass` in `MainGeometricLimit`. | Actual iid-sign history law, chronological plane ordering, extinction and $p=0$ included. |
| T03.I | 293–301, `thm:height` | Height of a conditionally uniform active vertex divided by $h_n^+$ tends to $1$ in every real $L^p$, $p\ge1$. | `Freezing1.uniform_active_height_tendsto_Lp` / **proved** | Actual forward tree and conditional uniform active sampling; all admissible triangular schedules, varying laws, every real $p\ge1$. Direct forward averaging/MGF proof bypasses L01/A13/T05; L01 and the Bernoulli representation have since been checked separately, while T05 has since been proved separately. |
| T03.II | 302–305, `thm:height` | With probability tending to one, normalized maximum height lies in $[1-\varepsilon,e+\varepsilon]$ for each $0<\varepsilon<1$. | `Freezing1.maximum_height_window_tendsto_one` / **proved** | Actual forward maximum; derived upper bound retains $n+1$ and a one-edge threshold shift, both controlled asymptotically. Does not certify the false P03 upper bound. |
| T03.III | 306–309, `thm:height` | If $\log n=o(h_n^+)$, maximum height divided by $h_n^+$ tends to $1$ in every real $L^p$, $p\ge1$. | `Freezing1.maximum_height_tendsto_Lp` / **proved** | Actual maximum tails, exponential moments, Jensen and Hölder/truncation supply all real-power moments; no assumed uniform-integrability or limit hypothesis. |
| T04.I | 316–325, `thm:lineaire`, `eq:assumptions` | Under both uniform linear-regime conditions and $A_n\to\infty$, $A_n=o(\log n)$, prove $h_n^+/\log n\to(c+1)/(2c)$ for $0<c\le1$. | `Freezing1.linear_heightScale_tendsto` / **proved** | Exact literal nested-limit assumptions, real cutoff and strict survival. L08 is proved by Abel summation; integer cutoff and early/late contributions are explicit. |
| T04.II.height | 326–334, `eq:fvprobahn` | A conditionally uniform vertex has height divided by $\log n$ tending in every real $L^p$, $p\ge1$, to $(c+1)/(2c)$. | `Freezing1.linear_uniform_height_tendsto_Lp` / **proved** | Actual forward tree, uniform sampling over active and frozen vertices, exact source assumptions and all real powers. Forward birth-mixture proof bypasses the reverse random-mean arguments A40–A43, which have since been verified separately with the stated source corrections. |
| T04.II.distance | 326–334, `eq:fvprobahn` | Two conditionally independent uniform vertices have distance divided by $\log n$ tending in every real $L^p$, $p\ge1$, to $(c+1)/c$. | `linear_uniform_distance_tendsto_Lp` / **proved** | Actual independent conditional samples, including the diagonal, literal source assumptions and every real exponent at least one. The logarithmic coalescence estimate fills the gap in the printed inference; exponential height moments supply the moment upgrade. |
| T04.III | 335–339, `thm:lineaire` | Maximum height divided by $\log n$ tends in probability to $((c+1)/(2c))f(c)$, where $f(c)>1$ is the unique root of $f(c)(\log f(c)-1)=(c-1)/(c+1)$. | **Proved:** `Freezing1.linear_maximum_deviation_tendsto_zero` | Exact source assumptions and constant. True forward continuation, permutation averaging, geometric good chains and their summable failures give the lower bound, combined with the established upper bound. The bypassed conditional forest arguments and literal weaker wording of L13 remain separate obligations. |
| T05 | 661–664, `thm:samelaw`; proof 685–720 | Forward attachment/freezing tree and reverse growth/coalescent tree have the same distribution after erasing the distinction between active labels. | `CanonicalTree.construction_laws_eq` / **proved** | Actual algorithms, including $n=\tau$. Full canonical-state law equality is also proved. Legal-history masses, exact $S_n!$ fibres and deterministic reconstruction supply the corrected support; the false printed L04 is not assumed. |
| T06.I | 2047–2054, `thm:SIRlocallimit` | If $\lambda_n\sim\lambda/n$, $\lambda>0$, the full SIR infection tree converges locally in law to the geometric Bienaymé tree with geometric parameter $1/(1+\lambda)$. | **Proved:** `SIR.physical_sir_geometric_local_limit_of_source_ratio` in `SIRPhysicalLimits`, with embedded theorem in `MainSIREmbedded`. | Actual full-contact terminal tree, supplied independent recovery/Poisson data, chronological local topology and exact source ratio. Positive rate is derived eventually; no blanket positivity assumption. |
| T06.II | 2047–2054, `thm:SIRlocallimit` | If $n\lambda_n\to\infty$, full SIR infection trees are not tight in the local topology. | **Proved:** `SIR.physical_sir_not_tight_of_source_ratio` in `SIRPhysicalLimits`. | Actual full-contact terminal root degree escapes finite bounds. Eventual source data and the exact rate ratio suffice; the source Prokhorov/Skorokhod route is bypassed. |
| T07.I.a | 2080–2087, `limite fluide I` | For $\lambda_n\sim\lambda/n$, $\lambda>1$, infectious-count paths scaled by $n$ converge in law uniformly on compacts to $\max(2-2g_\lambda(t)-t,0)\mathbf 1_A$, with one shared survival event $A$. | **Proved:** `SIR.physical_sir_fluid_limit_of_source_ratio` in `SIRPhysicalLimits`, with embedded theorem in `MainSIRFluid`. | Actual complete stopped count-path law, exact compact-uniform topology and the shared survival event of the concrete geometric Bienaymé tree. Full contact-history identification supplies the physical model. |
| T07.I.b.height | 2088–2093, `eq:cvprobaHn SIR` | Uniform-vertex height divided by $\log n$ converges in law to $\lambda/(\lambda-1)\mathbf 1_A$. | **Proved:** `SIR.embedded_sir_uniform_height_limit_of_source_ratio` in `MainSIRUniformSamplesFinite`; physical version `physical_sir_uniform_height_limit_of_source_ratio` in `SIRPhysicalFiniteLimits`. | Actual terminal all-vertex conditional uniform sample, divided by log n; weak limit on the concrete geometric survival event. Startup, finite-constraint T04 transfer, exact joint gates and terminal capture are discharged. |
| T07.I.b.distance | 2088–2093, `eq:cvprobaHn SIR` | Uniform-pair distance divided by $\log n$ converges in law to $2\lambda/(\lambda-1)\mathbf 1_A$. | **Proved:** `SIR.embedded_sir_uniform_distance_limit_of_source_ratio`; physical version `physical_sir_uniform_distance_limit_of_source_ratio`. | Actual independent conditional uniform pair from the same terminal tree, including diagonal/frozen vertices, actual graph distance and exact source rate ratio; concrete shared geometric survival target. |
| T07.II.a | 2095–2101, `eq:limite fluide presque recursif` | If $n\lambda_n\to\infty$, scaled infectious paths converge in probability uniformly on $[0,2]$ to $\min(t,2-t)$. | **Proved:** `SIR.physical_sir_strong_uniform_fluid_limit_of_source_ratio` in `SIRPhysicalLimits`; embedded theorem `countsFullLaw_strong_uniform_tendsto`. | Actual stopped physical count path on the entire real interval [0,2], floor time and n scaling; no survival premise. |
| T07.II.b.height | 2102–2104, `eq:cv Hn cas presque recursif` | In the same regime, uniform-vertex height divided by $\log n$ tends in probability to $1$. | **Proved:** `SIR.physical_sir_strong_terminal_uniform_height_of_source_ratio`; embedded theorem `sir_terminal_uniform_height_tendsto`. | Actual all-vertex terminal conditional uniform law at event 2n+1. Deterministic T04 uniformization, full adaptive count-prefix law and terminal subset comparison. |
| T07.II.b.distance | 2102–2104, `eq:cv Hn cas presque recursif` | In the same regime, uniform-pair distance divided by $\log n$ tends in probability to $2$. | **Proved:** `SIR.physical_sir_strong_terminal_uniform_distance_of_source_ratio`; embedded theorem `sir_terminal_uniform_distance_tendsto`. | Actual terminal graph metric and two independent conditional uniform draws from the same tree; frozen vertices and diagonal retained. |
| T07.II.b.maximum | 2102–2104, `eq:cv Hn cas presque recursif` | In the same regime, maximum height divided by $\log n$ tends in probability to $e$. | **Proved:** `SIR.physical_sir_strong_terminal_maximum_of_source_ratio`; embedded theorem `sir_terminal_maximum_of_source_ratio`. | Actual terminal maximum, exact source rate ratio, genuine post-n charge and cut maximum. Forward potential/exponential-sum route replaces the unchecked reverse coupling. |
| L01 | 584–590, `lem:accroissementH` | Conditional reverse-process height increment is Bernoulli with parameter $\mathbf 1_{X_i=1}/S_i$ for every valid vertex and index. | `ReverseHistory.height_increment_conditional_probability` / **proved** | Actual coherent history; conditioning is on the complete predecessor history. The joint law factors from the original transition kernel. Natural subtraction agrees with the nonnegative height increment on the proved support. |
| L02 | 601–607, `lem:bunif` | For a uniform vertex, $\Pr(b_n(V)<m)=(m+1-S_m)/(n+1+S_n)$ for $1\le m\le n\le\tau$. | `Freezing1.Reverse.uniform_birthTime_lt` / **proved for the constructed terminal reverse tree** | Exact uniform conditional vertex selection, deterministic phase membership and birth shift proved; proof prose error S03 retained. |
| L03 | 620–626, `loi du temps de coalescence` | Exact coalescence-time hazard/product law. | **False as printed; corrected version proved:** `ReverseHistory.fullLaw_coalescenceTime_eq` | The necessary premise $u\ne v$ is explicit (S02). The actual common-history maximum, its existence/range and persistence are proved. `fullLaw_coalescenceTime_self` handles the diagonal separately. |
| L04 | 670–674, `lem:loiTn` | Forward-tree probability equals $\prod_{i=1}^n1/S_{i-1}$ on the displayed tree class. | **False as printed; corrected support version proved:** `Forward.corrected_forward_tree_probability`, `treeLaw_singleton_ne_zero_iff_historyShape` | The fixed-schedule increasing shape is equivalent to a legal history, and its mass has the exact source product indexed by $1\le i\le n$, including absorption; see S01. |
| L05 | 953–956, `lem:BGW` | A plane-tree law with single-vertex mass $1-p$ and independent identically distributed first-child subtree and remainder is the geometric Bienaymé law. | **Proved:** `PlaneTree.law_eq_geometricBienayme_of_conditional_split`, `isBienayme_geometric_of_fixedPoint`. | Concrete iid law, uniqueness, actual reindexed remainder, and null conditioning at $p=0$ are handled. |
| L06 | 1133–1141, `lemme chaines de markov alternées` | The two embedded chains of a state-dependently interleaved Markov chain have the independent product law when every nonabsorbed coordinate is eventually selected. | **Proved:** `InterleavedChain.extracted_pair_map_eq_prod`, `extracted_pair_hasLaw`. | Exact minimum/fallback times and source `Fair` assumptions; the asynchronous factorization proof is bypassed. |
| L07 | 1235–1238, `lemme minoration h_n^+` | For $n\ge1$ and $\tau>n$, $h_n^+\ge\log(n/4)$. | `Freezing1.heightScale_lower_bound` / **proved** | The original harmonic proof is retained; A32 now separately checks the actual adjacent-swap/sorting proof. |
| L08 | 1311–1319, `lem:estimee uniforme sur h_n+` | Uniform logarithmic block asymptotics for reciprocal attachment sums, for every $C>1$ and $A_n\le a<b\le\varepsilon n$, $aC<b$. | `Freezing1.logIntervalLimsup_of_nearOriginLimsup` / **proved** | Exact finite maximum and order of limits; interval $(a,b]$, strict $aC<b$ and all $C>1$ retained. the Abel proof and a separately verified repaired geometric-block source proof are both available. |
| L09 | 1450–1455, `lemme ça coalesce en zéro` | Coalescence time of independent uniform vertices divided by $n$ tends in probability to zero in the linear regime. | `ReverseHistory.linear_uniform_coalescence_tendsto_zero` / **proved** | Actual same-history conditional independent uniforms, every active/frozen label and the diagonal included. The weaker bulk condition alone suffices. The printed incomplete averaging is repaired explicitly. |
| L10 | 1670–1676, `Forestier` | For each $\eta\in(0,1)$ choose $C\ge2$, $\lambda>0$, $\varepsilon\in(0,1)$ uniformly so that $\Pr(N_k^n(C,\eta)\le4C^k)\le\lambda/C^k$ throughout the stated range. | **Proved:** `linear_forward_geometricBlock_fewTallRoots_probability` | Actual forward cut count, the non-strict event and exact uniform quantifier order; the complete independent auxiliary coupling/thinning route is now also proved and independently audited, as recorded below. |
| L11 | 1681–1685, `Forestjump` | For large $n$ uniformly in $A_n\le C^k\le n/C$, $\Pr(M_k^n>k^3)\le k^{-2}$. | **Proved:** `linear_geometric_componentMaximum_tail` | Actual forward component maximum with the marked root included, exact geometric window and reciprocal-square failure bound; the original infinite positive-extension/component-path maximal route is now also proved, with the marked-root $+1$ correction. |
| L12 | 1798–1804, `lem:minoration` | For each $\eta\in(0,1)$ choose integer $C>1$ and $\varepsilon>0$ uniformly so that $\mathbb E N_k^n(C,\eta)\ge5C^k$ in the specified range. | **Proved:** `linear_forward_geometricBlock_expectation_lower` | Actual random-root count and exact geometric windows, with uniform $C,\varepsilon$. The exact cut-forest identification is proved; S09–S10 are repaired by the documented Poisson route. |
| L13 | 2001–2007, `Pólya` | Uniform maximal concentration of the normalized signed Pólya urn, with the displayed constants and reciprocal-square summability assumptions. | **Markov-path version proved:** `SignedUrn.infinite_maximal_summable`; literal weaker formulation unresolved | Exact constants, reciprocal-square sum, attained maximum reciprocal and infinite-time event; complete finite path laws are explicitly required. Conditioning only on the current state has not been shown sufficient (S11). |
| P01 | 858–865, unlabelled proposition | The recursive map $\Phi$ is a bijection between increasing frozen/active trees and increasing full plane binary trees, preserving the specified labels and parameters. | **Proved:** `BinaryBijection.unorderedPaperEquiv` and `phi_paper_bijective` in `UnorderedBinaryBijection`. | The source is an actual sibling-permutation/subtree-congruence quotient. Recursive normalization constructs its unique canonical representative; the intrinsic increasing predicate descends to the quotient. Phi/Psi inverses, active and integer labels, separate edge/frozen-label preservation and n versus 2n-1 size are checked. See `verification/UNORDERED_BINARY_AUDIT.md`; C01 enumeration remains separate. |
| P02 | 1180–1185, `prop:bennett` | Both upper and lower strict tails of an independent Bernoulli sum with positive mean $m$ are bounded by $\exp(-m g(t/m))$, $t>0$. | `Freezing1.bernoulli_sum_upper_tail`, `Freezing1.bernoulli_sum_lower_tail` / **proved** | $g(u)=(1+u)\log(1+u)-u$; both tails, not only a variance estimate. |
| P03 | 1200–1211, `prop:bounds` | Upper and lower maximum-height tails with exponents $-h_n^+g(t/h_n^+)+\log n$ and $-h_n^+g(t/h_n^+)$. | **Lower proved:** `reverseMaximum_lower_tail_source`; **upper false as printed**, corrected by `reverseMaximum_corrected_upper_tail_source` | Actual reverse tree, unshifted threshold and exact birth-truncated Bernoulli laws. Corrected upper factor is $N_n$ (or $n+1$); no independence between different vertex heights is assumed. S16 remains a refutation of the printed factor $n$. |
| C01 | 869–875, unlabelled corollary | $\#\mathfrak T_{0,n}^+=4^n(4^n-1)\vert B_{2n}\vert /(2n)=\tan^{(2n-1)}(0)$ for positive $n$. | **Proved:** `BinaryBijection.source_fullyFrozen_card_formula` in `TangentEnumeration`. | Actual finite unordered source class; explicit largest-label growth bijection proves the counting recurrence. Local real tangent derivatives and formal exponential/Bernoulli series discharge the exact coefficient identity; complex norms give the absolute value without a Bernoulli-sign assumption. Independent component and final-interface audits pass, with the $n=1$ boundary checked. The external cited counting argument is replaced by a direct proof. |

## Substantive unnamed assertions and proof obligations

Each row retains the mathematical assertions in the indicated source span as an obligation family. Routine restatements of a named conclusion point back to that conclusion. Displayed identities and estimates within these spans remain part of the family: a row is complete only when all of its assertions are verified, or when an explicitly recorded proof departure makes a source assertion unnecessary while leaving that assertion's source-check status unresolved. This grouping avoids pretending that a theorem inventory alone covers the paper.

| ID | Source locator | Assertion family retained in scope | Status |
| --- | --- | --- | --- |
| A01 | 245–249, 386–391, 438, 613; `eq:defintro` | Signed walk recurrence, attachment/freezing counts, $S_n=1+P_n-M_n$, $P_n+M_n=n$, $M_n=(n+1-S_n)/2$, and $N_n=(n+1+S_n)/2$ before absorption. | **Substantial coverage:** original walk/count identities plus actual random-tree `Forward.treeLaw_counts`, `Forward.treeLaw_vertices_card_real`, including $n=\tau$. |
| A02 | 248–249, 428–438 | Algorithm 1 defines a rooted labelled tree process; active count equals the walk before absorption; hitting zero is exactly complete freezing and the tree then remains constant. | **Substantial coverage:** actual uniform transition and iterated `Forward.treeLaw`; finite-tree/count/label/graph-distance invariants, `run_constant_of_active_empty`, `treeLaw_active_empty_iff` and `treeLaw_constant_after_extinction`. The actual fixed-schedule and iid-sign joint histories are constructed in `ForwardInfiniteHistory` and `ForwardAnnealedHistory`; absorption and full-path transport are verified. |
| A03 | 271–274 | All-positive schedules give ordinary recursive trees (with the initial vertex counted); iid symmetric signs conditioned on extinction time give the uniform plane-tree law after uniform ordering. Preserve the parity/positive-probability condition. | **Recursive example proved; finite conditioned plane law proved for the chronological plane order; uniform sibling reordering also proved:** `Forward.treeLaw_allAttachment_eq_recursive` identifies the entire actual all-positive State law with a separately specified fresh uniform-parent process on $n+1$ vertices (independent five-example/six-closure probe now run: exit zero, `verification/recursive-tree-independent-statements.log`; only two measurability side conditions of the probe were repaired, not its statements). For every success probability $p\in(0,1)$ (the source case is $p=1/2$) `ForwardAnnealed.iid_signs_conditioned_extinction_uniform_plane` proves: the actual first active-zero event $\{\tau=2m-1\}$ has positive probability $|\mathrm{FinitePlaneClass}(m)|\,(1-p)^m p^{m-1}$ (`measure_extinctionTimeIs`), and conditionally on it the terminal tree is the uniform law `finitePlaneUniform m` on all finite plane trees with exactly $m$ vertices; `..._at_time` reads the same law from the stopped tree $T_{2m-1}$. Even times have probability zero (`measure_extinctionTimeIs_even`). The proof (i) derives the exact atom mass $(1-p)^m p^{m-1}$ of the actual limit law on every finite plane tree by induction on the true vertex count from the first-step fixed point (`planeLimitLaw_atom`), (ii) proves the invariant $2|V|-|A|-1=$ elapsed steps along the genuine chain, whence $\tau=2m-1\iff$ the limit has $m$ vertices almost surely (`ae_extinctionTimeIs_iff_finiteVertexCount`), and (iii) conditions the actual limit law on the finite class (`cond_finitePlaneSet_eq_uniform`). No Catalan count and no assumed Bienaymé law are used. The conditioning event is an event of the actual chronological plane chain `PlaneForward.fullLaw` (first time the active set is empty); it coincides with $\{\tau(\mathbf X)=n\}$ because the active count is the walk $S_k(\mathbf X)$ and the signs are read off the history, an identification carried by the earlier bridge `map_fullLaw_toPlaneState` and not restated in this family. Authored probe: `verification/A03FiniteConditionedPlaneStatements.lean`, exit zero, standard axioms only. **Uniform sibling reordering also proved:** `PlaneTree.shufflePMF` reorders a finite plane tree by recursively shuffling each child subtree independently and applying one uniform permutation of the children (explicit one-level transition mass `shufflePMF_apply_eq`; independent of the plane representative of the unordered tree, `SameUnordered.shufflePMF_eq`; junk identity on infinite trees). It preserves vertex counts, is symmetric and doubly stochastic on every class (`sum_shuffleMatrix_row/column`), so `finitePlaneUniform_bind_shuffleLaw` shows the uniform law is invariant, and `iid_signs_conditioned_extinction_uniform_plane_shuffled` gives the source statement with a uniformly random plane order. Worker-authored (`verification/A03_SHUFFLE_NOTES.md`, probe `verification/A03ShuffleStatements.lean` exit zero, 14 closures), root-read statements; `SameUnordered` is not bridged to the A20 unordered quotient. S05 preserves the initial-vertex correction. |
| A04 | 342–343 | Stronger uniform ratio convergence implies `eq:assumptions`; supercritical iid signs conditioned on survival satisfy the linear assumptions almost surely with $c=2p-1$. | **Proved with an explicit existence coupling:** `uniformTailRatio_iff_maximum_tendsto` and `sourceAssumptions_of_uniformMaximum` derive both literal nested assumptions from the stronger introductory maximum. `ForwardAnnealed.exists_conditioned_iid_linear_coupling` constructs one probability space with every exact iid row conditioned on $\tau>n$, a true survivor conditioned on $\tau=\infty$, eventual equality of whole rows and both source assumptions for every prescribed positive diverging sublog cutoff. Positive survival is derived from the actual iid walk. No independence between rows or arbitrary-coupling almost sure assertion is claimed. Authored eight examples/fifteen closures; independent four/eleven, actual imported checks pass. Focused artifact PASS 3,970 jobs. |
| A05 | 338, 351, 1493–1501 | Existence and uniqueness of $f(c)>1$, endpoint $f(1)=e$, identity $g(f(c)-1)=2c/(c+1)$, and strict inequality after adding positive $\eta$. | **Proved:** `linearHeightFactor_existsUnique`, `linearHeightFactor_one`, `bennettRate_linearHeightFactor`, `bennettRate_linearHeightFactor_add` |
| A06 | 357 | Under the linear regime the rescaled metric measure trees are not Gromov–Hausdorff–Prokhorov tight, but converge in the cited distance-sampling topology to the stated long dendron. | **Partial — finite-sampling convergence and Gromov–Hausdorff non-tightness proved; GHP non-tightness, convergence in the topology of [ET21, Jan21] and the dendron identification are not Lean statements:** for every $k$ the $k\times k$ matrix of graph distances between $k$ conditionally independent uniform vertices of the same forward tree, divided by $\ln n$, converges in probability (hence in distribution) to the deterministic star matrix with off-diagonal entries $(c+1)/c$ (`LinearBush.linear_sampled_distance_matrix_tendsto_zero`, diagonal exactly $0$, coincidences included; limit `starMatrix`, `longDendronSampleLaw_dirac`). For Mathlib's `GromovHausdorff.GHSpace`: every compact $K$ has uniformly bounded packing numbers at scale $r>0$ (`exists_packingNumberLE_of_isCompact`), the actual rescaled tree has packing number $\ge k$ with probability $\to1$ for every $k$ and every $r<(c+1)/c$ (`linear_packingAtLeast_tendsto_one`), hence for every compact $K\subset\mathrm{GHSpace}$ the event $\{T_n/\ln n\in K\}$ has probability $\to0$ (`linear_scaledGH_mem_isCompact_tendsto_zero`, `linear_not_tight`, and `linear_not_isTightMeasureSet` for Mathlib's `IsTightMeasureSet`). Non-tightness for GHP follows on paper because forgetting the measure is continuous from GHP to GH; this remark is not a Lean theorem. The statement that these sampled matrices are those of Janson's long dendron $\Upsilon_{\delta_a}$, $a=(c+1)/(2c)$, is taken from the paper's parametrization, not derived from a formalization of dendrons or of the topology of [ET21, Jan21], and was not checked against [Jan21, Example 3.12] (reference text unavailable). Because the limit is deterministic, annealed convergence in probability of every $k\times k$ matrix gives convergence in distribution in the sampling topology if that topology is characterized by sampled matrices; this passage is not formalized. The hypothesis `hτ` is strict for every $n$, matching the standing source assumption at line 286. Notes `verification/A06_NOTES.md`; probe `verification/A06Statements.lean` exit zero, standard axioms only. Worker-authored, root-read statements; independently reviewed at statement level (`verification/INDEPENDENT_REVIEW_RESUMPTION_2026_10_30.md`); proofs not independently audited. |
| A07 | 311, 523, 2346 | All-positive reverse construction reduces to the stated Kingman-coalescent construction. | **Embedded jump chain proved (no holding times):** `Kingman.mergeLaw` specifies Kingman's jump independently of any forest (uniform ordered pair of distinct blocks of a set partition, merged); `mergeLaw_unordered` gives every unordered pair mass $1/\binom m2$ and `mergeLaw_ae_partition` shows partitions of a fixed set stay partitions and lose exactly one block. `ofForest_isPartitionOf` shows the component family of an actual rooted forest is a genuine partition, `joinLaw_map_blocks` shows one actual uniform ordered-root join projects exactly to one Kingman merge, and `map_blockHistory_lawAfter` shows the entire joint history (current forest and all earlier forests) of the all-positive reverse construction, forgotten to component partitions, has exactly the recorded Kingman jump-chain law from the discrete partition of the $n+1$ labels; `ae_kingmanLawAfter_partition` gives the genuine-partition and block-count invariants, so one block remains after $n$ jumps. No continuous-time holding times are claimed (the source defines none). Authored probe `verification/A07KingmanStatements.lean`, exit zero, standard axioms only; authored self-review plus an independent statement-level review (`verification/INDEPENDENT_REVIEW_RESUMPTION_2026_10_30.md`). The introduction's reversed signs and the $n$ versus $n+1$ count remain S05. |
| A08 | 530–538, 706 | Algorithm 2 is well-defined up to and including absorption; its forest at time $i$ has exactly $S_i$ components, and the final forest is one tree. | **Constructed:** `Reverse.lawAfter_valid`, `Reverse.treeLaw_isTree`, `ReverseStamped.map_lawAfter`, `ReverseHistory.map_lawAfter_current`. Actual stamped transitions and coherent graph histories project exactly to the verified marginals. |
| A09 | 532–536, 708–718 | Uniform ordered pairs have probability $1/[S_i(S_i-1)]$; freezing inserts a deterministic singleton; labels and increasing-label invariant are preserved. | **Proved:** finite pair laws, `ReverseStamped.transitionLaw_attachment_singleton`, `transitionLaw_freezing_singleton`, `treeLaw_times_valid`, `treeLaw_timestamp_order`. The edge labels are exactly the attachment times, increase away from the root, and precede adjacent frozen labels. |
| A10 | 570–572; `eq:labels` | The reverse tree's deterministic vertex labels are the disjoint union of frozen-time labels and active labels, with the asserted cardinalities. | **Proved for the constructed graph process:** `Reverse.treeLaw_vertices_and_root`, `card_frozenIndices`, `card_vertexLabels`. |
| A11 | 575–577 | Reverse birth time is $n$ for active labels and $u-1$ for frozen label $u$; graph heights and coalescence times have the stated existence/range characterizations. | **Proved:** `Reverse.mem_phaseLabels_iff_birthTime`, `RootedForest.depth_eq_dist`, `ReverseHistory.coalescenceTime_spec`, `fullLaw_coalescenceTime_lt` and `fullLaw_coalescenceTime_self`. Coalescence is the largest phase in the actual common history with both vertices present in one graph component. |
| A12 | 610–613 | Uniform birth distribution is the pushforward of counting measure on frozen labels shifted by one; event counts give the rational expression in L02. | **Counting law and terminal-tree selection proved:** `Reverse.uniformVertexLaw_eq`, `Reverse.uniform_birthTime_lt`; the displayed frozen-label shift is explicit. |
| A13 | 592–595, `eq:H0`; 1215–1228 | Independent Bernoulli representation of a vertex height, including its birth truncation; stochastic domination by the full sum; upper union bound and active-vertex lower-tail reduction. | **Corrected mathematical content proved:** `ReverseHistory.phaseIncrements_hasLaw_product`, `fullLaw_depth_eq_sum_phaseIncrements`, `Reverse.treeLaw_depth_identDistrib_bernoulli` and `ReverseHeightBounds`. Actual increments of one fixed vertex are mutually independent and telescope to its actual height. No cross-vertex independence is claimed. Parameters are attachment-masked, including absorption (S06); the printed union factor remains false (S16). |
| A14 | 658–668 | Relabelling active labels preserves graph structure; characterize the forward-tree support in increasing labelled trees. | **Partial:** `CanonicalTreeObservable` gives both actual pushforward laws, a graph isomorphism for reverse canonical coordinates, root zero, preserved edge times and frozen labels; `ForwardScheduleSupport` proves necessary schedule compatibility. `ForwardSupportCharacterization` now gives exact corrected shape support, and `construction_laws_eq` identifies the pushforwards. The original schedule-incompatible support assertion remains false. **Intrinsic union over schedules proved (Claude resumption):** `Forward.IncreasingLabelled N s` is the schedule-free increasing condition; `increasingLabelled_iff_exists_support` shows it holds exactly when the state has positive forward probability for some schedule with $N\le\tau$ (`IncreasingLabelled.exists_schedule`, `exists_mass` with the product mass). `Rooted.IsEncoding`/`Rooted.toState` encode a heap-increasing source tree with labels $1..N$ as such a state (unique, independent of sibling order), `ForwardStateDecoding*` decodes every such state back to a heap-increasing tree, and `Forward.intrinsicClassEquiv` is a bijection between `UnorderedIncreasingClass k n (Icc 1 (2n-k-1))` and the intrinsic increasing states with $k$ active and $n$ vertices; `treeLaw_ae_exists_paper_class` gives that almost every sample of the forward tree encodes a class with the schedule's deterministic parameters ($S_n=$ `activeCount x N`, $N_n=$ `plusCount x N + 1`), i.e. $\mathcal T_n\in\mathfrak T^+_{S_n,N_n}$ (`treeLaw_ae_exists_class` is the version with parameters read from the sample). The fixed-schedule support claim remains false and is not claimed. Worker-authored, root-read statements (`verification/A14_INTRINSIC_NOTES.md`, `A14_CONVERSE_NOTES.md`, probes exit zero, standard axioms); independently reviewed at statement level (`verification/INDEPENDENT_REVIEW_RESUMPTION_2026_10_30.md`); proofs not independently audited. |
| A15 | 677–682 | Unique forward history of a schedule-compatible labelled tree and product of its one-step probabilities. | **Proved on the corrected support:** `ForwardReconstruction`, `ForwardHistoryExistence`, `ForwardPointMass` and `ForwardSupportCharacterization` give unique reconstruction, explicit legal truncations, exact product mass and the shape/history/support equivalence. The printed transition class indices are not used. |
| A16 | 689–720; `eq:toshow` | Unique reverse forest history, membership and component counts, reverse probability product, and the $S_n!$ active-label fibre count. | **Partial:** `ReverseStampedReconstruction`, `ReverseStampedPointMass` and `ReverseStampedHistoryExistence` prove legal-history uniqueness, existence for actual samples, and their actual terminal probability product with factorial normalization, including absorption. `CanonicalReverseFibers` and `CanonicalReversePointMass` now identify the complete reachable fibre with a free orbit of cardinal $S_n!$ and sum its actual masses. The proof uses the corrected reachable support; reverse admissibility of every arbitrary shape in the printed class remains unchecked. **Added by the resumption (A14 bridge):** the printed class $\mathfrak T^+_{k,n}$ equals the union over schedules of the forward supports (`Forward.intrinsicClassEquiv`, `increasingLabelled_iff_exists_support`; see A14). This says nothing new about the fixed-schedule product $\frac1{S_n!}\prod 1/S_{i-1}$ and does not make the printed fixed-schedule class a support statement; it records that every printed class element is reachable for some schedule. Independently reviewed at statement level (`verification/INDEPENDENT_REVIEW_RESUMPTION_2026_10_30.md`); proofs not independently audited. |
| A17 | 718–720 | Product/factorial identity $\prod_{i\le n:X_i=1}[S_i(S_i-1)]^{-1}=(S_n!)^{-1}\prod_{i=1}^n S_{i-1}^{-1}$, including the absorbed endpoint. | **Proved:** `reverseHistoryWeight_eq_factorial_inv_mul_forward`, `factorial_mul_reverseHistoryWeight_eq_forward`. The paper's factorial induction is checked; identifying products as tree-history probabilities remains A15–A16. |
| A18 | 1173–1176 | Equality in law transfers graph height, distance, and uniform-vertex laws between the two constructions. | **Proved:** `CanonicalUniformSampling.forward_uniformHeightLaw_eq_reverse`, `CanonicalPairSampling.forwardPairDataLaw_eq_history`, `CanonicalMaximum.forward_maximum_law_eq_reverse`; actual graph distances are preserved by `CanonicalGraphDistance.reverseState_graph_dist`. The pair law retains both heights and distance jointly and includes equal samples. |
| A19 | 742–755, 862–867 | Recursive binary-tree map and inverse are well-defined, preserve increasing labels and active leaves, are mutual inverses; tangent numbers count the fully frozen binary class. | **Proved:** actual unordered P01 map/inverse, unique canonical representatives, separate edge/frozen-label preservation and exact sizes. `TreeGrowthPolynomial` and `TangentEnumeration` additionally prove the full tangent/Bernoulli enumeration C01 without an assumed counting recurrence. |
| A20 | 882–889 | Rooted labelled locally finite tree space admits a Polish metric characterized by eventual agreement of every finite truncation; corresponding plane/unlabelled variants. | **Proved on the full source ambient domain:** `UnorderedTreeTopology` gives a compatible complete separable metric on actual unordered rooted labelled locally finite trees, with exact eventual finite-ball agreement. Genuine rooted labelled graph isomorphisms, repeated labels and all coherent towers are covered; plane/unlabelled variants are proved. `ChronologicalAmbientEmbedding` and `ChronologicalAmbientLaws` now prove the actual chronological model has a closed embedded image, with same-radius ball equivalence and faithful pathwise/weak-law transport. `MainLocalAmbient` exports T01/T02 in the full ambient. Independent audits: broad topology ten examples/ten closures; actual model bridge six/seven. No support premise is added. |
| A21 | 893–899; `eq:sumP` | Local convergence of the growing process is equivalent to finite eventual degrees; survival implies attachment density at least one half and divergence of the attachment reciprocal sum. | **Proved:** `ForwardDegreeLocalCriterion.exists_local_limit_iff_all_degrees_stabilize` (namespace `ForwardInfiniteHistory`) proves the deterministic equivalence on every valid legal-or-held trajectory, including the root and absorption, without assuming freezing. `AttachmentDensity` proves the literal density and post-step sum divergence; `AttachmentReciprocalSeries` transfers divergence to the true hazards. The divergence proof uses the verified height-scale lower bound instead of the displayed density-to-harmonic argument. |
| A22 | 895–906 | Eventual freezing implies finite degrees; conditional infinitely many attachments for a never-frozen vertex; survival product and reciprocal divergence criterion. | **Corrected result and source strategy proved:** `ForwardAttachmentPatterns` derives joint finite selection patterns and survival from the actual kernels. `ForwardConditionalAttachments` proves genuine conditional independence with parameters $1/S_{i-1}$ for $i$ strictly after birth, then applies second Borel–Cantelli. `ForwardFreezingDegrees.fullLaw_local_limit_iff_all_eventually_frozen_all_schedules` proves the simultaneous equivalence, including null survival events, the root, and finite extinction. Existing lifetime modules supply the corrected product/printed-series criterion. Printed selection/product formulas remain false (S04), with actual finite/infinite counterexamples in `ForwardSelectionSourceChecks`. |
| A23 | 908–910 | A fully frozen finite truncation is determined by finitely many schedule entries; transfer to pointwise eventually equal schedules. | **Proved:** `ForwardLocalStability`, `ForwardSchedulePrefix` and `ForwardDiagonalBalls` construct a genuine coupling, show equality of frozen balls at every later pair of horizons, and bound the discrepancy of every ball event by the true nonfreezing probability. `ForwardDiagonalLocalLimit` transfers to the same weak limit. |
| A24 | 912–921 | Coupling an increasing subsequence of matching prefixes transfers positive-probability diverging degrees and rules out local distributional convergence. | **All-vertex obstruction proved in the full source ambient:** `ForwardDegreeCoupling` constructs the strictly increasing matching-prefix extraction and actual full-history pair couplings. `ForwardDegreeDivergence`, `LocalBallTightness` and `MainLocalDegreeNecessity` give positive marginal tails and the contradiction to weak convergence, without the freezing-series theorem. `MainLocalAmbientDegreeNecessity` transports this to arbitrary full-ambient weak limits using proved closedness. The final proof uses marginal tails; no single common coupling or the printed nonmonotone diagonal union inference is asserted. Independent core audit: nine examples/twelve permitted closures, with separate authored four/eight. |
| A25 | 927–948 | Ulam–Harris plane trees, descendant subtrees, local finiteness, and existence/uniqueness of the branching law from the root-offspring and independent-subtree characterization. | **Proved:** `PlaneTree`, geometry/topology, iid `bienaymeLaw`, `isBienayme_bienaymeLaw`, `IsBienayme.unique`, and `eq_bienaymeLaw`. |
| A26 | 959 | Geometric tail recurrence $\Pr(K\ge j)=p\Pr(K\ge j-1)$ and mass $(1-p)p^k$. | **Proved:** `FirstChildStructure.degree_tail_recurrence_of_fixedPoint` and `degree_measure_of_fixedPoint` for an arbitrary first-child fixed-point law, with actual `planeLimitLaw_offspring_tail_recurrence`, `planeLimitLaw_offspring_tail` and `planeLimitLaw_offspring_mass`. The literal predecessor-index recurrence, including $p=0$, is checked in `GeometricOffspringTailStatements.lean`; four standard axiom closures pass. |
| A27 | 961–969 | Inductive factorization of conditional subtree expectations establishes the branching property in L05. | **Mathematical expectation identities proved:** `FirstChildConditionalIntegrals`, `FirstChildInductionIntegrals` and `FirstChildSourceInduction` prove arbitrary nonnegative measurable products, the literal $g_n$, its normalization and all three source expectation identities from the genuine conditional split. Actual plane-tree/limit-law specializations and the null single-leaf branch are checked. Derivation uses the proved joint law/rectangle induction rather than the printed proof order. Independent review: `verification/A27_SUBTREE_INTEGRAL_INDEPENDENT_AUDIT.md`, five expanded examples/thirteen permitted closures; separate implementing self-review is retained. |
| A28 | 973–979 | Unique increasing relabelling to consecutive labels; almost sure extinction for $p\le1/2$, and local convergence on nonextinction for $p>1/2$. | **Proved:** `IncreasingRelabelling.existsUnique_paper_consecutive_relabelling` (namespace `BinaryBijection`) constructs the unique actual unordered representative using the unique finite order isomorphism, with literal per-incidence relabelling and preserved rooted skeleton/active marks. `ForwardAnnealed.iid_extinction_of_le_half` gives raw infinite-product extinction including criticality. The strong-law drift, freezing density and `iid_nonextinction_local_criterion` check the source T01 route on nonextinction; `iid_schedules_local_converge` handles every $p<1$. No conditional independence after conditioning on survival is assumed. |
| A29 | 982–1011 | First-child decomposition, its Markov transition kernel, harmonic-product eventual selection, joint independent embedded limits, and continuity of ordering then erasing labels. | **T02 dependencies proved:** chronological projection and full-history law transport, exact first-child graft kernel, global raw-state fairness, extracted product law and actual joint limit, and continuous ordering/erasure. The labelled consecutive-reindexing argument remains with A28; the source conditional infinite-product shortcut is bypassed. |
| A30 | 1140–1146 | Embedded-coordinate times with the repeat-last-time convention are well-defined and reflect absorbed chains correctly. | **Proved:** `nextCandidate_exists`, `nextTime_spec`, exact selected times and fallback, `coordinate_eq_extracted_tail`, and `tendsto_coordinate_of_extracted`, including finitely selected/absorbed coordinates. |
| A31 | 1146–1161 | Finite-dimensional product-law induction for interleaved chains; extension to path-law equality. | **Source scalar identities proved:** `InterleavedSourceFirstSelectionLaw` proves the literal first-selected-value law even without fairness, retaining never-selected mass. `InterleavedSourceFactorization` proves both coordinate recurrences, restarted first-selection scalar factors and both absorbing two-term identities, including empty/null prefixes and strict next times. Independent audit: three examples/seven closures; authored six/thirteen. The existing harmonic-cylinder proof establishes the product law first; the source double-induction order and a full asynchronous Markov restart are not certified. |
| A32 | 1240–1242 | Swapping adjacent $-1,+1$ to $+1,-1$ decreases $h_n^+$; iterate to sorted increments; compare the harmonic sum with $\log((P_n+1)/2)\ge\log(n/4)$. | **Proved by the source strategy:** `HeightScaleAdjacentSwap` checks the actual transposition, exact height difference, positivity and counts. `HeightScaleSorting` constructs a finite chain terminating at the literal all-attachments-first prefix, preserves the original tail, proves the exact harmonic identity and every displayed logarithmic inequality. The bounded integer area increases at each swap; an attained maximum proves termination. Independent audit: `verification/A32_ADJACENT_SWAP_AUDIT.md`, nine reconstructed examples/ten allowed closures. |
| A33 | 1250–1258 | Uniform active-vertex Bernoulli law, two-sided concentration, and divergence of $h_n^+$ imply convergence in probability. | **Proved by the source strategy:** `uniformActiveHeightLaw_eq_bernoulli_array` gives the actual forward uniform-active law as the unmasked independent Bernoulli product with parameters $1/S_i$, masked only in the sum. `UniformActiveBennett` proves both exact $g(u)$ tail bounds and their limit for admissible varying schedules. `UniformActiveMoments` also proves uniform real moments and all finite source $L^p$ limits from this law. Scoped independent audit: `verification/A33_ACTIVE_HEIGHT_AUDIT.md`. |
| A34 | 1258–1270 | Tail-integral formula for every real $p\ge1$, $g(u)\ge u$ for $u\ge7$, exponential-tail integral estimate and uniform moment control. | **Proved, with a recorded analytic departure:** `ActiveHeightTailIntegral` proves the actual real layer-cake identity and integrability, literal split at 7, uniform moments and the source-method real-$p$ limit. `ExponentialMomentTail` proves $e^2-1\le7$, exact dilation, the explicit $2\,7^{p-1}e^{-7m}/m$ bound and the claimed big-O estimate for all real $p\ge1$. A logarithmic envelope replaces repeated integration by parts; that printed proof route is not certified. Independent audit: `verification/A34_INDEPENDENT_AUDIT.md`, five reconstructed examples/eight allowed closures. |
| A35 | 1272–1278 | Positive rate $g(C-1)$, $g(e-1+\varepsilon)>1$, and L07 imply the universal height window. | **Conclusion proved:** `maximum_height_window_tendsto_one`; the actual forward bounds use the documented one-edge shift and $n+1$ factor. The source's finite P03 upper bound is refuted separately. |
| A36 | 1279–1285 | Under $\log n=o(h_n^+)$, uniform exponential upper tails imply all required moment convergence. | **Proved by the source strategy with finite corrections retained:** `eventually_maximum_uniform_bennett_upper` has one sufficiently large rank for every real $C\ge2$ and the exact half-rate exponent. `TailIntegralSeven` and `MaximumTailMoments` prove the actual uniform real moments and `maximum_height_tendsto_Lp_via_tail_integral`, using the source tail method and finite-height integrability. The false finite P03 bound is replaced by a derived bound retaining $\log(n+1)+\log C$, absorbed uniformly. Independent review in `verification/A36_MAXIMUM_TAIL_INDEPENDENT_AUDIT.md` passes eight expanded examples/ten permitted closures, including finite initial rows. The separate implementing review/probe is retained with its own provenance. |
| A37 | 1322–1337; `EqProp9` | Geometric-block partition, interval attachment/freezing count identities, and uniform count error bounds from $\vert S_i/i-c\vert \le\eta_n(\varepsilon)$. | **Corrected geometric strategy proved:** `IntervalFreezingCounts` proves both literal plus/minus count identities; EqProp9 is proved. `GeometricHeightBlocks` proves the exact integer partition and block-count bounds with $1<\beta<C$, allowing empty individual blocks. The unrestricted printed partition is formally refuted. Independent audit: `verification/A37_A38_GEOMETRIC_INDEPENDENT_AUDIT.md`; see S15. |
| A38 | 1338–1378 | Uniform upper/lower block estimates $U_n,L_n$, boundary-block errors, normalization by $\log(b/a)$, and passage through $n\to\infty$, $\varepsilon\to0$, $\beta\downarrow1$. | **Corrected source geometric strategy proved:** `GeometricHeightBlockBounds`, `GeometricHeightWindowBounds`, `GeometricHeightEnvelopes` and `GeometricHeightUniform` prove the actual printed complete-block $U_n,L_n$, corrected partial-block errors, actual-source-error eventual positivity, uniform normalization and the original finite-maximum/nested-limit conclusion. The last endpoint retains a vanishing $1/A_n$ rounding term and the correct denominator. No block estimate or partition is an extra premise. The earlier Abel proof remains available. Independent probe: five expanded examples/ten permitted closures; three false printed finite steps are retained as proved counterexamples (S15). |
| A39 | 1381–1395; `cv hn cas lineaire` | Integer cutoff enlargement $A'_n$, negligible early contribution, logarithmic bulk, bounded late contribution, and their combination. | **Proved:** `HeightScaleBounds`, `LinearRegimeCutoffs`, `MainLinearHeightScale` use $A'_n=\lceil A_n\rceil$ and $b_n=\lfloor\varepsilon n\rfloor$, exact splitting, and the bulk lower constant depending on $\varepsilon$. |
| A40 | 1402–1411; `eq:Hvn` | Random birth-truncated Bernoulli representation with independent driving variables and its conditional mean $M_n$; $0\le M_n\le h_n^+$. | **Proved:** `UniformBirth.actualBirthHeightLaw_eq_auxiliary`, `auxiliary_coordinates_independent`, `auxiliary_birth_indep_array`, `randomMean_condExp`, `randomMean_eq_heightScale_birth` and `randomMean_bounds`. The actual joint reverse birth/height law equals the explicit independent unmasked Bernoulli product pushforward. Conditioning is on the genuine birth sigma-algebra. For positive horizons `randomMean_ge_half` supplies $M_n\ge1/2$; the zero row is retained. Independent audit and nine permitted axiom closures pass in `verification/UNIFORM_BIRTH_REPRESENTATION_AUDIT.md`. |
| A41 | 1415–1429 | Uniform positive late-time count, high-probability birth beyond $A_n$, logarithmic birth-tail bound, and $M_n/h_n^+\to1$ in probability and all $L^p$. | **Corrected content proved:** `UniformBirthTail`, `UniformBirthLogTail`, `UniformBirthMeanLimit` and `UniformBirthHarmonicTail` give exact rounded CDFs, negligible early births, the literal logarithmic birth-tail limit, all-real-power mean normalization, and the displayed harmonic upper bound for the true strict post-birth complement. `eventual_mean_tail_normalized_le_log` derives the bound uniformly from the source assumptions. The limit proof itself uses a stronger bulk-only fixed-fraction cutoff route; the paper harmonic calculation is now checked separately after the explicit S21 correction. The literal inclusive equality/intermediate sum inequality remain false. |
| A42 | 1430–1445 | Conditional moment bound for $Z_n/M_n$ and convergence; deduce $(Z_n-M_n)/h_n^+\to0$ in all $L^p$. | **Proved by the source strategy:** `UniformBirthConditionalMoments` gives genuine conditional expectation, non-strict layer-cake identity and the exact $g(u)$ Bennett bound. `BennettMomentIntegral`, `UniformBirthMeanEscape` and `UniformBirthRealBennettIntegral` prove finiteness, domination and convergence of the actual expected tail integral; rare small means are controlled by the proved $M_n\ge1/2$ on positive rows. `UniformBirthMomentConclusions` proves the literal real moment limits, centered-error inequality and $Z_n/h_n^+\to1$ for all source real powers. The zero-mean initial row is retained; no convergence or conditional-law estimate is assumed. |
| A43 | 1446 | Combine T04.I and A41–A42 to obtain the uniform-vertex height limit. | **Source proof now checked:** `UniformBirth.linear_uniform_height_via_random_mean` combines the proved random-mean normalization, T04.I scale limit and actual joint reverse birth/height law, then transports to the genuine forward conditional uniform-height law. Its exact original source assumptions and every real $p\ge1$ are retained. The earlier direct forward-mixture proof remains available as an alternative. |
| A44 | 1458–1479 | Conditional coalescence hazard bound, summation above $\varepsilon n$, and uniform $O(1/n)$ estimate. | **Proved with corrected averaging:** `CoalescenceBounds`, `UniformCoalescence`, `CoalescenceLimits`; the diagonal contributes at most $1/N_n\le2/n$, all labels are included, and the off-diagonal hazard sum gives the uniform $O(1/n)$ estimate. |
| A45 | 1482 | Derive uniform-pair distance using the most recent common ancestor, its negligible normalized height, and moment bounds. | **Proved with an explicit repair:** `uniform_coalescence_div_log_tendsto_zero` now supplies the stronger estimate missing from the text, using $A_n\to\infty$ and $A_n=o(\log n)$. The actual common-history geometry `ReverseHistory.fullLaw_dist_depth_bounds` and `fullLaw_distance_defect_bounds`, together with the exact forward joint-law transfer, are now proved. `linear_uniform_distance_deviation_tendsto_zero` and `linear_uniform_distance_tendsto_Lp` finish the probability and all-real-power conclusions. |
| A46 | 1492–1507 | Positive slack in the Bennett exponent yields the sharp linear-regime height upper bound. | **Proved:** `linear_maximum_upper_tendsto_zero`; the source's rate-slack strategy is checked, using the corrected actual forward bound with the explicit one-edge shift and $n+1$ factor. |
| A47 | 1509–1512, 1648–1659 | Telescoping height over chains; cut-forest construction, unique marked root per component, exchangeability, independence from the past, uniform matching reconstruction, and height-increment characterization. | **Corrected construction proved:** the actual cut geometry and ancestor-height identity are checked. `ForwardForestSlots` proves full anonymously slotted forest/past-tree product law and root exchangeability. `ForwardForestRootOrbit`, `ForwardForestRootMatchingEquiv` and `ForwardForestUniformMatching` prove actual independent uniform-bijection reconstruction of the complete terminal state, retaining root freezing clocks. The printed bare star forest loses those clocks and cannot reconstruct the full labelled state by matching alone; `ForwardForestStarConvention` formally witnesses the loss. The entire bare forest is also proved independent of the past (`ForwardForestStarOrbit`), and its joint matching law retains hidden root clocks in the independent driving data. Independent review: `verification/FULL_FOREST_INDEPENDENT_AUDIT.md`, six reconstructed examples/seven permitted closures. Conditional observable formulas remain in A51/A52; see S08/S17. |
| A48 | 1661–1666, 1678, 1693–1696 | Tall-active-vertex count $N_k^n$, maximum component active size $M_k^n$, and cumulative-good count $\overline N_k^n$ are well-defined measurable quantities with the claimed meanings. | **Proved with exact finite source indices:** actual tall count, bare all-star component maximum and cumulative-good count are measurable and characterized. `ForwardTerminalGoodPredicate` reads historical activity and all block heights from one terminal state. `GeometricChainPositiveCutoff` proves the literal positive-index filter with $\max(1,\lceil\log A_n/\log C\rceil)$, including $A_n\le1$, and eventual agreement with the earlier cutoff. The marked-root correction is retained. Independent source-geometry audit/probe: three expanded examples/eight permitted closures. |
| A49 | 1698–1713; `eq:proba` | Existence of a good vertex at the final scale produces an ancestor chain and the displayed asymptotic logarithmic lower bound. | **Graph-chain and asymptotic conclusion proved:** `ForwardGoodGraphAncestorChain` and the exact positive-cutoff wrapper construct one actual historical ancestor chain from every good endpoint, with parent iterates, ordinary graph distances above threshold and the deterministic height lower bound. Exact rounded span asymptotics and the corrected actual good-chain survival theorem supply the logarithmic conclusion. Independent review: `verification/FOREST_SOURCE_GEOMETRY_INDEPENDENT_AUDIT.md`. The corrected base convention remains explicit under A50. |
| A50 | 1715–1732; `eq:Nbar` | Uniform one-step failure $O(k^{-2})$ plus initial-scale control imply survival of a good chain with high probability. | **Proved for the actual good sets, with corrected base:** `linear_conditional_goodChain_failure_bound` proves the normalized conditional $\Delta/k^2$ bound under the literal limsup/liminf assumptions; null conditioning gives zero. `Forward.goodChain_survival` and `LinearGoodChainBase` prove survival with initial threshold $\rho2^k$, $\rho=c/4$. The printed base at threshold $2^k$ is not assumed. |
| A51 | 1735–1751; `14/07/21h`, `14/07/19h` | Past/forest independence, failure decomposition, and conditional expectation $\mathbb E[\overline N_{k+1}\mid\text{past,forest}]=\overline N_kN_k/S_{C^k}$. | **Proved for the complete actual bare forest:** full independence and the genuine $N,M$ observables are checked; `ForwardConditionalGoodChain` supplies the failure decomposition. `ForwardForestConditionalChainMean.condExp_goodSet_succ_given_forest` (namespace `Forward`) is the literal actual conditional expectation with true $S_{C^k}$, including all supported boundary cases. Actual rematching invariance, finite averaging, good-set inheritance and integrability are proved inputs. Independent source review: `verification/FOREST_CONDITIONAL_MOMENT_INDEPENDENT_AUDIT.md`. |
| A52 | 1753–1769; `14/07/19hb` | Conditional negative correlation for different matched components and variance bound $\operatorname{Var}(\overline N_{k+1}\mid\cdot)\le M_k\mathbb E[\overline N_{k+1}\mid\cdot]$. | **Actual covariance and variance proved:** `ForwardForestConditionalChainCovariance.goodVertices_conditionally_negatively_correlated` proves conditional negative correlation in distinct actual components, given the whole past tree and complete bare forest. Old marked roots and later vertices are treated explicitly. `ForwardForestChainComponentMarks` proves the common inherited mark and same-component explanation. `ForwardForestConditionalChainVariance.condVar_goodSet_succ_given_forest` proves the literal variance bound. Finite permutation moments discharge actual support and integrability; variance algebra uses centered moments rather than a literal double covariance expansion. Independent audits/probes cover mean/variance (three/nine) and source geometry/covariance (three/eight). |
| A53 | 1770–1788 | Conditional Chebyshev estimate and $k^3/2^k=O(k^{-2})$ prove the one-step chaining estimate. | **Corrected actual source route proved:** `ForwardForestConditionalChebyshev`, `ForwardForestConditionalGrowth` and `MainConditionalGoodChainForest` use full-forest conditional mean/variance, conditional Chebyshev, observed-event tower integration and actual independence to prove the normalized one-step bound and uniform source window with exact positive indices. The true $S_a\le a+1$ gives the sufficient error $3k^3/2^k$ for large cuts. Independent final audit: two expanded examples/seven permitted closures; authored three/seven. False printed population/base steps remain explicit. |
| A54 | 1805–1819; `13/06/7h` | Positive large-deviation slack, existence of a sufficiently large integer $C$, Bernoulli block-height law, and uniform mean convergence. | **Corrected rate slack and actual-law conclusions proved:** existing block-law and first-moment modules give the actual independent Bernoulli representation, uniform mean and forward transfer. `PoissonSourcePolynomialScale.linear_source_rate_slack` derives the printed positive slack when $1<f(c)-\eta$; an explicit safe threshold in $(1,f(c))$ handles every positive margin without weakening the original tail event. The literal claim that the printed slack is positive for every $\eta\in(0,1)$ is formally refuted (S23), not certified by that repair. |
| A55 | 1820–1833; `eq:cvPC` | Uniform total-variation Poisson approximation and convergence of strict block-height tail probabilities. | **Partial:** `bernoulliPartialSumLaw_poisson_parameter_event` proves the actual event error $\sum p_i^2+|\sum p_i-\lambda|$; the stronger bounded-test estimate is also proved, with total variation normalized to $[0,1]$. Exact block parameters and their square-sum bound are checked. The uniform source-regime estimate and actual random-root reverse transfer are proved in `LinearBlockLowerTail` and `MainLinearBlockCount`; forward identification is now proved via the timestamp-preserving cut-forest law. |
| A56 | 1835–1853; `eq:bornePC` | Factorial bound, quantitative Poisson lower tail, choice of $C$ making $P(C)\ge6/(cC)$, and first-moment lower bound. | **Corrected quantitative route proved:** `PoissonSourcePolynomialBound.poisson_strict_tail_cubic_lower` gives the exact printed cubic tail lower bound for every real $\lambda>2,t>1$, including integral and small thresholds. `PoissonSourcePolynomialScale` proves the $\log(C)^{-4}$ scale and actual $P(C)\ge6/(cC)$ choice, with a supplied large-$C$ rounding constraint. The exact printed exponent is retained for $1<f(c)-\eta$; a visible safe exponent supplies all other margins. The printed ceiling singleton and real factorial derivation remain refuted (S10/S22), as does the all-margin slack (S23). Independent ten-example/fifteen-closure audit passes. Actual forward first-moment conclusions were already proved. |
| A57 | 1856–1867; `eq:c0` | Uniform eventual linear lower and upper walk bounds. | **False for all $1\le i\le n$ as printed**; `eventually_linear_lower_above_cutoff` proves the positive uniform lower bound on the repaired domain $A_n\le i\le n$. The all-positive upper bound follows from the existing walk count identities; the erroneous small-index claim remains refuted (S12). |
| A58 | 1873–1888; `eq:var`, `eq:esp` | A uniform $O(C^k)$ variance/second-moment error plus L12 implies the required lower-tail bound for $N_k^n$. | **Proved:** `probability_below_four_le_of_mean_variance` and `linear_forward_geometricBlock_fewTallRoots_probability`; the non-strict event and uniform constants are preserved. |
| A59 | 1892–1909; `ligne`, `eq:majoration ligne1` | Pairwise height law, split according to coalescence, and uniform $O(C^{-k})$ coalescence probability. | **Proved on the actual reverse history:** `Reverse.blockLaw_separated_pair_tail_le`, `blockLaw_coalesced_integral_le`, and their coherent-history continuation. The conditional coalescence error is the genuine sum of hazards, uniformly in the starting forest and distinct roots. |
| A60 | 1911–1943; `eq:ksi` | Coupling of two height increment sequences with independent Bernoulli $\xi_i$ of parameter $1/(S_i-1)$ and the pair-tail product bound. | **Proved by the source auxiliary coupling:** `BernoulliPairCoupling.actual_separated_tail_le_enlarged_square` and `uniform_geometric_actual_pair_tail` follow from the genuine complete-history augmentation and full independent Bernoulli driver words. Every actual increment is aligned, including current merges via the before-step same-root state. The final product uses two true marginal tails. Independent audit: twelve examples/twenty permitted closures. The false current-merge prose remains S24. |
| A61 | 1944–1977 | Monotone Bernoulli coupling, tail-probability error bounded by $\sum1/[S_i(S_i-1)]=O(C^{-k})$, and covariance estimate. | **Proved by independent monotone thinning:** the complete probability space carries actual history, independent driver words and fresh retention coins. The thinned word has the original product law and is independent of the first driver. Exact mismatch expectation is the source reciprocal sum, bounded uniformly by $O(C^{-k})$; `BernoulliPairCouplingError`/`Conclusions` discharge the actual product-tail/covariance errors. The older supersolution route is not used in this source proof. |
| A62 | 1980–1994 | Sum diagonal/off-diagonal pair bounds to obtain $\mathbb E N_k^2=(\mathbb E N_k)^2+O(C^k)$ and the variance estimate. | **Proved for the actual reverse count:** `ReverseHistory.variance_blockTallRootCount_le`, `uniform_geometricBlock_variance_le`; diagonal and distinct-root terms are summed with their actual random-root probabilities. The exact cut-count law now also transfers this result to the forward source count. |
| A63 | 2011–2015 | Extend the finite schedule by positive steps, identify component active counts with the urn, and bound $\delta_k^n$, $\varepsilon_k^n$, and $1/S_{C^k}$ by $O(C^{-k})$. | **Proved for actual whole component paths:** `ForwardPositiveExtension` preserves the complete original prefix law. `ForwardComponentUrnPathInfinite` disintegrates the actual infinite history given its full past and identifies every finite joint component record with the urn path law. `ForwardComponentUrnPathPositive` derives these path laws almost surely for the original positive extension; they are conclusions, not assumptions. `ForwardComponentUrnPathMaximal` gives the actual infinite-component maximal bound with true budgets and marked-root $+1$. Uniform source-window bounds are proved. Joint-path authored audit: eight examples/thirteen closures; separate root independent audit: three/seven. Earlier endpoint audit: ten/sixteen. The weaker arbitrary-process L13 premise remains separate under S11. |
| A64 | 2016–2019 | Individual component tail $2e^{-k^2/O(1)}$, union over $O(C^k)$ components, and uniform $k^{-2}$ bound. | **Source infinite-urn strategy proved with the marked-root correction:** `SourceUrnComponentTailScalar`, `SourceUrnComponentTail` and `SourceUrnComponentMaximum` derive the quadratic exponential rate from the actual infinite maximal urn bound, absorb the cubic marked-root threshold, union over exactly the actual cut roots, mix over the genuine earlier tree, and prove the uniform original-window $k^{-2}$ conclusion. No finite-MGF bound or component independence is assumed/called. Independent audit: three examples/eight closures; authored eight/twelve. The earlier stronger finite estimate remains available. |
| A65 | 2026–2037 | Independent exponential infectious periods and Poisson contacts induce the displayed embedded SIR Markov transitions and absorbing states. | **Both rate branches proved:** `SIRPoissonFullContactLaw` gives entire actual positive-rate next-point tree/count laws from supplied independent recovery/Poisson paths. `PoissonContactOptional` proves that zero Poisson counting marginals force genuinely empty paths; `SIRPhysicalZeroRate` proves the actual whole tree/count laws, positive exponential recovery time and holding after event one. Absence is represented by no contact point, with no artificial delay. `SIROptionalContactCompatibility` identifies the optional protocol with the positive-path protocol when paths are injected, and `SIRPhysicalOptionalRate` transfers positive source data. Independent positive-history and zero-branch audits pass. |
| A66 | 2039–2046 | Equality in law of the whole infection-tree process and attachment/freezing process driven by infectious-count increments. | **Proved:** `SIRForwardPrefixBridge` transports actual one-step kernels to complete original fixed-word forward histories. `treeFullLaw_countsPrefix_original_treePrefix_word_mixture` keeps every count and every tree jointly under the actual adaptive word law, at arbitrary horizons with absorption. `PoissonSIRData.countsPrefix_original_treePrefix_word_mixture` supplies the positive physical branch; `zeroRate_physical_original_treePrefix_word_mixture` supplies zero rate. The same count prefix determines stopping; no process identity is inferred from endpoint marginals. Independent source/type and count-selected stopping probes pass. |
| A67 | 2059–2068 | Uniform early infection-probability sandwich and finite-prefix coupling to the limiting random walk. | **Embedded finite-prefix content proved:** exact susceptible bounds, uniform early infection-probability sandwich and actual adaptive finite-word convergence in `SIRProbability`, `SIRSignWords`, `SIRTreeWordMixture`. The proof handles stopping without comparing an absorbed chain to an unstopped walk; the source walk coupling is bypassed. |
| A68 | 2070 | Skorokhod coupling, local-limit transfer also at finite extinction, and geometric-tree identification. | **Conclusion proved for embedded and physical models:** genuine finite-prefix laws, frozen balls and finite extinction give the geometric terminal weak limit in `MainSIRLocalLimit`; `SIRPhysicalLimits` transfers it to the actual full-contact protocol. Skorokhod representation is a bypassed proof method. |
| A69 | 2072 | Strong-infection finite prefixes approach all-positive schedules; subsequence compactness contradicts the local convergence criterion. | **Embedded conclusion proved:** actual finite prefixes approach the all-attachment tree; `terminal_bounded_degree_tendsto_zero` and `embeddedTerminalTreeLaw_not_tight` give degree escape and non-tightness directly. The source subsequence/Skorokhod route is bypassed. |
| A70 | 2087, 2118–2121; `eq fonction de Lambert` | Existence/uniqueness of $g_\lambda$, Lambert-$W$ expression, derivative identity on its proper domain, smoothness, monotonic decrease, convexity, and limit zero. | **Positive-profile content proved:** `SIRFluidProfile` supplies initial value, ODE, smoothness, strict decrease/convexity, limit zero and uniqueness among positive solutions on nonnegative times. `SIRLambertW` constructs the full principal branch, endpoints, inverse and derivative on its proper domain, and proves the explicit formula for the same profile. Uniqueness outside the positive-solution class is not asserted. |
| A71 | 2131–2143; `limite fluide H`, `limite fluide I tilde` | Unstopped chain construction, identity $\widetilde I_k=2(n-\widetilde U_k)-k+1$, susceptible fluid limit, and infectious fluid-limit deduction. | **Proved for embedded paths and transferred to the physical protocol:** actual unstopped susceptible/integer infectious paths, exact identity, compact-uniform auxiliary fluid limits, stopped/unstopped agreement through first extinction and shared-survival weak path mixture in `MainSIRFluid`. `SIRPhysicalLimits` supplies actual physical identification. |
| A72 | 2144 | Concavity, initial positive growth, eventual negativity, and unique positive zero of $2-2g_\lambda(t)-t$ for $\lambda>1$. | **Proved:** `infectiousProfile_strictConcave`, `infectiousProfile_deriv_zero`, `fluidExtinctionTime_spec`, `infectiousProfile_pos_before` and `infectiousProfile_neg_after` give strict concavity and the unique positive zero in $(0,2)$ for $\lambda>1$. |
| A73 | 2144–2159; `eq couplage marches` | Early transition sandwich, upper/lower random-walk couplings, and extinction-probability limit identifying the common survival mixture. | **Probability conclusion proved:** `SIREarlyExtinction` gives the actual two-stage early extinction/survival probabilities. `SIRIidCountProjection` and `SIRBiasedWalkExtinction` prove the fixed-prefix walk projection and exact absorbed-walk extinction limit. `PlaneFiniteExtinction` identifies survival of the concrete geometric Bienaymé tree. A true-kernel exponential bound replaces the printed walk coupling; its literal probabilities/indexing and negative-integer wording are not certified. |
| A74 | 2162–2176; `hypothèse Gronwall stochastique` | Stochastic Grönwall/Doob criterion for uniform fluid convergence, with all initial and drift assumptions made explicit. | **Printed criterion false (S18):** `SIRSourceChecks.printed_global_max_criterion_counterexample`. Corrected adapted discrete Grönwall and its true stochastic inputs are proved in `SIRFluidApproximation` and `SIRSusceptibleConcentration`. Exponential-moment/finite-union bounds replace the source Doob argument. |
| A75 | 2178–2196 | Conditional drift computation and uniform second-order Taylor remainder. | **Corrected content proved:** `SIRSusceptibleLaw.transition_drift`, `SIRFluidApproximation` Euler step/remainder bounds and `normalized_path_fluid_bound` retain the $\lvert n\lambda_n-\lambda\rvert$ error. The source equality substituting $\lambda/n$ for $\lambda_n$ remains false (S13). |
| A76 | 2197 | $x/(1+x)$ is $1$-Lipschitz on nonnegative reals, bounded jump second moments, and verification of the corrected fluid criterion. | **Proved for the actual unstopped fluid argument:** `infectionFraction_abs_sub_le`, bounded centered increments, actual MGF estimates, uniform noise convergence, and `SIRSusceptibleFluid` verify a corrected criterion. The false printed future-maximum criterion is not certified. |
| A77 | 2199–2203 | Terminal uniform vertices are captured by pre-extinction truncations with high probability; transfer of uniform height/distance laws and survival conditioning. | **All retained capture obligations proved:** `source_same_epsilon_reverse_birth_capture`, `source_same_epsilon_two_reverse_births` and `source_same_epsilon_two_uniform_captures` retain the literal rate ratio and the same $\varepsilon$ in cutoff and error, for every $0<\varepsilon<t_0$. The actual unconditional count estimate supplies its survival weight, terminal denominator and deadline errors internally; it does not assume a surviving-branch capture estimate. The full observed reverse-birth law uses actual forward terminal vertices and their freezing-label-minus-one clock. Native `treeFullLaw` prefix-membership capture and two conditionally independent uniform samples are also proved. Reverse and chronological clocks are compared, not equated. Independent audit seven examples/fifteen closures; authored eight/thirty-one. Focused actual artifacts end at 4,114 jobs. |
| A78 | 2204–2221; `eq demarrage I`, `eq demarrage I tilde`, `eq:gbound` | Uniform early slope $(\lambda-1)/(\lambda+1)$ from logarithmic cutoffs, ODE expansion, random-walk law of large numbers, and linear-regime hypotheses. | **Startup and stochastic T04 application proved:** `SIRStartup` and `SIRStartupQuantitative` give literal log-log and same-$\varepsilon$ inputs. Finite near-origin/bulk constraint uniformization supplies the actual adaptive random-environment T04 application and the terminal mixtures. The printed Skorokhod/random-walk LLN route is bypassed; independent iid extinction/drift assertions remain under A28. |
| A79 | 2223–2233; `limite fluide jusqu'au temps 1` | Strong-infection early uniform slope and path limit up to time one, including vanishing probability of early absorption. | **Embedded content proved:** quantitative true-kernel early extinction bounds, uniform absolute path limit and relative slope estimates down to the literal $\log\log n$ cutoff in `SIRStartup`, including the extension through time $n$. No survival or iid coupling is assumed. The printed random-walk coupling is bypassed. |
| A80 | 2235–2239 | Remaining susceptible count is $o(n)$; at most $o(n)$ later attachment steps; declining fluid limit on $[1,2]$. | **Embedded conclusion proved:** `SIRStrongCounts` proves deterministic whole-grid triangle control from the early susceptible count, genuine expectation bounds, and the uniform declining profile on $[1,2]$ as part of the full $[0,2]$ theorem. The printed walk-coupling route is bypassed. |
| A81 | 2241–2245; `eq lgn infection cas recursif` | Uniform slope down to $\log\log n$ and application of T04.II to pre-extinction truncations with $c=1$. | **Embedded conclusion proved:** relative slope, deterministic T04 uniformization under the actual adaptive word law, time-$n$ observations and terminal uniform sampling are all proved. A diagonal good-profile argument replaces the source Skorokhod route. |
| A82 | 2247–2256 | T04.III gives height $e\log n$ at time $n$; the post-$n$ reciprocal attachment sum represents the remaining height contribution. | **Embedded content proved:** `sir_time_n_maximum_tendsto` and the exact feasible-word pre-extinction reciprocal/actual-charge comparison are proved. The geometric comparison bounds terminal height between its time-$n$ truncated maximum and that maximum plus the cut maximum. |
| A83 | 2259–2273; `eq convergence des transitions cas presque recursif` | Late infection probability vanishes uniformly, by monotonicity, coupling, and contradiction with the fluid limit. | **Embedded content proved:** `countsFullLaw_infection_pressure_after_three_halves_tendsto_zero` proves the rational infection probability vanishes uniformly over every time after $\lfloor3n/2\rfloor$, stronger than the printed interval. The proof uses actual uniform noise control, the true stopped/unstopped coupling and $U_n/n\to0$, avoiding a future-conditioned walk coupling. |
| A84 | 2275–2285; `eq h n tend vers zero`, `eq somme jusque n sur 2 tend vers zero` | Reversed-increment representation of the late reciprocal sum and reduction to the last half-$n$ time window. | **Corrected source reduction proved; printed identity refuted:** `SIRReversedHeightIdentity` proves exact pre-step reversal and formally refutes the shifted printed equality on the genuine feasible $(+1,-1,-1)$ word ($1/2$ versus zero). `SIRCountsExtinctionIndex` supplies the measurable genuine first zero under the actual law. `SIR.countsFullLaw_late_charge_reduced_to_lastHalf` proves the corrected-charge reduction to the last half-window, supplying the earlier normalized remainder internally from the actual triangle fluid law. Independent audit: five expanded examples/ten permitted closures. The final half-window iid localization remains A85–A86. |
| A85 | 2287–2305; `eq limite proba A n epsilon tend vers 1`, `eq limite proba Y epsilon toujours plus grand que i sur 2` | High-probability late-transition event, iid domination of reversed increments, and high-probability lower linear bound for the auxiliary walk. | **Auxiliary iid assertions proved; genuine reverse coupling open:** `IidHalfSlope` proves the unconditional whole-time half-slope probability tends to one, including time zero, by Chernoff and a countable geometric union (independent audit four statements plus reindexing/eight closures). A83 supplies the late-pressure event. `SIRReverseCouplingFormulation.SourceReverseIidCoupling` states the exact actual-history/unconditional-iid joint-law target, with measurable genuine first extinction and random window. `Necessary` proves a necessary marginal bound only. The positive-probability source-window hazard inheritance gap is proved in `SourceGap`; it does not refute the weaker coupling itself (S25). |
| A86 | 2306–2321 | Harmonic expectation bound, localization on good events, and convergence of the post-$n$ reciprocal sum divided by $\log n$ to zero. | **Convergence conclusion proved by the forward alternative; auxiliary expectation now checked:** `countsFullLaw_post_population_birth_charge_over_log_tendsto_zero` and the exact word reciprocal comparison prove the required limit. `IidHalfSlope.expected_auxiliary_harmonic_failures` also proves the literal iid harmonic expectation with the source negative-step parameter. The localized reversed-sum inequality and expectation still require the actual reversed coupling and remain open. |
| A87 | 2326–2330 | Conditional stochastic height domination, Bennett union bound, asymptotic $g(u)\sim u\log u$, and negligible additional maximum height. | **Maximum conclusion, scalar asymptotic and corrected fixed-word Bennett estimate proved:** the earlier actual forward exponential-sum route gives negligible extra maximum. `bennettRate_div_mul_log_tendsto_one` proves $g(u)\sim u\log u$; `bennett_unionBound_tendsto_zero` proves the exact scalar bound vanishes for every eventually positive deterministic mean $m_n=o(\log n)$. `SIR.terminal_word_cutMaximum_bennett` gives the genuine conditional fixed-word bound with explicit threshold $1+D+a$ and factor $2n+2$; `terminal_word_cutMaximum_zero_charge` proves zero tail above one in the zero-charge case. Independent restricted audit (scalar and fixed-word Bennett only) six expanded examples/eight closures passes. **Fixed-state generating-function recursion and corrected per-vertex exponential-moment bound proved; stochastic domination remains unproved. This is an inequality of exponential moments for all $c\ge1$ from any valid state with $\lvert\mathrm{active}\rvert=S_n$, with Bernoulli parameters $1/S_i$ for the attachment steps $i=n+1..n+k$ ($S_i$ the active count after step $i$); no coupling or stochastic ordering is constructed (the recursion also gives equality of generating functions of the uniform active vertex, not stated as a theorem); this per-vertex step is not covered by the earlier independent Bennett audit (statement-level independent review in `verification/INDEPENDENT_REVIEW_RESUMPTION_2026_10_30.md`):** `Forward.lintegral_activeHMean_pow_treeLawFrom` is the exact exponential-moment recursion for the height of a uniform active vertex started from any valid state at time $n$ (a factor $1+(c-1)/S_i$ per attachment step, none at freezing steps), and `newVertex_height_pow_le` bounds the height of a vertex born by attachment at time $n+k+1$ by $H+1$ plus independent Bernoulli$(1/S_i)$ increments in exponential moment (the $+1$ is missing in the printed statement, harmless for the $O(\ln n)$ conclusion). Probe `verification/A87A14StateStatements.lean` exit zero. The literal shifted-mean/unshifted-threshold bound and the future-conditioned random-mean argument remain uncertified; the corrected fixed-word estimates are not claimed to certify them. |

## Source issues and obligations that cannot be certified literally

These are audit findings, not changes to the supplied TeX. A proposed repair remains distinct from verification of the printed argument. Concrete false statements are separated from proof gaps needing further investigation.

1. **S01 — L04 is false on its printed support.** Set $n=3$ and $X_1=X_2=1$, $X_3=-1$. Then $S_3=2$ and $N_3=3$. Consider the root with two children: one edge labelled $1$ ending in a frozen vertex labelled $2$, and one edge labelled $3$ ending in an active vertex; the root is active. This tree belongs to $\mathfrak T^+_{2,3}$ as defined in the paper, but has probability zero under the fixed schedule because step $3$ freezes and cannot create an edge labelled $3$. The printed product is $1/(1\cdot2\cdot3)=1/6$. The tree is compatible with schedule $(+1,-1,+1)$ instead. The corrected support now requires the exact positive/negative schedule labels, increasing parent labels, compatible frozen times, and the rooted-tree data. `Forward.HistoryShape` is proved equivalent to existence of an actual legal history and to positive atom mass. The corrected product formula and T05 are proved on this support; the printed broader claim stays false.
2. **S02 — L03 is false when the two vertices coincide.** Take $n=1$, $X_1=1$, and $u=v=a_1$. Then $b_1(u)=1$ and $\operatorname{coal}_1(u,u)=1$. At $c=0$ the displayed left side is $0$, while the right side is $1/\binom22=1$. `printed_coalescence_law_counterexample` verifies this for the actual coherent law. The corrected distinct-vertex statement is proved. Equal uniform samples are handled separately with probability $1/N_n$ in L09.
3. **S03 — the birth-law proof's conditional-uniform sentence is shifted.** At line 611, $b_n(V)$ conditional on a frozen vertex is uniform on $\{i-1:i\in\mathbb F_n\}$, not on $\mathbb F_n$. The final formula of L02 uses the correct shift.
4. **S04 — forward selection probabilities in the local-limit proof use the wrong time.** Lines 902 and 906 use $1/S_n$ for selecting a vertex at forward step $n$; Algorithm 1 selects among $S_{n-1}$ active vertices. For schedule $(+1,-1,+1,+1,\ldots)$, a particular original vertex freezes at step $2$ with probability $1/2$, whereas $1/S_2=1$. Its actual probability of never freezing is $1/2$ while the printed product gives zero. The reciprocal-series equivalence is proved, and `ForwardSelectionSourceChecks` formally verifies the finite and infinite counterexample. Selection events must also begin strictly after the observed vertex's birth: its own birth-degree jump is deterministic. The corrected conditional-independence and Borel–Cantelli argument is now checked in A22; the incorrect finite products cannot be certified.
5. **S05 — the Introduction reverses the signs of Algorithm 2.** Line 311 says positive steps add a singleton and negative steps merge. The precise Algorithm 2, lines 532–536, does the opposite. The precise algorithm is the intended construction, but the introductory assertion remains a source error. The all-positive example at line 273 also has $n+1$ vertices after $n$ steps, not $n$.
6. **S06 — Bernoulli parameter at absorption.** A13 is stated up to $n=\tau$, when $S_n=0$ and the text introduces a Bernoulli variable with parameter $1/S_n$. Its multiplier vanishes because the final step is negative, but the Bernoulli variable itself is not defined as written. Define parameters only on attachment steps or use the complete indicator-weighted parameter from the outset.
7. **S07 — averaging and distance gaps.** Lines 1459–1469 average only over distinct frozen birth labels, omitting active vertices and equal samples. L09 is now proved with all cases included. Moreover $\operatorname{coal}_n/n\to0$ alone does not imply negligible common-ancestor height on the $\log n$ scale in line 1482. `uniform_coalescence_div_log_tendsto_zero` proves the stronger required time estimate: beyond $\lceil A_n\rceil$, the hazard sum is $O(1/A_n)$, while $A_n=o(\log n)$. The actual graph-distance inequality and joint forward transfer are now proved, including the diagonal; the limiting distance and all-real-power conclusions are now proved using exponential moments of the two heights. No moments of coalescence time are required.
8. **S08 — cut-forest/chaining details.** Line 1648's parenthetical active-vertex description omits the initial root when there is no adjacent edge yet; use activity at time $k$ as the definition. Line 1656 should match active vertices of $\mathcal T_k^n$, not of $\mathcal T_{k'}^n$, to marked roots. Line 1771 uses $S_{C^k}\le C^k$, false for the all-positive schedule ($S_i=i+1$); constants need slack. Line 1780 repeats $N_k$ in the denominator where the conditional expectation gives $\overline N_kN_k$. The eventual estimate $S_{C^k}\le C^k+1$ now yields the finite matching mean lower bound $3b$ instead of $4b$ for $C^k\ge3$, with failure bound $3M/b$. The initial scale of the cumulative-good count imposes no previous block, so it equals the active population; the source incorrectly compares it directly to $N_{k_0}$. The planned threshold $\rho2^k$, $\rho=c/4$, gives a deterministic base. Their full tree-level chaining integration remains open.
9. **S09 — large-deviation proof domain.** For $\eta\in(0,1)$ and small $c$, $f(c)-1-\eta$ can be negative. The function $g$ was introduced only on positive arguments, and the claimed $\delta\in(0,1)$ at lines 1806–1808 does not follow for the full stated range. Prove the result first for smaller positive $\eta<f(c)-1$ and extend by monotonicity, or give a separate lower-threshold argument.
10. **S10 — strict Poisson tail.** Line 1838 lower-bounds $\Pr(Z>\lambda t)$ using the mass at $\lceil\lambda t\rceil$. When $\lambda t$ is an integer that mass is outside the event. Use $\lfloor\lambda t\rfloor+1$ and re-establish the quantitative estimate with its rounding loss.
11. **S11 — urn filtration and imported proof.** L13 conditions only on $U_n$ in its displayed transitions, but a martingale maximal inequality needs transitions conditional on the full past, or an explicit Markov-chain hypothesis. The assertion is imported by reference to a proof not reproduced in this source. The exact constants and infinite-time conclusion are now proved for `HasPathLaws`, which specifies every finite-dimensional law by actual urn-kernel iteration. This checks the intended Markov urn formulation, with a direct backward exponential and first-crossing argument. The displayed weaker conditioning alone has not been proved sufficient; that literal obligation remains unresolved.
12. **S12 — `eq:c0` is false below $A_n$.** Choose integers $m_n\to\infty$ with $m_n^2=o(\log n)$ and let $A_n=m_n^2$. For each $n$, take $m_n$ repetitions of $(+1,-1)$ followed by positive steps forever. The walk never hits zero. At $i=2m_n$, $S_i=1$, so no uniform positive $c_0$ can satisfy $c_0i\le S_i$ for every $1\le i\le n$. For $i\ge A_n$ (eventually), $S_i=i-2m_n+1$, hence the first linear assumption holds with $c=1$, and the second holds as well. The likely repair is to restrict the lower bound to $A_n\le i\le n$, which suffices for the subsequent large-scale use.
13. **S13 — SIR fluid proof replaces an asymptotic parameter by an equality.** Line 2181 uses $\lambda/n$ instead of $\lambda_n$ although only $n\lambda_n\to\lambda$ is assumed. The drift has an additional vanishing deterministic error that need not be $O(1/n)$. A suitable perturbed Grönwall estimate is needed. The generic criterion at lines 2162–2176 also needs its initial-value assumption and a justified adapted drift bound.
14. **S14 — time reversal of the late SIR path.** The forward late-transition bound does not by itself justify iid domination of increments read backward from the random extinction time (line 2295). Conditioning on extinction and on the late-transition event changes their law. The asserted reverse coupling is a substantial unverified step; it must be proved or replaced, with any departure recorded. The displayed reverse-sum identity also shifts $X_i$ to $X_{i+1}$ under the given definitions and needs explicit reindexing.
15. **S15 — geometric subdivision needs finite repairs.** The unrestricted source partition is false: $a=2,b=3,\beta=4$ gives $\ell=1,m=0$ and overlapping/extraneous endpoint intervals. The repaired choice $1<\beta<C$ under $aC<b$ orders the cuts and still permits $\beta\downarrow1$. Even then, $\beta=4/3,a=2,b=3,C=7/5$ has one final integer point but real geometric length $64/81<1$, so the last endpoint needs an additional $1/A_n$ rounding term. The printed intermediate denominator $\beta^{\ell-1}$ must also be $\beta^m$ for the last block; an actual all-attachment example gives the false comparison $6\le2$. `GeometricHeightSourceChecks` proves these three counterexamples. A37–A38 now prove the repaired geometric strategy through the original exact maximum/nested-limit conclusion, with eventual positivity of the actual lower constant. The earlier Abel proof remains available. The random-mean zero-row convention and real-power tail integrals mentioned at the earlier milestone are now resolved under A34/A36/A40–A43. None of these findings refutes a main theorem.

16. **S16 — the upper bound of P03 is false at $n=1$.** Take $X_1=1$, so $\tau>1$ (extend by positive steps), $\operatorname{Height}(\mathcal T^1)=1$ deterministically, and $h_1^+=1/2$. At $t=1/4$ the left side is $1$, but the printed right side is $\exp(-g(1/2)/2)<1$. The union bound in line 1222 uses $n$ although the deterministic reverse-label set can contain $n+1$ vertices. Its random root cannot be discarded while retaining the fixed-label Bernoulli law. The proposed immediate repair replaces $n$ by $N_n=(S_n+n+1)/2$ or $n+1$; the unshifted repaired reverse bound is now proved by `reverseMaximum_corrected_upper_tail_source`. `exists_counterexample_printed_height_bound` proves the counterexample for the actual reverse-tree law, including strict survival, without T05. The main T03 results instead use a proved forward bound with factor $n+1$ and threshold shifted by one edge.

17. **S17 — cut-forest boundary and activity conventions.** The operational definition of $\mathcal A_k$ means vertices genuinely active at time $k$. The adjacent-edge parenthesis at line 1647 omits the initial root at $k=0$; the formal cut roots preserve the operational definition. At line 1657, a marked root $\star$ is declared active by convention even if it froze between the two cut times. Thus a component count that includes every marked root can exceed the true active population used by the urn by one. The proved L11 now explicitly absorbs this correction through the comparison $M\le U+1$ and slack in the finite exponential tail. This does not change L10/L12, whose counted vertices are genuinely active at the upper cut time. In the same paragraph, the merging description incorrectly names active vertices of $\mathcal T_{k'}$ instead of $\mathcal T_k$; the independence assertion also needs a representation that erases the old vertex names before matching. A complete conditional grafting law is now proved for the augmented forest retaining true root freezing clocks. The printed all-star forest erases those clocks, so matching alone cannot recover the complete labelled active/frozen terminal state. `ForwardForestStarConvention.star_activity_counterexample` checks the strictly surviving two-step schedule $(+1,-1)$ at cuts 1 and 2: two marked roots versus one genuinely active terminal vertex. Actual bare-forest conditional means, pair covariance, variance, Chebyshev and normalized growth formulas are now proved separately. Bare geometric fields are reconstructible with a true matching, while erased root clocks remain unrecoverable by matching alone.

18. **S18 — the future-maximum Grönwall criterion is false even with zero initial error.** At lines 2162–2176 take the deterministic path $X_k^n=k$, time horizon $1$, and constant $C=1$. The increment and its squared moment equal $1$, and $1\le(1+n)/n$ gives the printed drift bound, but the normalized maximum equals $1$ and does not converge to zero. `SIRSourceChecks.printed_global_max_criterion_counterexample` checks these scalar bounds and the failed limit. A valid adapted drift estimate is needed. `SIRFluidApproximation` and `SIRSusceptibleFluid` prove the actual fluid limit through a past-sum Grönwall estimate and genuine exponential noise bounds, retaining initial and rate errors. This correction does not certify the false printed criterion.

19. **S19 — extinction means hitting zero.** At line 2158 the walk started at $1$ must be compared through hitting zero or the nonpositive integers. With upward probability $\lambda/(1+\lambda)$, $\lambda>1$, its hitting-zero probability is $1/\lambda$, while hitting a negative integer has probability $1/\lambda^2$. The latter wording cannot identify the advertised survival mixture. The corrected two-stage early extinction probability is now proved in `SIREarlyExtinction`, using genuine fixed-prefix probabilities and a true-kernel superharmonic bound. This does not certify the printed negative-integer wording.

20. **S20 — the binary-tree example uses the vertex count as its parameter.** The definition at line 745 gives $2n-1$ vertices for a tree in $\mathfrak B_{k,n}^+$. The image of the displayed $\mathfrak T_{4,8}^+$ tree therefore belongs to $\mathfrak B_{4,8}^+$ and has fifteen vertices. The prose and caption instead name $\mathfrak B_{4,15}^+$, which would require twenty-nine vertices. `BinaryBijection.figure_binary_vertices` and `figure_parameter_fifteen_impossible` certify this contradiction. P01 itself uses the correct common parameter $n$.

21. **S21 — the random-mean complement sum includes its cutoff twice.** At line 1423, $M_n$ already includes the summand at $B=\operatorname{birth}_n(V_1^n)$. Thus $h_n^+-M_n$ sums over $B<i\le n$, whereas the printed equality starts at $i=B$. For the all-positive schedule with $n=B=1$, the true difference is zero and the printed sum is $1/2$. `UniformBirth.heightScale_sub_truncatedMean` proves the corrected strict tail, and `printed_inclusive_birth_tail_false` certifies the counterexample. The subsequent upper estimate can retain the larger sum, but its printed equality is not certified.

22. **S22 — the real ceiling-factorial bound is false.** The source claims $\lceil u\rceil!\le u^3(u/e)^u$ for every real $u\ge2$. At $u=21/10$ the right side is strictly less than $6=3!$. `PoissonSourcePolynomialChecks.printed_real_ceiling_factorial_counterexample` proves this, including an admissible source choice $\lambda=41/20>2$, $t=42/41>1$ with $u=\lambda t$. The final cubic strict-tail inequality is nevertheless true and is now proved for all stated parameters using the corrected floor-plus-one mass and a separate small-threshold argument. The logarithmic prefactor conversion supplies the stronger sufficient condition $\log C\ge(Kt)^3$ during the large-integer witness choice.

23. **S23 — the printed Poisson rate slack is not positive for all margins.** At lines 1805–1811, $\eta\in(0,1)$ need not imply $f(c)-\eta>1$. `PoissonSourcePolynomialSlackChecks.printed_all_margin_rate_slack_counterexample` constructs an actual admissible $c$ with $f(c)=5/4$ and $\eta=3/4$ for which the displayed $\delta=1-[(c+1)/(2c)]g(f(c)-1-\eta)$ is negative. The exact printed exponent and positive slack are proved when $1<f(c)-\eta$. For arbitrary positive margins, the transparent auxiliary threshold $t=\max((f(c)+1)/2,f(c)-\eta)\in(1,f(c))$ gives valid positive slack and a lower bound for the original $P(C)$. This repair does not certify the false all-margin scalar assertion.

24. **S24 — the no-current-merge prose has an inclusive boundary error.** At line 1915, $Y_i=1$ and $\operatorname{coal}(v,w)\le i-1$ do not exclude a merge during the current step: equality permits exactly that merge. `BernoulliPairCouplingSourceChecks.source_current_merge_boundary` gives an actual Algorithm 2 example at $n=i=1$ with two initial roots. The first height increment equals one and the roots merge with probability $1/2$, while the coalescence time is zero. The following algebraic formula remains valid when its same-root branch is read before the step; the constructed coupling uses that correct state criterion.

25. **S25 — the late gate does not inherit across the whole reversed window.** The source gate begins at $3n/2$, whereas the random reversed window can reach earlier steps. `SIRReverseCouplingSourceGap` gives a genuine positive-probability actual-history witness at $n=6$, word $(+,+,+,-,-,-,+,-,-)$ and first extinction nine: the gate has susceptible count two, but included reverse coordinate three uses pre-step count three and a strictly larger forward infection hazard. This refutes the stronger hazard-inheritance assertion. It does **not** refute `SourceReverseIidCoupling`, which requires only an unconditional iid marginal and may correlate with the gate. That weak coupling remains open.

## Explicit conjectures and research questions

These remain visible in the inventory but are not claimed theorems of the paper and must not be presented as proved results.

| ID | Source | Status |
| --- | --- | --- |
| Q01 | 2345 | Number of ends of the infinite tree: open research question. |
| Q02 | 2346 | Evolution of forest component sizes and vertex degrees: research directions; the concrete all-positive coalescent specialization is A07. |
| Q03 | 2347–2350 | Universal lower height bound $(e-\varepsilon)\log n$ for every schedule surviving to $n$: explicitly a conjecture, including the boundary $\tau=n$. |
| Q04 | 2124–2127 (`rem:SIR`), 2351 | Maximum-height limit for the finite-$\lambda>1$ SIR regime: open question. The proposed non-negligible contribution near extinction is heuristic, not a proved limit theorem. |
| Q05 | 2352 | Preferential and other attachment mechanisms: future research. |
| Q06 | 2353 | Nonuniform freezing: future research. |
| Q07 | 2354 | Root/patient-zero recovery: future research. |

## Proof correspondence and next audit milestones

The initial source reading checks the **inventory and the mathematical meaning of the intended obligations**, not the correctness of all written arguments. L02's counting proof and its application to the actual reverse tree are checked, with the frozen-label shift explicit. L07 originally used a different harmonic comparison; A32 now separately verifies the actual adjacent-swap/sorting argument. P02 uses MGF factorization and Chernoff optimization; the source states Bennett without a proof. A05 uses the intermediate value theorem and monotonicity. EqProp9 and A17's factorial induction are checked directly. S16 now has a complete actual reverse-tree counterexample, not only a scalar obstruction.

**Substantive T03 departure:** the proof derives the conditional uniform-active height recurrence directly from Algorithm 1. Averaging after an attachment mixes the old active-height law and its unit shift with parameter $1/S_{n+1}$; averaging uniform deletion at a freezing step leaves that law unchanged. These exact finite identities give the all-parameter MGF estimate. For maxima, the proof controls the expected sum of exponentials over all vertices, including frozen vertices, and retains the child's extra edge. Chernoff bounds yield the probability limits; real higher moments, Jensen and Hölder/truncation yield every real-$p$ limit on varying probability spaces. This route bypassed the reverse representation and T05. The reverse representation and corrected finite maximum-tail argument have since been checked separately; T05 is now proved as well. The displayed real-power tail-integral calculations have since been verified in A34 with the explicit logarithmic-envelope departure; the uniform-in-$C$ estimate and the source maximum-law tail-integral consumer are now proved in A36.

**Substantive L08 departure:** write $E_i=S_i-ci$ and sum its weighted increments by Abel summation. The resulting finite bound is the slope error times a constant depending only on $c,C$, plus a boundary error of order $1/(a\log C)$. Denominator positivity follows from the slope error being at most $c/2$. This proves the exact finite-maximum/double-limit conclusion without geometric subdivisions. The source's EqProp9 and the repaired geometric partition with exact $U_n,L_n$ estimates are now separately checked in A37–A38; three false finite steps remain formally refuted. The two literal assumptions are proved equivalent to quantified uniform estimates with explicit boundedness of the real limsup/liminf; eventual nonempty finite intervals are also proved. T04.I then follows by the source's early/middle/late decomposition, with both integer rounding operations certified.

**Substantive T04.II.height departure:** `ForwardUniformHeight` constructs conditional uniform sampling over all vertices and proves its exact mixture: the root and one shifted active-height law for every attachment time, each with weight $1/(P_n+1)$. Positive exponential moments cancel this vertex-count denominator. For the lower tail, stochastic increase of the active-height law bounds every birth after $\lfloor\varepsilon n\rfloor$ by the active law at that cutoff; the root and early births have mass at most $2(\lfloor\varepsilon n\rfloor+1)/n$. The bulk hypothesis shows that removing the late block changes the logarithmic height scale by a negligible amount. Concentration, exponential moments and the real-power Hölder argument finish every $L^p$ limit. The reverse random-mean route A40–A43 has since been proved separately, including the literal conditional Bennett/layer-cake argument, the missing domination of small random means, the corrected harmonic bound and the final exact source uniform-height consumer. The direct forward proof remains a substantive alternative route.

**Reverse-history arguments checked:** the new increment's joint law with the whole preceding history factors from the genuine kernel. This proves L01's conditional expectation, then mutual independence and telescoping for each fixed vertex. The common-history coalescence time is the greatest phase with both labels in one component. Actual transitions preserve coalescence, and the terminal one-root property excludes the default case of the finite maximum. The separation product therefore gives the corrected L03 distribution, while equal vertices coalesce exactly at birth. P03's lower-tail reduction and upper union argument are checked for the actual reverse tree, retaining the true vertex count. These proofs do not assume independence of heights belonging to different vertices.

**Scalar Poisson departure:** Mathlib's Stirling estimate gives a logarithmic factorial bound, applied to the strict-tail witness $\lfloor\lambda t\rfloor+1$. Positive large-deviation slack proves divergence of $C P(C)$ and hence the required $6/(cC)$ bound. This replaces the printed polynomial lower bound, whose integer-threshold argument is incorrect. Large margins use monotonicity from a valid threshold in $(1,f(c))$. The Le Cam bounded-test estimate is proved directly by single-coordinate comparison and convolution contraction, with explicit parameter drift. The timestamp-preserving cut-forest bridge now identifies the actual forward count and transfers the mean estimate to L12.

`ForwardScheduleSupport` proves the necessary schedule-compatible vertex and frozen-label support missing from L04. Both forward and stamped reverse histories now have the exact actual probability products and are reconstructible from terminal data. The reverse active-label permutation action preserves legal histories and has a free orbit of size $S_n!$. Each entire reachable canonical fibre is now identified with that orbit. Truncation of the canonical terminal state proves an actual forward history, and atomic comparison gives T05. This follows the paper’s probability-product/factorial strategy on the corrected support; it avoids assuming reachability of every tree in the paper’s overly broad shape class.

**T04.II distance repair and correspondence:** on one genuine reverse history with two independent conditional uniform labels, the two depths and actual graph distance satisfy $0\le H_u+H_v-D\le2C$, where $C$ is their coalescence phase. The sharper $C/\log n\to0$ estimate supplies the missing logarithmic argument; both height marginals have the already proved forward height limit. For the moment upgrade, $D\le H_u+H_v$ and $\exp(H_u+H_v)\le(\exp(2H_u)+\exp(2H_v))/2$ give an exponential bound without assuming independence of heights. This proves all real $L^p$ limits. The diagonal is included throughout. Coalescence time is used only in probability; no unjustified high-moment estimate for its diagonal contribution is needed.

**Pair-tail and variance proof departure:** the actual two-root transition kernel satisfies a product supersolution until coalescence. Iterating it bounds the separated joint tail by the square of the original single-root Bernoulli tail; the genuine coalescence hazard sum bounds the remaining event. Coherent continuation transfers this bound to one common history. Summing the true random-root indicators gives the second moment and variance estimate. This earlier route bypassed the printed independent auxiliary $\xi_i$ construction; that construction, independent thinning and the final actual-tail consumer have since been proved separately (A60–A61). Chebyshev, the proved mean lower bound, and a common minimum of the two cutoff parameters now prove the reverse-history counterpart of Forestier, with the exact uniform $L/C^k$ window. The forward-cut bridge is now proved: parent recursion equals the recorded phase depth, that depth equals distance in the induced finite cut graph, and a bijection of actual roots equates the counts. L10 and L12 are therefore proved for the actual forward law.

**L11 proof correspondence:** the conditional population of genuine active descendants of each lower-cut root follows exactly the signed urn kernel, with initial value one. Its finite MGF gives a uniform positive exponential moment under the corrected linear bounds above $A_n$. Chernoff then yields a component tail exponentially small in $k^3$, which absorbs the at most $C^k+1$ candidate roots and gives the exact $1/k^2$ bound. The marked-root convention is included by the proved count bound $U+1$. This bypasses the paper's infinite positive-step extension and use of L13 for an endpoint estimate; those are not certified by the L11 proof.

**Signed urn progress:** `PolyaBernoulliMGF` proves the small centered-Bernoulli exponential estimate and the complete backward parameter step for both increment signs. This checks the analytic mechanism of the cited urn proof, but it is not the maximal inequality L13: `SignedUrn` and `SignedUrnContinuation` now supply the actual kernel, invariant occupancy domain, and finite backward MGF iteration. `SignedUrnConcentration` proves the finite endpoint tail with denominator $4(D+tM)$. `SignedUrnPath` and `SignedUrnMaximal` now prove the finite maximal bound directly by first-crossing recursion, and `SignedUrnInfinite` passes to an increasing union of finite events under the explicit full path-law assumption. This replaces the cited Doob/submartingale step; the finite kernel iteration and signed exponential comparison are checked. The literal weaker filtration wording remains unresolved. The component-size application L11 is proved separately by a finite endpoint MGF, which also absorbs the marked root. The primary external reference read was arXiv:2012.13058v1 (December 2020), Appendix A.1; no claim is made to have checked the final 2023 publication.

T03, all parts of T04, L01, L02, L05, L06, L07, L08 and L09 are now proved. T05 and corrected L04 support are also proved. L10, L11 and L12 are proved for the actual forward cut forests. Work continues on the literal filtration issue in L13 and the remaining source arguments. T01 and T02 are now proved; the constructed embedded SIR model has both T06 conclusions and actual auxiliary population fluid limits. Its physical identification and stopped T07 results remain open. All skipped source arguments remain obligations.

At each milestone, add exact declaration names and source correspondence, run the current affected Lean targets and batch transitive axiom queries, and independently audit changed statements and semantic dependencies. Conditional results remain conditional. Before any claim of complete coverage, reconcile every row, repeat the whole-source omission scan, and resolve the literal false statements explicitly. Publication additionally needs the reviewed Challenge/Solution interface, current Comparator evidence for the exact candidate, a clean reproducible build, a public source commit for Palomar, and the full mandatory Palomar mechanical verification. None of those checks is replaced by this report.

The maximum-height lower-bound assembly now has checked canonical prefix laws (`ForwardTruncationLaw`, `ForwardContinuationPrefix`), deterministic good-set heights (`ForwardGoodChains`, `ForwardGoodChainMaximum`), exact geometric indices (`GeometricChainCutoffs`), genuine inheritance under the forward continuation (`ForwardGoodChainPropagation`), and multiplicity-preserving projection to the tagged population kernel (`ForwardTaggedPopulation`, `ForwardTaggedCounts`). Independent reviews checked these interfaces. The true conditional growth estimate and summable failure chain are now integrated in `MainLinearMaximumLower`, which proves T04.III. The finite-permutation second-moment mechanism and geometric chaining are checked. The proof replaces source conditioning by joint-event estimates, uses the corrected initial population, and sums the exact errors directly. The permutation-averaging route does not certify the source’s full conditional forest independence or conditional expectation/variance claims in A47/A52.

**T01 proof correspondence and departures:** `ForwardInfiniteHistory` constructs the actual common trajectory by Ionescu–Tulcea, with exact finite marginals and legal steps. The true freezing hazard is $1/S_{i-1}$, while T01's criterion retains the printed $1/S_i$; a factor-two comparison proves equivalence of the two reciprocal series. `ForwardLifetimeLimit` identifies the actual infinite survival event and proves simultaneous eventual freezing. `ForwardLocalStability` then inducts on radius: freezing the radius-$h$ ball fixes that ball and the finite vertex set at radius $h+1$. Freezing that next finite set gives stabilization of every labelled ball. `LocalTreeGraph` proves the coherent finite-ball limit is a genuine connected acyclic locally finite graph with exactly the stored distance balls. Its almost-everywhere measurability and weak law follow from pointwise convergence and dominated convergence.

For T01's diagonal implication, `ForwardSchedulePrefix` constructs an actual coupling of the two complete trajectories. Frozen prefix balls agree at all later horizons; their failure probability tends to zero. The clopen cylinder basis then identifies the same weak limit. For necessity, a finite-kernel exponential product bounds the true joint event that the root remains active and has bounded degree. The attachment hazard sum diverges. If the freezing series converges, a fixed positive mass therefore escapes every degree threshold. Prefix-law equality and degree monotonicity transfer that mass to the diagonal sequence, contradicting Portmanteau for the continuous root-degree observable. This bypasses the source's conditional-independence/Borel–Cantelli and union-event arguments; those literal source checks are not inferred from the main result. `ForwardLocalExtinction` separately proves pathwise absorption and identifies the finite-extinction local limit, for use in T02. Independent audits reconstructed T01 with the actual pushforward laws, literal schedule quantifiers, and the same measurable limit for both sequences.

## Current verification and publication evidence

Checked on **30 October 2026** for the integrated main results, combinatorics and source-argument milestone. The source and declared whole-paper scope are unchanged; the initial inventory is retained. T02 and its changed dependencies received a new independent source/type review.
These sources are newer than the private remote snapshot. No current publication
commit is claimed. The comparison configuration still covers the earlier
supporting-result interface; it has not been extended to the new main theorems.

| Check | Actual result |
| --- | --- |
| `lake build` | **Pass** (historical checkpoint; the current result is 4,631 jobs, see the final section), 4,596 jobs, all default targets `Freezing1`, `Challenge`, `Solution`. Includes A04 exact conditioned iid rows, all A77 actual capture interfaces/pairs, A87 scalar and corrected fixed-word Bennett/zero-charge scope, actual recursive-tree specialization, and the two checked one-susceptible SIR foundations. Unimported proof drafts have separate status. |
| Fresh project build | Not rerun for this enlarged milestone. The earlier supporting snapshot passed a fresh project build reusing the pinned public dependency cache; that result is not evidence for the newly added modules. |
| `lake env lean scripts/AxiomAudit.lean` | **Pass** (historical checkpoint; the current result is 8,618 declarations, see the final section) for 7,986 declarations in namespace `Freezing1` at the 4,596-job integration. Every transitive axiom is one of `propext`, `Classical.choice`, `Quot.sound`. This checks dependencies, not independent kernel replay or complete source coverage. |
| `lake env lean -DautoImplicit=false verification/MainLocalLimitStatement.lean` | **Pass**, two independently reconstructed source statements and six transitive closures, all standard axioms. Uses explicit pushforward laws, almost-sure agreement of full finite balls, the literal eventual schedule quantifiers and one common measurable limit. `LocalNecessityStatements` adds three expanded checks and eleven closures; `ForwardDegreeStatements` adds three expanded checks and twenty-seven closures. |
| Exact T02 statement probe | **Pass**, `verification/MainGeometricLimitStatements.lean`: seven expanded independent source statements and sixteen standard-axiom closures; actual iid prefix mixture, one chronological local limit, literal offspring mass, all-child joint branching law, and $p=0$. |
| Exact forward L11 statement probe | **Pass**, `verification/MainLinearComponentMaximumStatement.lean`: expanded marked-root component maximum, exact window and nested source hypotheses; four standard axiom closures. |
| Geometric chain index probe | **Pass**, `verification/GeometricChainCutoffsStatements.lean`: exact rounded cutoffs and logarithmic span; thirteen standard axiom closures. |
| Forward chain structure probe | **Pass**, `verification/ForwardChainAxioms.lean`: fifteen current closures for continuation histories, prefix event laws, good-chain heights and inheritance, and actual tagged counts. All use only the three permitted standard axioms. |
| Exact T04.III statement probe | **Pass**, `verification/MainLinearMaximumStatement.lean`: expanded source limit assumptions, actual maximum over vertices, arbitrary factor satisfying the source equation and its proved uniqueness; seven permitted axiom closures. |
| Independent statement audits | **Pass for the integrated scope**, including T05 with a separately reconstructed full observable, corrected L04 support, the exact T03, T04.I and both T04.II statements, the full T04.III statement, the actual graph and sampling definitions, exact nested-limit assumptions, uniform block estimate, real-power/varying-law limits, reverse kernel/birth law, and the source counterexample. The forward L10/L12 wrappers and their timestamp-preserving cut-forest bridge also pass independent automated source review. Separate automated reviewers reconstructed exact main-result statement examples. No human review claimed. |
| Challenge source | Earlier 900-line, 38,094-byte supporting reference; only Mathlib imports, 16 exports, no holes. It does not yet include the new main theorems. Complete copied proofs are not independent proof implementations. |
| Maintained source scan | **Pass** for 624 maintained Lean sources at this checkpoint: unchanged source identity, all 24 environments and A01–A87/Q01–Q07 IDs, module headers, size bounds, forbidden-construct scan, pinned environment and official v0.4 metadata schema. This text scan includes unimported drafts and does not establish their proof completion. |
| Environment | All 9 dependency source revisions match `lake-manifest.json`; project and Mathlib toolchains agree on `v4.35.0`. Pins were not upgraded. |
| Metadata | `formalization.yaml` passes the official v0.4 JSON Schema (schema blob `19f4a46a1bc0e4798dca7bcb7ed57281b1c8c996`); citation and workflow YAML parse. |
| `lake comparator --config comparator.json` | **No successful check.** Earlier local attempt exited 2 because `bwrap` requires Linux namespaces. The earlier private-snapshot Linux CI passed build/axioms but failed Comparator before comparison with `bwrap: setting up uid map: Permission denied`. No current-milestone comparison was run; isolation was not disabled. |
| Independent kernel replay | **Unverified**; an axiom check and ordinary Lean compilation do not replace this. |
| Full Palomar preflight | **Not run**. The repository is private; no `mechanical-report.json`, NanoDa acceptance, intake, or registration exists. |

The retained logs in [verification/](verification/) give the current build and
axiom outputs, independently reconstructed main-statement probes, and the earlier
local Comparator platform error. Source-faithfulness judgments and proof-route
findings above are separate from these mechanical logs.

The private repository is
[`igor-kortchemski/uniform-attachment-with-freezing`](https://github.com/igor-kortchemski/uniform-attachment-with-freezing).
It was created prematurely, before the requested formalization was complete;
further uploads and publication operations are now suspended as instructed.
Apache-2.0, citation,
provenance notices, CI, and a manually dispatched full Palomar preflight workflow
are prepared. The Palomar workflow does not run on a private repository and does
not perform intake or registration. The source manuscript was not relicensed or
edited. No GitHub Release or public deposit is claimed.

Publication-sensitive sources refreshed at these immutable revisions:

- [Palomar policy `28bd48b`](https://github.com/PalomarRegistry/PalomarPolicy/tree/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60).
- [Palomar pipeline `14aa8d6`](https://github.com/PalomarRegistry/PalomarSubmission/tree/14aa8d6b3c2f14a8540605e37144560b9a00e7e7), used consistently in the prepared workflow.
- [Palomar template `2891de4`](https://github.com/PalomarRegistry/PalomarTemplate/tree/2891de4c48955af824969a263d31b25e7a9a1406).
- Lean CI action `fe408643ea7367d8c0404a8be3975bb145f5fb64`.

## Explicit remaining work

1. Continue the remaining intermediate full-paper obligations. T01–T07, P01, C01 and A28 are proved. A20–A22 are proved in their recorded domains; the chronological-to-full-ambient transport is now proved and independently audited.
2. Finish review/integration of the new A53 full-forest source-route consumer, and retain the literal L13 filtration issue. A47/A51/A52 now have proved corrected full-forest constructions and actual conditional formulas. A40–A43, including the source conditional moment route and corrected harmonic calculation, are now proved.
3. Complete every other open named or substantive inventory obligation, including retained source proof steps and the literal L13 filtration issue. P01 and C01 are proved; their class encodings, count and exact Bernoulli normalization are audited.
4. Complete the retained literal SIR reverse arguments and related auxiliary claims. Both rate branches of A65 and the complete original fixed-word tree/count-prefix adapter A66 are proved, with scoped independent audits. Every T06/T07 limit is proved for the embedded and given full-contact source models. The literal reversed-walk arguments, same-epsilon capture coefficient and other retained source claims remain open.
5. Resolve source corrections without silently certifying false printed claims; reconcile the full inventory and repeat the omission scan before asserting complete coverage.
6. Obtain successful Linux Comparator and required independent-kernel evidence for a fixed publication snapshot. A Palomar candidate additionally needs a public GitHub commit and a passing complete official mechanical report.

The current result is a **partial, checked development**, not completion of the
user's requested whole-paper formalization or a verified final Palomar candidate.

Report structure adapted from the supplied [template](.agents/templates/FORMALIZATION_REPORT.md); see its [attribution](.agents/skill-notices/lean-palomar-skills-updated/ATTRIBUTION.md).

## T02 completion milestone

`MainGeometricLimit.lean` proves the Introduction's literal iid-sign result
for every $p\in[0,1)$ on the actual annealed history. The limit is the
chronological ordering-and-erasure of the actual labelled local limit. Its
law equals the concrete iid geometric-offspring construction with mass
$(1-p)p^k$, and its full conditional family of child subtrees has the
Bienaymé product law. Extinction and $p=0$ require no extra premise.

The finite chronological rank map is injective, preserves height, and commutes
with both genuine transitions. Its complete path pushforward is the plane
Markov chain, rather than merely an agreement of marginal laws. The first-child
and remainder graft has the actual split kernel; global fairness holds on all
raw states. L06 gives two independent complete extracted paths. The clock
transfer handles a coordinate selected finitely often by the exact repeat-last
convention. Its joint limit gives the true graft-chain weak limit. The exact
first-step mixture and uniqueness of weak limits yield the actual-law fixed
point used by L05. No independence, fairness, or convergence assumption remains
in the T02 export.

Substantive proof departures are retained: direct annealed freezing hazards
$(1-p)/(n+1)$ and harmonic survival products establish convergence without the
source's extinction/drift split; true Markov avoidance recursion establishes
fairness without conditioning on the entire future active-count path; L06 uses
harmonic cylinder completion and dominated convergence instead of the printed
asynchronous conditional factorization. The final fixed-point/finite-rectangle
argument avoids conditioning on a null positive-degree event at $p=0$. These
routes establish T02; they do not certify the bypassed manuscript calculations.

Current evidence:

- `verification/build.log`: full default build **PASS**, 4,228 jobs.
- `verification/axioms.log`: **PASS**, 4,256 namespace declarations, only the
  three permitted axioms.
- `verification/MainGeometricLimitStatements.lean` and its log: **PASS**, seven
  independently reconstructed source statements and sixteen axiom closures,
  including explicit iid prefix mixtures, actual finite-ball convergence,
  concrete iid offspring/pruning, the all-child branching law, and $p=0$.
- `verification/ForwardPlaneProjectionStatements.lean` and its log: **PASS**,
  eight expanded source/dependency statements and sixteen closures.
- `verification/InterleavedChainsStatements.lean` and its log: **PASS**, the exact
  L06 transition/extraction/product statements and eleven closures.

T02 has no unresolved proof obligation in its advertised statement. The open
whole-paper rows above, the literal source arguments identified here, and the
publication comparison/kernel requirements remain unresolved. No current
Comparator or Palomar acceptance is claimed.

## Embedded SIR and auxiliary fluid milestone

The source and full inventory are unchanged. The new scoped independent review
is [verification/SIR_EMBEDDED_AUDIT.md](verification/SIR_EMBEDDED_AUDIT.md),
with expanded exact-type examples in `verification/SIRLocalLimitStatements.lean`.
Both source rate ratios, the true terminal horizon, geometric parameter,
finite extinction, and actual root-degree pushforward were checked.

`SIRCounts`, `SIRCountLaw`, `SIRTreeState`, `SIRTreeLaw` and `SIRAbsorption`
construct actual stopped Markov histories, with one initial infectious root
and $n$ susceptible individuals. Legal events decrease $2U+I$ before
extinction, so the complete tree state has been absorbed and held by $2n+1$.
The infection-tree path projects exactly to the count path. Impossible
infections at $U=0$ have zero probability.

`MainSIREmbedded` proves both local conclusions for this actual embedded
model. It uses adaptive finite-word probability laws and exact uniform
finite-prefix event comparison. Frozen balls transfer that comparison to the
complete terminal tree, including finite extinction. In the strong-rate
regime, actual root degree escapes all finite bounds, directly excluding
tightness. This checks the conclusions through different routes; the printed
unstopped-walk and Skorokhod shortcuts are not certified. The independent
physical Poisson/exponential-history identification remains open in A65/A66.

`SIRSusceptibleLaw`, `SIRSusceptibleConcentration` and `SIRSusceptibleFluid`
prove actual uniform compact-time susceptible and integer infectious limits
for general rates $n\lambda_n\to\lambda>0$. The centered increments have
proved zero kernel mean and exponential moments. Chernoff and finite-union
bounds make the true noise uniformly negligible. A deterministic past-sum
Grönwall estimate retains the parameter error and the uniform Euler remainder.
This replaces the false future-maximum criterion S18 and the uncorrected
substitution in S13; the source Doob argument is bypassed.

`SIRStoppedCoupling` constructs a genuine joint full path, whose two complete
marginals are exactly `countsFullLaw` and `Susceptible.fullLaw`. Agreement and
the integer infectious identity hold through the first extinct state.
Agreement after extinction is not asserted. The early-survival probability and the stopped weak path-law mixture are now proved in `SIREarlyExtinction` and `MainSIRFluid`; see the later milestone below.

Current integrated evidence is `verification/build.log` (4,228 jobs),
`verification/axioms.log` (4,256 declarations, three permitted axioms), and
`verification/sir-local-limit-statements.log` (expanded independent statements
and twenty permitted closures). The focused SIR build logs are also retained.
These are Lean compilation and axiom checks, with independent automated source
review; they are not Comparator success or independent kernel replay.

## Strong SIR fluid and analytic milestone

`SIRStrongCounts.countsFullLaw_strong_uniform_tendsto` proves the literal
uniform error probability on the entire real interval $[0,2]$, for the actual
stopped embedded count history, whenever $n\lambda_n\to\infty$.
The initial infectious count is $1$, the scale is $n$, and floor-time rounding
is proved negligible. No conditional survival or iid sign assumption appears.
A true-kernel exponential superharmonic bound controls early absorption;
expected missed infections include post-extinction held steps. Their exact
count identity bounds the susceptible population. A deterministic triangle
estimate controls all later times. This proves the embedded conclusion of
T07.II.a, bypassing the printed random-walk coupling. The relative startup estimates have since been proved in `SIRStartup`; all SIR height statements remain obligations.

The independent exact-type/source audit and eleven permitted closures are in
`verification/SIRStrongCountsStatements.lean`,
`verification/sir-strong-counts-statements.log` and
[verification/SIR_STRONG_FLUID_AUDIT.md](verification/SIR_STRONG_FLUID_AUDIT.md).
The stopped finite-rate shared-gate approximation, its precise order of limits
and the concavity proof departure are recorded separately in
[verification/SIR_STOPPED_FLUID_AUDIT.md](verification/SIR_STOPPED_FLUID_AUDIT.md).
The gate's limiting probability and final path-space law have since been proved; see the later finite-rate milestone.

`SIRLambertW` proves the explicit formula using the actual principal inverse
on $[-1,\infty)$, including the closed real domain, endpoint and derivative at
zero. The quotient derivative excludes zero and the branch endpoint. The
formula is proved by exponentiating the verified implicit profile equation,
rather than by substituting the Lambert derivative into a second ODE.
Its independent audit is
[verification/SIR_LAMBERT_AUDIT.md](verification/SIR_LAMBERT_AUDIT.md), with
`verification/SIRLambertWProbe.lean`. The positive-profile uniqueness class
remains explicit.

The expanded integrated default build passes 4,228 jobs; the current global
axiom check passes all 4,256 namespace declarations using only the permitted
three axioms. Separate current build evidence also exists for the absorbed
biased walk and its exact limiting extinction probability, and for its
full-path active-count projection. Those newer source obligations are still
being integrated and reviewed. No publication or upload has occurred.

## Finite-rate SIR shared-survival fluid milestone

`MainSIRFluid.embedded_sir_fluid_limit_of_source_ratio` proves the source
T07.I.a conclusion for the actual constructed embedded population model.
The `PopulationPath` carrier includes discontinuous step paths. Its topology
is proved equivalent to uniform convergence on every compact subset of
nonnegative real times. The measurable finite-prefix encoding at $2n+1$
equals the actual uncapped stopped path almost surely at every time.

The target is `geometricSurvivalPathLaw`: draw one concrete iid geometric
Bienaymé tree, then use its survival event for the entire path
$\max(2-2g_\lambda(t)-t,0)\mathbf1_A$. The same event is shared by all times;
its probability is derived rather than assumed. `PlaneFiniteExtinction`
proves that finiteness of the complete Ulam--Harris vertex set is equivalent,
along the actual plane chain, to reaching empty activity. The genuine
absorbed biased-walk harmonic exponential and a contracting masked
exponential give extinction probability $1/\lambda$. Fixed-prefix
convergence and a true SIR-kernel superharmonic bound give the matching
two-stage early survival probability. The generic numerical mixture is
proved equal to the concrete Bienaymé-survival path law.

The final weak convergence is proved through all bounded continuous tests.
Continuity at its two possible limit paths, the actual shared-gate uniform
approximation and the derived gate probability give convergence of the true
path-law integrals. No survival, independence, noise-convergence or weak-limit
premise is added. This route bypasses Skorokhod representation; it does not
certify that source argument. The direct exponential method for walk ruin
also bypasses the printed walk-coupling/extinction shortcut.

Independent expanded source review is recorded in
`verification/SIR_FLUID_MIXTURE_AUDIT.md` and the exact examples in
`verification/SIRMainFluidStatements.lean`. The whole-tree survival and
actual early-gate examples are in `verification/SIRSurvivalStatements.lean`.
The focused `main-sir-fluid-build.log` passes; current integrated evidence is
`verification/build.log` (4,228 jobs) and `verification/axioms.log` (4,256
namespace declarations, only the three permitted axioms).

Both T07 fluid conclusions are therefore proved for the embedded model.
The physical preassigned-clock/Poisson-process identification remains open,
as do the SIR height, distance, maximum-height and other whole-paper rows.
No full-paper coverage or verified publication candidate is claimed.

## Startup, full terminal mixtures and forward late-phase bounds

`SIRStartup` and `SIRStartupQuantitative` now supply the genuine relative
startup inputs, including the literal logarithmic cutoff and the exact
same-$\varepsilon$ auxiliary window/error claim. Actual exponential noise
bounds summed over all times after a diverging cutoff replace a random-walk
law-of-large-numbers coupling. The stopped transfer uses the actual joint
history and its complete marginal identities, including first extinction.

The terminal-tree mixture now uses the original fixed-sign forward laws at
arbitrary horizons, including $2n+1$, with actual adaptive sign-word weights
and proved almost-sure feasibility. It retains absorption. This is more than
the earlier capacity-free fixed-prefix comparison, but it is not by itself a
joint-law theorem about all earlier counts; that history transport remains
separate during the next height-transfer step.

`SIRLateInfectionProbability` proves uniform decay of the true late infection
probability by a forward accumulated-pressure/noise contradiction.
`SIRLateHarmonic`, `SIRLateReciprocalBudget` and `SIRLateAttachmentBudget`
prove a forward harmonic potential estimate under the actual future chain.
Starting from a state with infection probability at most
$\varepsilon<1/2$, expected reciprocal population cost is at most
$H_I/(1-2\varepsilon)$ and expected actual pre-birth attachment charge is at
most $\varepsilon H_I/(1-2\varepsilon)$. These are true-kernel estimates;
no reversed path conditioned on future extinction is used. The final global
late-sum and height consequences are still being integrated. The printed
reverse coupling and its auxiliary claims remain explicit obligations.

The static preassigned-clock construction now samples one independent array
once, evolves that same array at every event, and has verified measurable
clock selection, population validity and absolute-event times. This does not
yet prove its embedded history law agrees with `treeFullLaw`. Dynamic residual
identities and their probability invariant, followed by the Poisson
first-arrival identification, remain the physical A65/A66 bridge.

At that startup/late-budget checkpoint, the expanded default build passed 4,228 jobs and the global axiom audit checked 4,256 declarations with only the three permitted standard axioms. Focused direct and axiom logs for startup,
terminal-word mixtures and late infection pressure are retained in
`verification/`. That earlier checkpoint preceded the strong terminal geometry milestone below; physical-history identification remains open.

## Strong-regime terminal SIR geometry milestone

All three T07.II.b conclusions are proved for the constructed embedded
model. `MainSIRUniformSamplesStrong` gives terminal uniform height and the
distance of two conditional independent uniform vertices, divided by
$\log n$, tending to $1$ and $2$. `MainSIRStrongMaximum` gives terminal
maximum height divided by $\log n$ tending to $e$. These observe the actual
tree at event $2n+1$, after the proved absorption horizon, and require only
$n\lambda_n\to\infty$. The exact source ratio hypothesis is also checked.

The deterministic T04 application is justified uniformly over finite good
profiles. A diagonal insertion argument fills unselected rows with a proved
balanced schedule and rules out bad increasingly accurate environments.
The actual adaptive full count-prefix law, rather than an assumed iid sign
law or marginal convergence, supplies the required relative profile.
Chronological coordinates preserve heights and graph distances. The
conditional uniform laws include all vertices, with frozen vertices and
the pair diagonal retained.

Terminal sampling is compared with the time-$n$ samples along the same
forward history. The single-sample error is bounded by the missing vertex
fraction, and the independent-pair error by twice that fraction. Exact
feasible-word population identities and $U_n/n\to0$ show these errors vanish.
The maximum proof instead combines its exact earlier truncated marginal
with a negligible late cut maximum. Genuine forward harmonic budgets give
the post-$n$ attachment charge; the forward exponential sum bounds the cut
maximum, including the actual extinction step and words extinct before the
cut. This replaces the printed reversed-walk/Bennett route. Its unchecked
auxiliary assertions remain in A84–A87.

The independent source/statement review is
`verification/SIR_STRONG_GEOMETRY_AUDIT.md`; the exact expanded terminal
examples in `SIRStrongGeometryStatements.lean` pass with seventeen standard
axiom closures. The complete default build passes 4,271 jobs, and the
refreshed global audit passes 4,695 namespace declarations, only the three
permitted axioms. These are current local Lean checks, not Comparator or
independent-kernel evidence.

For finite rates, `SIRSublinearExtinction` proves extinction probability
$1/\lambda$ at every diverging sublinear cutoff. The actual early-extinct
tree is held, so its terminal height is at most the cutoff.
`SIREarlyTerminalSampling` makes its entire uniform-height and pair-distance
contribution negligible at a sublogarithmic cutoff. The literal log-log
cutoff is included; these helper checks are labelled self-review.
Near-extinction capture with the cutoff chosen according to tolerance is
proved separately in `SIRFiniteRateCapture` and
`SIRFiniteRateSamplingCapture`. The same-$\varepsilon$ coefficient printed
in A77 is not certified. The full finite-rate height/distance mixture still
requires the surviving branch and its joint earlier-gate/later-tree law.

The physical clock work now proves the actual positive-rate static-array
residual product and event-word probabilities after every finite history in
`SIRClockPrefixLaw`. The array is sampled once; newly activated rows are
the original unused clocks. No conditional memorylessness or independence
invariant is assumed as a premise. Event-word/kernel transport and the
Poisson-contact identification remain explicit obligations. No upload,
whole-paper completion or verified final publication candidate is claimed.

## Finite-rate weak mixtures and full physical contact milestone

`MainSIRUniformSamplesFinite` completes both T07.I.b conclusions. The
height and independent-pair distance laws are the exact terminal conditional
sampling laws divided by $\log n$. Their limits are the constants
$\lambda/(\lambda-1)$ and $2\lambda/(\lambda-1)$ on the same concrete
geometric Bienaymé survival event, and zero otherwise. The full joint
count/tree-prefix mixture retains the early gate and later observation
on the same actual history. A proved comparison replaces the diverging
sublinear gate by any prezero fluid-time gate. The early-extinct terminal
contribution is negligible; surviving-prefix T04 estimates and actual
near-extinction capture give the other branch. All convergence and profile
inputs are discharged from the genuine adaptive process.

Finite families of near-origin and bulk constraints, followed by a diagonal
bad-row argument, replace Skorokhod representation. The exact subset law
compares uniform samples along a single forward history, preserving old
heights/distances and both pair cases. It replaces the printed birth-time
shortcut and does not certify its same-$\varepsilon$ coefficient. The scalar
weak convergence follows through bounded continuous tests, with no assumed
weak limit or survival probability. Independent final-assembly review is
in `verification/SIR_FINITE_MAIN_WEAK_AUDIT.md`; the authored geometric
inputs are explicitly distinguished from that independent review.

`SIRPoissonFirstArrival` derives first-contact exponential laws from the
given whole-process counting marginals. `SIRClockPrefixLaw` and
`SIRClockWordKernel` derive the original array's residual and whole event-
history laws. `SIRClockTreeProjection` proves the actual source/recipient
sums give the existing tree kernel. `SIRPoissonFullContacts` recomputes the
next point of each entire live contact path; the future-live invariant
identifies its entire frame history with the static-array history.
`SIRPoissonFullContactLaw` consequently proves the actual genealogy/count
path laws, finite absorption and terminal law from source process data.

`SIRPhysicalLimits` and `SIRPhysicalFiniteLimits` transfer every T06/T07
conclusion to that full-contact protocol. The source-data bundle contains
only measurability, independence, rate-one recovery laws and Poisson
counting marginals. It assumes neither an embedded law nor a convergence
estimate. Those source conditions are needed only eventually, and eventual
positive intensity is derived from the exact source rate assumptions.
The standalone zero-rate/no-arrival carrier extension remains distinct
from these asymptotic main conclusions. Existence of the supplied Poisson
process law is source input; it is not constructed in this development.

Independent physical source review and exact expanded probes are recorded
in `verification/SIR_PHYSICAL_HISTORY_AUDIT.md`,
`SIRPoissonStatements.lean` and `SIRPhysicalSourceStatements.lean`. The
that checkpoint passed 4,304 build jobs and 5,257 namespace axiom closures.
The subsequent combinatorics and source-argument milestone below supersedes
its remaining-work list; no whole-paper coverage or final
publication verification is claimed.

## Combinatorics and source-argument milestone — 30 October 2026

P01 and C01 are proved for the actual unordered source classes. Canonical
representatives are constructed and unique. The finite class is genuinely
finite; a largest-label growth bijection proves its weighted polynomial
recurrence. The real tangent derivative characterization is local where the
cosine is nonzero, and the formal exponential/Bernoulli identity proves the
exact coefficient formula. Taking norms supplies the absolute Bernoulli
number without a sign premise. This replaces the externally cited counting
argument by a direct proof. The integrating agent independently reviewed the
finite counting and norm/factorial inputs; their author independently reviewed
the root-owned analytic modules and final assembly. These scopes and authored
inputs are distinguished in `TANGENT_COMBINATORICS_INDEPENDENT_AUDIT.md` and
`TANGENT_ANALYTIC_AUDIT.md`. The final probe passes nine reconstructed general
and boundary statements and sixteen permitted axiom closures.

A28 now includes actual raw iid extinction, the critical endpoint, strong-law
drift, freezing density, the source T01 argument on nonextinction and unique
increasing reindexing of the actual unordered trees. A40–A43 now check the
paper's random-birth mean argument itself: genuine independent Bernoulli
representation and conditional mean, exact rounded birth tails, corrected
strict harmonic inequality, conditional Bennett/layer-cake formulas, finite
dominating tail integrals, control of rare small means and every source real
power. The final consumer has the exact original uniform-height assumptions
and actual forward conditional uniform law. The literal inclusive equality
and intermediate harmonic sum remain false and explicitly corrected as S21.
The mean-limit proof uses a stronger bulk-only fractional-cutoff route; the
corrected printed harmonic inequality is also checked separately.

Both physical rate branches of A65 and all complete original-forward joint
prefix observations in A66 are proved. Zero intensity is represented by
genuinely absent points, forced by zero Poisson count laws. Its sole recovery
occurs at the actual positive exponential lifetime, then the full frame holds.
The optional next-event protocol agrees pointwise with the positive-path
protocol on injected arrival paths. Separate independent physical-history,
zero-branch and full joint-prefix audits pass, including observations at an
index selected from the same counts.

Current default integration passes 4,404 jobs; the global namespace audit
passes 5,972 declarations, with only `propext`, `Classical.choice` and
`Quot.sound`. The unchanged source inventory is retained. Subsequent work is
on generic topology A20, full degree/freezing and conditional attachment
arguments A21–A22, and complete conditional forest/matching formulas
A47/A51/A52. These and all other open rows remain obligations. No whole-paper
coverage, current Comparator/kernel replay or final Palomar verification is
claimed, and no upload has been performed.


## Earlier degree, active-height and forest milestone — 30 October 2026

A21/A22 now check the geometric degree criterion and the corrected source
conditional-independence/Borel–Cantelli argument themselves. The deterministic
equivalence needs no freezing premise. Joint finite selection patterns and
infinite survival are derived from the actual kernels, then normalized;
null conditioning is handled by restriction. Every occurring vertex, the root
and absorbed schedules are covered. S04 records both the pre-step denominator
and strict post-birth endpoint, with actual formal counterexamples. The
printed attachment density and reciprocal divergence are also proved, using
the previously verified height-scale lower bound for divergence.
The independent review/probe is
`verification/A21_A22_INDEPENDENT_AUDIT.md`: five reconstructed examples and
six standard axiom closures. The separate authored probe has eight examples
and fourteen closures. T01's original alternative proof remains unchanged.

A33 now follows the source's exact independent Bernoulli representation and
Bennett concentration. The product has heterogeneous parameters $1/S_i$;
only the summed coordinates carry the attachment mask. Actual conditional
uniform-active sampling, strict survival, all varying rows, positive mean
bounds, uniform moments and all finite real source exponents are verified.
`verification/A33_ACTIVE_HEIGHT_AUDIT.md` independently checks the scope,
with ten reconstructed examples and ten standard closures. A34 now also verifies the actual layer-cake integral, split at 7, exact dilation,
real-power tail asymptotic and the source-method moment limit; a logarithmic
envelope replaces the printed repeated-integration-by-parts phrase. Its
independent five-example/eight-closure review is recorded in
`verification/A34_INDEPENDENT_AUDIT.md`. A32 separately checks the actual finite
adjacent-swap iteration, literal sorted schedule and harmonic/logarithmic chain,
with an independent nine-example/ten-closure audit.

The generic plane unlabelled and arbitrary countable plane labelled local
topologies are checked, including repeated labels and complete boundary
labels. The full arbitrary unordered-labelled realization in A20 remains
open; finite quotients alone are not counted as that realization.

The complete augmented cut forest is exchangeable after erasing old IDs,
and its joint law with the actual earlier whole tree is a product. A true
uniform permutation parametrizes every possible root bijection, including
the empty case. The exact joint reconstruction law retains both the erased
forest and the full terminal state. It does not assert mutual independence
of components. S17 distinguishes this augmented object from the paper's
bare all-star convention, which loses root freezing clocks. Its conditional
observable formulas remain retained in A51/A52.

At that milestone the default build passed 4,481 jobs and the namespace axiom check
passed 6,876 declarations with only the three permitted axioms. Further
unimported downstream modules have separate focused evidence. The unchanged
inventory remains authoritative; no whole-paper completion, current
Comparator/kernel replay, final Palomar report or publication is claimed.


## Latest source-proof milestone — 30 October 2026

The full unordered labelled ambient topology A20 is proved, with actual
rooted graph isomorphisms, all coherent towers realized, repeated labels
permitted, and a compatible complete separable metric. The independent
ten-example/ten-closure audit checks the exact positive-radius sequence
criterion. The chronological model now has a proved closed embedding into that full
ambient space, preserving every actual birth-edge and frozen/active vertex
label. Same-radius ball equivalence, coherent closed-image gluing and weak-law
transport have no added support premise. MainLocalAmbient supplies the T01
equivalences/common limit and actual iid T02 history in the full ambient.
The independent bridge probe has six examples/seven closures; the separate
authored imported probe has nine/fifteen. Generic probability transport is
reviewer-authored and retains separate provenance.

A24 now has an all-vertex degree obstruction, an increasing matching-prefix
extraction, actual pair-history couplings, positive marginal degree tails
and a finite-ball tightness contradiction. The independent nine-example/
twelve-closure audit includes the first printed limiting union identity.
A common coupling of all rows and the manuscript's final diagonal
divergence inference are not certified; the final proof uses marginal
tightness and needs no freezing-series theorem.

A27's literal nonnegative subtree expectations and normalization now have
independent review, with five expanded examples and thirteen closures.
The earlier rectangle-induction proof-order departure remains explicit.
A36's uniform threshold over every real $C\ge2$, seven-split tail method,
all real source moments and boundedness including finite initial rows are
integrated and independently checked.

A37–A38 now prove the repaired source geometric strategy through the exact
finite-maximum/nested-limit L08 conclusion. Both plus/minus count identities,
actual rational block bounds, eventual positivity and integer endpoint errors
are checked. Three false printed finite steps have actual counterexamples;
the valid last-endpoint correction vanishes under the source assumptions.
The independent probe has five expanded examples and ten closures; the
separate authored probe has nine examples and eighteen closures.

A48–A49 now have the exact positive finite index filter, including initial
$A_n\le1$, and one actual graph-ancestor chain with the source distances
and height lower bound. A52's distinct-component conditional covariance
and same-component marks are proved, including old marked roots. Together
with the earlier actual conditional mean/variance, these complete the
recorded full-forest moment scope. An independent three-example/eight-closure
source-geometry probe checks the extension.

A53 now follows the full conditional mean/variance/Chebyshev/tower route to
an actual normalized conditional probability and the uniform source window.
The true $S_a\le a+1$ gives the sufficient corrected error $3k^3/2^k$ for
large cuts. The independent final probe has two examples/seven closures;
the authored final probe has three/seven. Its final source consumer has a
focused artifact build (3,959 jobs) and is now globally integrated.
The separate base correction under A50 and root-clock loss under S17 remain
explicit.

The current completed integrated default build is 4,552 jobs and the
namespace audit checks 7,538 declarations with only `propext`,
`Classical.choice` and `Quot.sound`. Later downstream modules have focused
checks and are recorded in the continuation checkpoint until the next global
build. All source and scope inventory entries are retained. No whole-paper
completion, current Comparator/kernel replay, complete Palomar mechanical
report or final publication candidate is claimed. Uploads remain suspended.


A56 now has the exact cubic strict-Poisson tail bound for all source
parameters, the actual logarithmic polynomial scale choice, and explicit
safe-threshold treatment of every positive margin. Independent review passes
ten expanded examples/fifteen closures. The invalid real factorial and
all-margin slack statements are formally refuted under S22/S23; the older
strict-ceiling witness correction S10 is retained.

A63 now constructs the actual positive infinite extension and canonical
infinite urn, proves every finite path law, and derives the original
component endpoint concentration with the exact infinite budgets. Independent
review passes ten examples/sixteen closures. It preserves endpoint-versus-
joint-path scope and the marked-root plus-one correction. The later A64
source scalar/union route and weaker L13 premise remain separate obligations.

A84 now has a formal feasible counterexample to the printed reversed-sum
equality, together with corrected pre-step algebra and reverse population
partial sums. The reduction to the last half-window and the future-conditioned
reverse iid coupling remain open. The original forward late-sum alternative
remains proved. The latest extra word-schedule semantic lemma has a focused
build; a following global refresh will include it.


The next integrated milestone passes 4,552 default build jobs and 7,538
namespace axiom closures. A31 scalar factorizations, A64 source urn/union
route, the A85 standalone iid probability and A86 harmonic expectation
are now integrated, with their independent audits above. The first actual
Bernoulli coupling kernel and product-word helpers are integrated; later
whole-block/thinning consumers have separate focused evidence until the
next global build. The actual infinite component-path identification and
reversed SIR coupling remain explicit obligations.

## Reconciled source-argument milestone — 30 October 2026

The full unchanged source was rescanned and reconciled in
[the inventory review](verification/FULL_INVENTORY_RECONCILIATION_2026_10_30.md).
All 24 named environments, A01–A87 and Q01–Q07 remain accounted for.
Current authoritative rows supersede older present-tense milestone notes.
The complete A60–A61 source coupling, actual A63 whole component paths and
corrected A84 first-zero/last-half-window reduction now have current artifact
evidence and scoped independent audits. In particular, final source methods
are not inferred from the previously proved main conclusions.

(Historical list, superseded by the final section "Claude resumption milestone": A03, A07, A14/A16 and the A87 per-vertex domination are now proved; A06 is partial.)
Remaining mathematical obligations include the remaining extinction-conditioned finite-plane example and ordering in A03;
metric-measure non-tightness and long-dendron convergence A06; the actual
Kingman partition specialization A07; the possible intrinsic all-schedules
reachability bridge A14/A16; the weaker current-state-only L13 formulation;
genuine reversed iid
coupling/localization A85–A86; and the original A87 per-vertex conditional domination and literal
future-conditioned random-mean argument. Its corrected fixed-word Bennett
estimate and zero-charge tail are now proved. The explicit all-row/path couplings in A24/A67/A73
remain distinguished from their already proved marginal conclusions and
bypassed proof methods. Research questions and formal source refutations are
retained separately. No complete coverage or publication verdict follows.

The subsequent focused milestone closes A04 and A77, with independent scoped
reviews in [A04](verification/A04_CONDITIONED_IID_INDEPENDENT_AUDIT.md) and
[A77](verification/SIR_CAPTURE_COEFFICIENT_INDEPENDENT_AUDIT.md). A04 supplies
an exact finite-survival-conditioned joint construction; A77 supplies the
literal same-coefficient reverse-birth estimate and actual prefix capture,
including two true conditional uniform samples. The scalar and corrected
fixed-word A87 scope passes the separate
[Bennett review](verification/SIR_LATE_BENNETT_INDEPENDENT_AUDIT.md).
These checks are included in the 4,596-job integration and 7,986-declaration axiom audit of that date (historical; the current totals are 4,631 jobs and 8,618 declarations, see the final section).

## User-requested handover checkpoint

On 30 October 2026 the user requested that proof development stop for a Claude
handover. Work is stopped. [CLAUDE_HANDOFF.md](CLAUDE_HANDOFF.md) records the
verified integration, stopped worker files, exact remaining obligations and
resumption commands. At that checkpoint (historical; superseded by the final section) the default build passed 4,596 jobs and the fresh global
axiom audit passed 7,986 declarations with only the three permitted axioms.
New draft one-susceptible coupling and finite-plane foundations remain clearly
distinguished from the imported verified scope. No upload, publication,
complete paper coverage, Comparator success or Palomar deposit is claimed.

Stopped-draft precision: `FinitePlaneConditionalBounds.lean` has two known
elaboration errors and is outside the imported verified scope; the geometry
foundation alone passed its artifact build. The later one-susceptible coupling
files also remain outside the integrated scope. Their stopped notes are
[A03](verification/A03_FINITE_PLANE_HANDOVER.md) and
[A85](verification/A85_ONE_SUSCEPTIBLE_HANDOVER.md). All workers confirmed
stop. The final maintained-source text/metadata scan passes 624 Lean files;
that scan is not a compilation claim for these drafts.

## Claude resumption milestone — 30 October 2026

Development resumed on the user's request after the handover checkpoint. This section supersedes the
"stopped-draft precision" paragraph above. The default build passes 4,631 jobs
([build log](verification/build.log)); the fresh global axiom audit passes 8,618 `Freezing1` declarations, all
transitive axioms among `propext`, `Classical.choice`, `Quot.sound` ([audit log](verification/axioms.log)); the
text/metadata scan passes 648 maintained Lean files and does not certify proofs. Source hash and inventory are unchanged.
Provenance: the root authored the A03 conditioned example, A07, the A14 state-level bridge and the A87 recursion; four
delegated workers authored A03 uniform reordering, A06, the A14 encoder and the A14 decoder. The root read each worker's exported statements and re-ran every worker probe against the integrated artifacts. A separate reviewer read all five families at statement level (no blocking finding; corrections applied): [independent statement review](verification/INDEPENDENT_REVIEW_RESUMPTION_2026_10_30.md). Proof scripts were not independently audited.

**A03 (extinction-conditioned finite plane example) — proved, including uniform sibling reordering.** The stopped
`FinitePlaneConditionalBounds` draft was repaired and `FinitePlaneClass` made a reducible abbreviation. `FinitePlaneAtomMass`, `FinitePlaneUniformLaw`, `FinitePlaneExtinctionTime`,
`FinitePlaneConditionedUniform` prove the exact atom mass $(1-p)^m p^{m-1}$ of the actual limit law, the invariant
$2|V|-|A|=1+k$ along the genuine chain and hence $\{\tau=2m-1\}=\{$limit has $m$ vertices$\}$ almost surely, and
`iid_signs_conditioned_extinction_uniform_plane` (uniform law on all finite plane trees with $m$ vertices, positive probability, even times null).
`FinitePlaneShuffle*` (worker) proves the uniform independent reordering of children preserves it: `iid_signs_conditioned_extinction_uniform_plane_shuffled`.
Reviews: [self-review](verification/A03_FINITE_CONDITIONED_PLANE_SELF_REVIEW.md), [shuffle notes](verification/A03_SHUFFLE_NOTES.md); probes `A03FiniteConditionedPlaneStatements.lean`, `A03ShuffleStatements.lean` exit zero. The independent recursive-tree probe now passes.

**A06 — finite-sampling convergence and Gromov–Hausdorff non-tightness proved** (`LinearBush*`; see the A06 row). GHP itself and the identification with Janson's long dendron are not formalized. Notes `verification/A06_NOTES.md`.

**A07 — embedded Kingman jump chain proved** for the whole joint all-positive reverse history, without holding times (`KingmanPartition`, `ReverseKingman`, `ReverseKingmanHistory`; [self-review](verification/A07_KINGMAN_SELF_REVIEW.md); probe exit zero).

**A14/A16 — intrinsic union-over-schedules bridge proved, with a bijection** (`ForwardIntrinsicSupport`, `RootedForwardEncoding*`, `ForwardStateDecoding*`; see the A14/A16 rows).

**A87 — fixed-state generating-function recursion and corrected per-vertex moment bound proved; the source stochastic domination remains unproved** (`ForwardActiveHeightMgf`; see the A87 row).

**A85, one-susceptible draft modules.** `SIROneSusceptibleFirstTime`, `SIROneSusceptibleTimeCoupling`,
`SIROneSusceptibleCouplingMarginals` passed direct checks, were built and are imported. They contain the explicit noncausal time/sign coupling and its two exact marginals. The reverse-birth domination, the actual-history wrapper and the general multi-susceptible coupling are **not** done.

**Remaining open or uncertified, stated plainly.** A85–A86 (the actual reversed iid coupling and the localized comparison): no proof is known to the author; a multivariate stochastic domination of the reversed infection indicators is required, and the forward hazard bound alone is refuted as a shortcut. L13 in its literal current-state-only form: neither proved nor refuted (see `MANUSCRIPT_RECOMMENDATIONS.md` for a heuristic obstruction). The printed shifted-mean/unshifted-threshold bound and the future-conditioned random-mean argument in A87. The explicit joint couplings A24/A67/A73, whose proved marginal conclusions do not use them (bypassed methods, recorded). A06's GHP/dendron identifications as above. Final source interface, Comparator, Linux/kernel replay and Palomar remain outstanding; no upload was made and no whole-paper or publication verdict is claimed.

## Codex verification of the Claude milestone — 30 October 2026

A fresh independent review confirms successful default compilation (4,631
jobs), successful compilation of the three proof modules omitted by the
entry-point closure, and the allowed axiom closure of 8,639 namespace
declarations after importing every proof module. The usual entry-point
audit checks 8,618. New independent probes for A03, A07/A14/A16 and
A06/A87 pass 17 expanded statements and 25 closure queries in total.
The checked new results pass within their precise mathematical scope.

**Whole-paper completion is not established.** A85–A86's actual reverse
coupling/localization, literal L13, A06's GHP/dendron/topology bridges and
A87's stochastic-order/future-conditioned argument remain open. The A87
headings above have been corrected to distinguish the proved moment bound
from stochastic ordering. The explicit source coupling claims A24/A67/A73
remain separately retained. Publication is also incomplete: the comparison
list covers only 16 auxiliaries, current Comparator/NanoDa and full Palomar
evidence are missing, there is no local candidate commit, and nine Lean
verification files outside the maintained scan lack `module`.

See [the complete verification findings](verification/CODEX_REVIEW_2026_10_30.md)
for current logs, independent review provenance, concrete source/code
locations and publication-policy evidence. No mathematical implementation
or publication state was changed by this verification.

## Certification-interface preparation for the main results T01–T07 — 30 October 2026

Scope: seven theorems, twenty conclusions; **not** the whole manuscript. Details: `verification/certification/README.md`,
`MAIN_RESULTS_CORRESPONDENCE.md`, `OPEN_OBLIGATIONS.md`.

* Four Challenge/Solution interfaces (`Challenge/{LocalLimits,Heights,SameLaw,Sir}.lean`, `comparator/*.json`) cover T01–T07 with no
  omission; each Challenge reproduces the semantic definitions verbatim (no statement simplified) and has holes only at the
  Comparator targets. Independent statement reviews found no unfaithful or vacuous statement; caveats are documented.
* New proofs: non-vacuity of the physical SIR hypothesis (`SIRPoissonExistence*`); the three previously unimported proof modules
  are now part of `Freezing1`.
* Evidence kinds, kept distinct: (a) results verified in Lean: build + axiom closures; (b) local comparison and kernel replays
  (toolchain tools outside the sandbox) — not the official Comparator; (c) Palomar mechanical conformity: not obtained;
  (d) whole-manuscript coverage: not claimed. See the candidate evidence summary `verification/certification/candidate/SUMMARY.md`
  for the exact results of the final candidate.
* Unchanged open items: A85–A86, literal L13, A06 GHP/dendron, A87 stochastic domination, A24/A67/A73 couplings, and the
  false-as-printed statements L03, L04, P03 upper.

## Codex audit of the publication candidate — 30 October 2026

The isolated candidate was audited from local commit `4b3e78c`. Four independent
interface reviews found no blocking mathematical mismatch in the selected
Heights, chronological LocalLimits, canonical-observable SameLaw and physical
SIR statements. New imported probes passed 16 expanded examples and 24 axiom
closures. The full ambient local-limit bridge remains proved elsewhere in
the library rather than selected by this comparison interface; the literal
T05 isomorphism-class dictionary remains an explicit representation caveat.

The verifier scripts were repaired to propagate failures and reject stale,
incomplete or mixed-identity evidence. Eighteen regression tests pass. A real
auxiliary comparison/Lean kernel check and a small real export replayed by
six bundled checkers passed. These focused tests do not replace the unchanged
full main-result proof evidence or establish an official Linux/Palomar pass.
No mathematical implementation, interface statement, comparison target or
version pin changed. The manual Linux workflow is prepared with NanoDa
explicitly enabled, but no push, dispatch, publication or visibility change
was performed. All whole-manuscript gaps remain retained.

Details and exact logs: [Codex takeover](verification/certification/CODEX_TAKEOVER.md),
[script review](verification/certification/SCRIPT_REVIEW.md), and the four
`CODEX_AUDIT.md` interface records.

## Official standalone Linux verification — 30 October 2026

The isolated candidate at `54253ce4046e1314cf5af6aedb19a278200d168d` passed
`scripts/run-linux-checks.sh` in a private Ubuntu 24.04 VM with the pinned
Lean/Mathlib environment and Bubblewrap 0.12.0. The fresh project build passed
4,645 jobs in 1,315.705 seconds using the public dependency cache. The source
scan passed 826 Lean files; all 8,683 library declarations and the exact 26
main/support exports had only permitted axioms. All four main configurations
and the old auxiliary configuration passed the official sandboxed Comparator,
including NanoDa and Lean kernel replay. The driver confirmed the same clean
source commit/tree at the end; all nine locked dependency worktrees were clean.

This closes the standalone Linux Comparator/replay obligation for the audited
interfaces. It does not produce a full Palomar mechanical report, certify the
whole manuscript, or alter the chronological-carrier/canonical-observable
qualifications. The source, mathematical statements, semantic dependencies,
proof routes and inventory are unchanged; the prior independent source audits
remain applicable. No new manuscript argument or open mathematical obligation
is marked checked or proved by this infrastructure milestone.

The complete run took 38 minutes 55 seconds. Seventeen script tests passed on
Linux, with one expected non-Linux-host guard test skipped. An initial cache
retrieval failed for eight files and stopped preparation; a separately logged
retry succeeded. No failure was suppressed. Nothing was pushed, published or
dispatched, and no candidate remote was added. The full Palomar report and all
whole-manuscript gaps remain explicit in
[OPEN_OBLIGATIONS.md](verification/certification/OPEN_OBLIGATIONS.md).

Current identity, verdicts, reproduction commands and raw logs:
[Linux evidence](verification/certification/linux/SUMMARY.md). Documentation
and evidence added after the run do not retroactively change its checked commit.

## Public-release content review — 31 October 2026

The user authorized a review of the local candidate and its history before
publication. The input was `d52e74e`: 1,787 tracked text files, five reachable
commits and 1,590 unique reachable blobs. No credential-pattern matches,
symlinks, submodules, unwanted build artifacts or manuscript TeX were found
in that candidate history. Existing absolute local paths remain disclosed as
provenance. Apache-2.0 and the separate skill-attribution/license notices are
retained. The exact scope and checks are in
[PUBLICATION_REVIEW.md](PUBLICATION_REVIEW.md).

The Comparator badge target, citation scope, missing-source links and stale
A32 recommendation were corrected. The prior report already records the
proved adjacent-swap/sorting route; this review certifies no new paper argument.
An unsupported exact Claude model identifier was removed while retaining its
framework credit. A public paper reference was added without changing the
formalized source's SHA-256 or asserting equality to the arXiv version.
Source/target/definition/proof/dependency/toolchain/verifier bytes are unchanged
from the Linux-checked snapshot; the source inventory and all open rows remain
intact. Existing statement audits and proof evidence are reused on that basis.

Read-only GitHub inspection found additional manuscript material in the older
private repository. A visibility change there is not equivalent to publishing
this selected export. The existing repository stays private and no upload or
remote change was made. Public destination selection and the full Palomar
mechanical report remain pending; whole-paper completion is not claimed.


## Public-candidate publication checkpoint — 31 October 2026

The user authorized preservation of the old GitHub repository and its manuscript
history privately as `uniform-attachment-with-freezing-private`, publication of
the reviewed candidate at `igor-kortchemski/uniform-attachment-with-freezing`,
and four full Palomar mechanical checks at one frozen source commit. The
[publication checkpoint](verification/certification/palomar/README.md) records
this snapshot's status; it does not claim a result before execution.

The current manifest, source scan and official metadata/citation schemas pass.
All Lean statements, definitions, proofs, dependency/toolchain pins and
verification scripts remain byte-identical to the Linux-checked `54253ce`.
The follow-up source-first statement checks found no new mismatch in the main
results; prior independent findings and all representation qualifications are
retained. No new mathematical obligation or paper argument is closed here.
The scope remains seven selected theorems/twenty conclusions, with every
whole-paper inventory obligation retained. Intake and registration are separate
from the authorized mechanical checks.


## Four full official Palomar mechanical preflights passed — 31 October 2026

The public source commit `82f0ad45a60ec785a725fc419082c7d1d779b222`, tagged
`palomar-checked-2026-10-31`, passed all four full mechanical checks using pinned
pipeline `14aa8d6b3c2f14a8540605e37144560b9a00e7e7` and profile
`palomar-standard-v1`. Every report has status pass, stage complete, no errors,
and acceptance by Lean, NanoDa and con-ron. Ordinary build and axiom CI passed.
The exact source/configuration hashes, selected theorem lists, source provenance,
profile, workflow/pipeline identities and completed kernel outcomes were inspected.
Raw reports and workflow metadata are archived in
[verification/certification/palomar/](verification/certification/palomar/README.md).
The only warnings concern the preferred Challenge review size, not mandatory limits.

The initial four attempts rejected a free-text authorization input before Lean;
those reports are retained. Corrected invocations use the accepted approval
category and the same source commit. The old manuscript/history repository remains
private under its renamed `-private` suffix; the reviewed export has a distinct
public repository identity. The published proof and statement bytes, semantic
dependencies, pins and verification scripts are unchanged from the audited source.
This subsequent report/documentation commit changes no mathematics. The inherited
inventory remains intact and no new paper argument or obligation is closed.

The mechanical preflight gap is closed for the four selected interfaces only.
No registry intake, editorial decision or registration has occurred. Whole-paper
obligations, corrected false printed statements, representation qualifications and
substantive proof departures remain explicitly unresolved as previously recorded.


## User-selected publication title — 31 October 2026

The user selected the exact title **Uniform attachment with freezing**.
`project.name` in `formalization.yaml` and the software title in `CITATION.cff`
now use that title. The descriptions, source inventory, twenty selected main
conclusions, representation qualifications, proof departures and unresolved
whole-paper obligations are unchanged. A project title is not a claim that
all source assertions have been formalized.

The existing four full mechanical reports continue to identify their exact
checked source commit `82f0ad45a60ec785a725fc419082c7d1d779b222`; this metadata
change does not retroactively change those reports. The existing registry intake is also bound to that old-title snapshot. The remaining
old-title intakes are held while preparing the replacement snapshot. No proof,
statement, semantic dependency, toolchain pin or verifier configuration changes.
