# Uniform attachment with freezing

[![CI](https://github.com/igor-kortchemski/uniform-attachment-with-freezing/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/igor-kortchemski/uniform-attachment-with-freezing/actions/workflows/ci.yml)
[![Comparator](https://github.com/igor-kortchemski/uniform-attachment-with-freezing/actions/workflows/palomar.yml/badge.svg?branch=main)](https://github.com/igor-kortchemski/uniform-attachment-with-freezing/actions/workflows/palomar.yml)

Lean 4 and Mathlib formalization of *Uniform attachment with freezing* by Étienne Bellin,
Arthur Blanc-Renaudie, Emmanuel Kammerer and Igor Kortchemski
([arXiv:2308.00493](https://arxiv.org/abs/2308.00493)).
**The seven main theorems T01–T07 of the paper (twenty conclusions) are proved in Lean, with the
qualifications below, using only the axioms `propext`, `Classical.choice` and `Quot.sound`, and with
no `sorry` outside the deliberate theorem holes of the Challenge files. The rest of the paper is only
partly formalized, and the results are not yet registered in the Palomar registry.**
Statements: [`Challenge/`](Challenge) · correspondence with the paper:
[MAIN_RESULTS_CORRESPONDENCE.md](verification/certification/MAIN_RESULTS_CORRESPONDENCE.md) ·
verification: [verification/certification/](verification/certification/README.md) ·
whole-paper coverage: [FORMALIZATION_REPORT.md](FORMALIZATION_REPORT.md).

## Main results

The paper grows a random tree from a sign sequence $x=(x_i)_{i\ge1}$. Starting from one active
root, a step with $x_i=+1$ attaches a new active vertex to a uniformly chosen active vertex, and a
step with $x_i=-1$ freezes a uniformly chosen active vertex. Let $T_n(x)$ be the tree and $S_n$ the
number of active vertices after $n$ steps, $\tau$ the first time $S$ vanishes, and $h_n^+=\sum_{i\le n}\mathbf 1_{x_i=+1}/S_i$.
The formalized text is the manuscript `attachement-uniforme-1-final.tex`, identified by its
SHA-256 in the [report](FORMALIZATION_REPORT.md) and not included here; its equality with a given
arXiv version has not been checked. All Lean names below are in the namespace `Freezing1`.

| Paper | Lean declarations | Statement |
| --- | --- | --- |
| T01 `thm:cvlocale` | [`local_convergence_equivalences`, `local_convergence_common_limit`](Freezing1/MainLocalLimit.lean) | If $x^n\to x$ coordinatewise and $\tau(x)=\infty$: $T_n(x^n)$ converges locally in law $\Leftrightarrow$ $T_n(x)$ converges locally a.s. $\Leftrightarrow$ $\sum_i\mathbf 1_{x_i=-1}/S_i(x)=\infty$; the limit is $T_\infty(x)$. |
| T02 `thm:BGW` | [`ForwardAnnealed.iid_signs_geometric_local_limit`](Freezing1/MainGeometricLimit.lean) | For iid signs with $P(x_i=+1)=p\in[0,1)$, $T_\infty$ exists a.s. and, as a plane tree, is a Bienaymé tree with offspring law $(1-p)p^k$. |
| T03 `thm:height` | [`uniform_active_height_tendsto_Lp`](Freezing1/MainHeight.lean), [`maximum_height_window_tendsto_one`, `maximum_height_tendsto_Lp`](Freezing1/MainMaximum.lean) | The height of a uniform active vertex over $h_n^+$ tends to $1$ in every $L^p$; $\mathrm{Height}(T_n)/h_n^+\in[1-\varepsilon,e+\varepsilon]$ with probability tending to $1$, and tends to $1$ in $L^p$ if $\log n=o(h_n^+)$. |
| T04 `thm:lineaire` | [`linear_heightScale_tendsto`](Freezing1/MainLinearHeightScale.lean), [`linear_uniform_height_tendsto_Lp`](Freezing1/MainLinearUniformHeight.lean), [`linear_uniform_distance_tendsto_Lp`](Freezing1/MainLinearDistance.lean), [`linear_maximum_deviation_tendsto_zero`](Freezing1/MainLinearMaximumLower.lean) | In the linear regime ($S_i\approx ci$, $0<c\le1$), after division by $\log n$: $h_n^+\to\frac{c+1}{2c}$, uniform-vertex height $\to\frac{c+1}{2c}$ and two-vertex distance $\to\frac{c+1}{c}$ in $L^p$, maximum height $\to\frac{c+1}{2c}f(c)$ in probability. |
| T05 `thm:samelaw` | [`CanonicalTree.construction_laws_eq`](Freezing1/ConstructionEquivalence.lean) | The forward construction and the reverse growth–coalescence construction have the same law for every $0\le n\le\tau$. |
| T06 `thm:SIRlocallimit` | [`SIR.physical_sir_geometric_local_limit_of_source_ratio`, `SIR.physical_sir_not_tight_of_source_ratio`](Freezing1/SIRPhysicalLimits.lean) | The SIR infection tree converges locally in law to a Bienaymé tree with offspring law $\mathcal G(1/(1+\lambda))$ if $\lambda_n\sim\lambda/n$, and is not tight if $\lambda_n\gg1/n$. |
| T07 `thm:SIR` | seven `SIR.physical_sir_*` theorems in [`SIRPhysicalLimits`](Freezing1/SIRPhysicalLimits.lean) and [`SIRPhysicalFiniteLimits`](Freezing1/SIRPhysicalFiniteLimits.lean) | Fluid limits of the infectious population; after division by $\log n$, height and distance tend to $\frac{\lambda}{\lambda-1}$ and $\frac{2\lambda}{\lambda-1}$ on the survival event if $\lambda_n\sim\lambda/n$, $\lambda>1$, and height, distance and maximum height tend to $1$, $2$ and $e$ if $\lambda_n\gg1/n$. |

Here $f(c)>1$ is the unique root of $f(\log f-1)=(c-1)/(c+1)$. The twenty conclusions, their exact
hypotheses and the extra targets are listed in the
[correspondence record](verification/certification/MAIN_RESULTS_CORRESPONDENCE.md).

Qualifications: T01 and T02 are stated on the closed subspace of chronologically labelled trees
containing every $T_n(x)$; the unrestricted versions `source_local_convergence_*` are proved in
[`MainLocalAmbient`](Freezing1/MainLocalAmbient.lean) but not compared. T05 is stated for a canonical
observable whose correspondence with isomorphism classes is argued in a review, not proved in Lean.
T06 and T07 concern the full-contact SIR model driven by `SIR.PoissonSIRData`, whose satisfiability is
proved (`SIR.PoissonSIRData.exists_data`). The proofs of T01, T03, T04, T06 and T07 follow other
routes than the paper's, whose arguments they do not validate. The report records 25
[source issues](FORMALIZATION_REPORT.md#source-issues-and-obligations-that-cannot-be-certified-literally):
three printed results are false as stated (L03, L04, upper half of P03), their corrected versions are
proved, and none enters T01–T07 ([errata](MANUSCRIPT_RECOMMENDATIONS.md)). Not formalized: A85–A86,
the literal L13 (proved only under a stronger path-law hypothesis), the GHP and dendron parts of A06,
the stochastic domination of A87 and the explicit couplings of A24, A67 and A73
([open obligations](verification/certification/OPEN_OBLIGATIONS.md)).

## Where to start

- [`Challenge/LocalLimits.lean`](Challenge/LocalLimits.lean) (T01–T02),
  [`Challenge/Heights.lean`](Challenge/Heights.lean) (T03–T04),
  [`Challenge/SameLaw.lean`](Challenge/SameLaw.lean) (T05), [`Challenge/Sir.lean`](Challenge/Sir.lean)
  (T06–T07): self-contained files importing only Mathlib, which reproduce with docstrings every
  definition the statements use and state the results with `sorry`. `Solution/*.lean` imports the
  proofs; [`comparator/*.json`](comparator) lists the 75 compared targets, namely the twenty
  conclusions and supporting targets that pin the model and show its hypotheses can be met.
- [`Freezing1.lean`](Freezing1.lean) imports the proof library; [docs/MODULES.md](docs/MODULES.md)
  maps the main modules.
- [`Challenge.lean`](Challenge.lean), [`Solution.lean`](Solution.lean) and
  [`comparator.json`](comparator.json) form a separate auxiliary interface for 16 supporting results
  (Bennett concentration, the lower bound on $h_n^+$, counting identities). It states no main result,
  and its Challenge contains complete proofs copied from the library rather than holes.

## Verify

Install Lean with the [Lean setup guide](https://leanprover-community.github.io/install/project.html);
Lean and Mathlib are pinned to v4.35.0 in `lean-toolchain` and `lake-manifest.json`. Do not run
`lake update`. Then:

```sh
git clone https://github.com/igor-kortchemski/uniform-attachment-with-freezing.git
cd uniform-attachment-with-freezing
git checkout palomar-checked-2026-10-31   # optional: the snapshot checked by Palomar
lake exe cache get                        # download compiled Mathlib
lake build                                # Freezing1, Challenge and Solution
lake env lean scripts/AxiomAudit.lean     # axioms of every Freezing1 declaration
lake env lean scripts/MainResultsAxioms.lean
```

`lake build` reports `declaration uses sorry` only for the Challenge targets. To browse the proofs,
open the folder in VS Code with the Lean 4 extension. On Linux, with Bubblewrap installed as in
[comparator.yml](.github/workflows/comparator.yml), `lake comparator --config comparator/heights.json`
compares one interface; `scripts/run-linux-checks.sh OUT` (`OUT` a new directory outside the
checkout) builds, audits and compares all five configurations with NanoDa enabled.

CI ([ci.yml](.github/workflows/ci.yml)) runs on every push to `main` and every pull request: it scans
the Lean sources (module headers, file size, forbidden constructs, `sorry` only in Challenge files),
tests the verification scripts, builds the project and checks the axioms of the whole namespace and of
the 26 exported names. The Comparator badge shows the latest run of
[palomar.yml](.github/workflows/palomar.yml), the official Palomar full mechanical preflight, which
checks one interface per run with the sandboxed Comparator. On 31 October 2026 all four interfaces
passed this preflight at commit `82f0ad4` (tag `palomar-checked-2026-10-31`), accepted by the Lean,
NanoDa and con-ron kernels, and CI passed on the same commit
([reports](verification/certification/palomar/README.md)). On 30 October 2026 the official sandboxed
Comparator with NanoDa also passed the four interfaces and the auxiliary one at commit `54253ce`
([Linux evidence](verification/certification/linux/SUMMARY.md)). No Lean file, Lake file or
Comparator configuration has changed since the tag.

## How it was made

The formalization was produced with Codex and Claude Code agents (exact model versions are not
recorded), using parallel proof workers and separate automated reviewers. A reviewer inventoried the
paper's results before reading the Lean proofs. Each Challenge file was checked against the manuscript
by an agent that had not written it and did not read the proofs, then audited again by Codex
(`verification/certification/*/INDEPENDENT_REVIEW.md` and `CODEX_AUDIT.md`); no unfaithful or vacuous
statement was reported. No human line-by-line review of the statements or proofs is claimed.

## License and citation

The Lean code and the original documentation are licensed under [Apache-2.0](LICENSE); this does not
cover the paper, which is not distributed here (see [NOTICE](NOTICE)). The formalization is maintained
by Igor Kortchemski. Cite the paper for its mathematics, and [CITATION.cff](CITATION.cff) for this
formalization. Report problems through GitHub issues; pull requests should keep the pinned versions and
the compared statements, update the [report](FORMALIZATION_REPORT.md), and pass CI.
