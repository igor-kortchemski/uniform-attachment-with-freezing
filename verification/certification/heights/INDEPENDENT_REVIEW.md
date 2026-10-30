# Independent review of `Challenge/Heights.lean` (T03 and T04)

Reviewer: independent subagent (wrote none of the Challenge, Solution or proofs), 30 October 2026.
Method: `lean-statement-audit`; manuscript read first, Lean second; read-only except this file.

Identity reviewed: manuscript SHA-256 `88953dd8...ab00df` (re-computed, unchanged);
`Challenge/Heights.lean` 389 lines, 17421 bytes, SHA-256 `a5bfa8a8...086fa0`; `Solution/Heights.lean`
`e79229ab...8cf3`; `comparator/heights.json` `5b86465d...ccb5`; `leanprover/lean4:v4.35.0`. File mtimes
(13:58:24 and 13:58:51) precede the diagnostic run (13:59:23 local) and nothing under `Freezing1/` is newer than
`run.log`, so the evidence refers to the files reviewed here.

## 1. Verdict

No blocking finding. All seven main statements and both pinning theorems state what the manuscript states.
The caveats are documentation and evidence packaging, not mathematics.

| # | Lean declaration (Challenge line) | Manuscript | Verdict |
| --- | --- | --- | --- |
| 1 | `uniform_active_height_tendsto_Lp` (303) | `thm:height` (I), tex 297-300 | faithful |
| 2 | `maximum_height_window_tendsto_one` (311) | `thm:height` (II), tex 302-304 | faithful |
| 3 | `maximum_height_tendsto_Lp` (321) | `thm:height` (III), tex 305-308 | faithful |
| 4 | `linear_heightScale_tendsto` (332) | `thm:lineaire` (I), tex 323 | faithful with caveat (F1, F2) |
| 5 | `linear_uniform_height_tendsto_Lp` (345) | `thm:lineaire` (II) height, tex 326-332 | faithful with caveat (F1, F2) |
| 6 | `linear_uniform_distance_tendsto_Lp` (361) | `thm:lineaire` (II) distance | faithful with caveat (F1, F2) |
| 7 | `linear_maximum_deviation_tendsto_zero` (376) | `thm:lineaire` (III), tex 335-339 | faithful with caveat (F1, F2) |
| 8 | `linearHeightFactor_existsUnique` (253) | "unique solution with $f(c)>1$", tex 337-339 | faithful |
| 9 | `linearHeightFactor_spec` (289) | same | faithful |

"Caveat" means only: the file does not tell the reader that `limsup`/`liminf` in $\mathbb R$ are genuine (they
are, 3.1) nor that the array hypotheses are satisfiable (they are, section 4). I checked both.

## 2. Manuscript reconstruction (tex only, before reading Lean)

Model (tex 244-262, 424-436). $\mathbf x\in\{-1,+1\}^{\mathbb N}$, $S_0=1$, $S_n=1+\sum_{i\le n}x_i$,
$\tau=\inf\{n\ge1:S_n=0\}$. Algorithm 1: one active root. At step $n$, if no active vertex then $T_n=T_{n-1}$;
else $V_n$ is uniform among the active vertices of $T_{n-1}$ (fresh independent choice each step); $x_n=-1$:
$V_n$ freezes; $x_n=+1$: a new active vertex is attached to $V_n$. Frozen vertices stay in the tree; $S_n$ = number
of active vertices. $\mathsf H(u)$ = graph distance to the root (tex 576); $\mathsf{Height}(T)$ = maximal vertex
height. $h_n^+=\sum_{i=1}^n \mathbf 1_{x^n_i=+1}/S^n_i$.

Standing assumption (tex 285-287): rows $\mathbf x^n$ with $\tau(\mathbf x^n)>n$, $T_n:=T_n(\mathbf x^n)$,
$S^n_k$ for $0\le k\le n$. It is inherited by `thm:lineaire` and needed for $h^+_n$ to be defined; since $S$ moves
by $\pm1$ from 1, $\tau>n$ means $S^n_i\ge1$ for all $i\le n$.

`thm:height`. (I) $U^n$ uniform among the **active** vertices of $T_n$: $\mathsf H(U^n)/h^+_n\to1$ in $L^p$, all
$p\ge1$. (II) every $\varepsilon\in(0,1)$: $\mathbb P(1-\varepsilon\le\mathsf{Height}(T_n)/h^+_n\le e+\varepsilon)\to1$.
(III) if $\ln n/h^+_n\to0$: $\mathsf{Height}(T_n)/h^+_n\to1$ in $L^p$, all $p\ge1$.

`thm:lineaire`. $c\in(0,1]$; $A_n>0$, $A_n\to\infty$, $A_n=o(\ln n)$; (eq:assumptions)
$\lim_{\varepsilon\to0}\limsup_n\max_{A_n\le i\le\varepsilon n}|S^n_i/i-c|=0$ and, for every $\varepsilon\in(0,1)$,
$\liminf_n\min_{\varepsilon n\le i\le n}S^n_i/n>0$. (I) $h^+_n/\ln n\to(c+1)/(2c)$. (II) $V^n_1,V^n_2$ independent
uniform vertices of $T_n$ given $T_n$ (all vertices, frozen included, coincidence allowed):
$\mathsf H(V_1^n)/\ln n\to(c+1)/(2c)$ and $d^n(V_1^n,V_2^n)/\ln n\to(c+1)/c$ in $L^p$, all $p\ge1$.
(III) $\mathsf{Height}(T_n)/\ln n\to\frac{c+1}{2c}f(c)$ in probability, $f(c)>1$ the unique solution of
$f(\ln f-1)=(c-1)/(c+1)$ ($c=1$: $f=e$, Devroye's constant). Constants check: $S_i\approx ci$ means $+1$-density
$(1+c)/2$, hence $h^+_n\approx\frac{1+c}{2c}\ln n$; all-plus gives $1,\,2,\,e$.

## 3. Lean definitions, followed by meaning (not by name)

- `activeCount` (48-49): unstopped walk, `true` $=+1$ at index $i+1$, index 0 unused. `extinctionTime` (52-54):
  `Nat.find` of the first $k$ with $S_k=0$ (so $k\ge1$ automatically), else $\top$. `hτ` is exactly
  $\tau(\mathbf x^n)>n$ (vacuous at $n=0$). `heightScale` (57-58) $=\sum_{j=1}^n\mathbf 1_{x_j}/S_j$. Correct.
- `State/initial/attach/freeze/step` (69-107): root `0` active, height 0; attach adds $t$ to `vertices` and
  `active`, edge $\{v,t\}$, height $h(v)+1$; freeze only erases $v$ from `active` (vertex and height kept).
  `transitionLaw` (115-118): `uniformOfFinset active` pushed through `step`, `dirac` if no active vertex
  (absorption). `treeLaw` (121-123): iterated `bind`, a fresh uniform active choice at every step conditional on the
  state, for BOTH attachment and freezing, new vertex active. This is Algorithm 1. `uniformOfFinset s =
  (card s)⁻¹ ∑ dirac a` (Mathlib `Uniform.lean:205`). `MeasurableSpace State := ⊤` (112) makes every
  `map`/`bind` measurable, so no hidden `map = 0` junk; the project proves `IsProbabilityMeasure` for `treeLaw`
  (`ForwardLaw.lean:84`), `uniformActiveHeightLaw` (`ForwardHeight.lean:244`), `uniformHeightLaw`
  (`ForwardUniformHeight.lean:50`), `forwardPairDataLaw` (`SIRRandomEnvironmentTransferStrong.lean:109`), all for
  every `x`, `n`.
- `treeHeight` (147) `= vertices.sup height`: maximum over ALL vertices, frozen included. Correct.
- Sampling. (I) `activeHeightKernel`/`uniformActiveHeightLaw` (134-142): uniform on `s.active`. (II)
  `vertexHeightKernel`/`uniformHeightLaw` (151-158) and `forwardPairKernel` (208-210): uniform on `s.vertices`
  (active and frozen); the pair is `(uniform u).bind ((uniform v).map ...)`, conditionally independent given the
  tree, diagonal included, observed as `(h u, h v, graph.dist u v)`. The graph is connected on `vertices` (edges
  only join an active vertex to a fresh one), so `dist` is the tree distance. Active vs all-vertex sampling is used
  exactly where the manuscript uses it.
- `NearOriginLimsup` (170-183), `BulkLiminf` (186-197): exact transcriptions of eq:assumptions (row $n$ with the same
  $n$ in $A_n$, $\varepsilon n$; integer $i$; $\varepsilon\to0^+$ as `𝓝[>] 0`; $\varepsilon\in(0,1)$ and strict
  `0 <` for the bulk; `bulkIndices` always adds `n`, already present for $\varepsilon\le1$).
- Conclusions: `eLpNorm f (ofReal p) μ → 0`, $p\ge1$ real, is $\mathbb E|Y_n-Y|^p\to0$ (the `eLpNorm'` formula needs no
  measurability); the window uses `Measure.real` of a probability measure; convergence in probability is
  $\mu\{\eta\le|\cdot|\}\to0$ for all $\eta>0$. Constants $(c+1)/(2c)$, $(c+1)/c$, `Real.exp 1`,
  `linearHeightFactor c` as in the manuscript. Quantifier order matches (array, $A$, $c$, then $p$, $\varepsilon$ or
  $\eta$, all fixed before $n\to\infty$).

### 3.1 Junk values

- `NearOriginLimsup`: for $i\ge A_n>0$ we have $i\ge1$ (`hA` keeps $i=0$ out), and always $|S_i|\le i+1$, so each
  term lies in $[0,2+|c|]$. The $\mathbb R$-valued sequence is bounded, so `limsup` is the true limsup (the
  `sInf ∅ = 0` junk of `Real.limsup` cannot arise). The `ℝ≥0` sup is $0$ on an empty index set; for fixed
  $\varepsilon$ the set is nonempty for large $n$ (as $A_n=o(\ln n)$ gives $\lceil A_n\rceil\le\varepsilon n$), so the
  convention never affects the limsup.
- `BulkLiminf`: $|S_i/n|\le(n+1)/n\le2$, bounded in $[-2,2]$ ($\ge0$ under `hτ`), so `liminf` is the true liminf;
  the only junk direction (`sSup` of an unbounded set $=0$) would falsify `0 <`, i.e. strengthen the hypothesis.
- `heightScale`: under `hτ`, $x_1=+1$ and $S_j\ge1$, so `heightScale (x n) n > 0` for $n\ge1$: no division by zero
  except at $n=0$. `Real.log 1 = 0` makes `/ log n` junk at $n\le1$. Finitely many $n$ never matter for `atTop`.
- `hA 0 : 0 < A 0` is an extra but harmless requirement (any sequence indexed from 1 extends).
- `hτ` on every row forces `activeCount (x n) i ≥ 1` for $i\le n$, hence nonempty `active` along the whole law: the
  `dirac s` branch, the `dirac 0` kernel fallbacks and `uniformOfFinset ∅ = 0` are never exercised.

### 3.2 Pinning of $f(c)$

`linearHeightFactor_existsUnique` (253) is exactly `∃! x, 1 < x ∧ x * (log x - 1) = (c-1)/(c+1)` for `0 < c ≤ 1`
(proved in the Challenge). `linearHeightFactor` (285) is `Classical.choose` of it on `Ioc 0 1`;
`linearHeightFactor_spec` (289) re-exposes the property; together they determine the value. My `#print axioms`:
`propext, Classical.choice, Quot.sound` for all three.

## 4. Non-vacuity (machine-checked by me, scratch only)

Directory `/private/tmp/claude-501/-Users-igor--claude-spares-spare-pgdWZg/5bdaa2ad-a45e-4f56-986a-69f4ce995350/scratchpad/review/`,
files `NonVac2.lean`, `NonVac3.lean`, `NonVac4.lean` (also `NonVac1.lean`, `Ax.lean`), each elaborated with
`lake env lean -DautoImplicit=false` against compiled `Challenge.Heights`: no `sorry`, axioms only
`propext, Classical.choice, Quot.sound`.

- All-plus rows ($c=1$, $S_i=i+1$, $\tau=\infty$), $A_n=1+\sqrt{\ln n}$: `hτ`, `hA`, `hAinf`, `hsmall`,
  `NearOriginLimsup`, `BulkLiminf` proved (NonVac2). Random recursive tree: conclusions $1,2,e$.
- Period-3 rows $(+,+,-,\dots)$, $c=1/3$, same $A_n$: all `thm:lineaire` hypotheses proved
  (`Review.hypotheses_pat3`, NonVac4), via general lemmas "$|S_i-ci|\le K$ implies `NearOriginLimsup` and
  `BulkLiminf`". So $c<1$ is not vacuous; $(c+1)/(2c)=2$ agrees with $h^+_n\approx\sum(2/3)/(i/3)$.
- Alternating rows $(+,-,+,-,\dots)$: `hτ` and `hlog` ($\ln n/h^+_n\to0$, `heightScale = ((n+1)/2)/2`) proved
  (NonVac3), so `thm:height` (III) has genuine instances (all-plus does NOT satisfy it: $\ln n/h^+_n\to1$).
- Content of the predicates: the alternating rows violate `BulkLiminf` (`Review.not_bulk_alt`, proved), so it is
  not true by junk. (Failure of `NearOriginLimsup` for a wrong slope is evident from the definition; not machine-checked.)
- iid supercritical case (NOT machine-checked): a path with $\tau=\infty$ and $S_i/i\to c=2p-1$, as a constant
  array, satisfies the hypotheses by the same argument with $o(i)$ deviations; see also the project's
  `IidLinearConditionedRows.lean`.

The Solution passes the export compare with only permitted axioms, so the statements are not junk-false either.

## 5. Evidence check (`heights/`, `negative-controls/README.md`)

- `compare.log`: `statements and reachable constants match` / `only permitted axioms`; `run.log`: both
  `leanexport` runs and `leanchecker --from-export solution.ndjson` exit 0; consistent with
  `comparator/heights.json` (9 targets, 3 axioms, `definition_names: []`).
- My direct check `lake env lean -DautoImplicit=false Challenge/Heights.lean`: exactly seven `declaration uses
  sorry` warnings, at lines 303, 311, 321, 332, 345, 361, 376; pinning theorems and helpers proved; imports only
  Mathlib; 389 lines / 17 KB.
- Negative controls: mutant A (`1 - ε` to `1 + ε`) fails with "theorem statement do not match"; mutant B
  (`heightScale` uses `S_i` instead of `S_{i+1}`) fails with "Const does not match". Good: the diagnostic sees a
  changed target and a changed reachable definition. Limits: two mutants, deleted (not reproducible), none inside
  `treeLaw`/`step`/`forwardPairKernel`, none for a `sorry` in a reachable declaration or a non-permitted axiom.
- This is Lake's comparison code run outside the Linux sandbox: NOT the official Comparator or Palomar report (the
  README says so). I could not run the official pipeline.

## 6. Findings

Blocking: none.

Should-fix (documentation/evidence; no statement changes):

- F1 (docstrings, lines 174-197, 300-387). State in the file: (a) `hτ` is the manuscript's standing assumption
  $\tau(\mathbf x^n)>n$ (tex 285-287) and forces $S_i\ge1$; (b) `limsup`/`liminf` are of sequences bounded by $2+|c|$
  and $2$, so no junk (3.1); (c) the `ℝ≥0` max is $0$ on empty index sets, irrelevant asymptotically; (d) row 0 and
  $n\le1$ junk is irrelevant.
- F2 (non-vacuity). The Challenge shows neither satisfiability of the array hypotheses nor probability-ness of the laws.
  Add NON-target proved declarations (unreachable from the targets, so absent from the Solution comparison; far
  below 1000 lines), e.g. my period-3 witness (about 170 lines with its general lemmas) and the `IsProbabilityMeasure`
  instances; or cite them in a `NOTES.md`.
- F3 (evidence packaging). `heights/` lacks the `NOTES.md` required by `CHALLENGE_RECIPE.md` (other groups have
  one); `run.log` line 15 refers to "certification notes" for nanoda though no nanoda run is recorded. Record
  SHA-256 of Challenge, Solution, config, `lean-toolchain`, `lake-manifest.json`; the 9 compared names; the mutant
  diffs; and "local diagnostic, not the official Comparator" beside any pass claim.

Minor:

- F4. Mixed style: three linear theorems take `{c} (hc) (hc1)`, the last `c : LinearRegimeParameter` (needed for
  `linearHeightFactor`). Equivalent; add one docstring sentence.
- F5. Docstring of `step` (104-105) says "all theorems about the process require a legal active choice": the uniform
  law only picks active vertices; reword.
- F6. `nearOriginMaximum` encodes `|·|` as `⟨_, abs_nonneg _⟩ : ℝ≥0` and needs
  `set_option backward.isDefEq.respectTransparency false` (167) (without it, tactic proofs about that term fail with
  type-incorrect-target errors in my scratch files). It compiles and compare passes; `‖·‖₊` would be idiomatic but
  would touch project definitions, so leave.
- F7. `forwardPairKernel` (208-210) has no empty-set guard (`uniformOfFinset ∅ = 0`); safe since `0 ∈ vertices`.
  One docstring clause suffices.
- F8. `maximum_height_window_tendsto_one` has the unused `_hε1 : ε < 1` (faithful to the manuscript; not needed).
- F9. Design note: both pinning theorems are proved inside the Challenge so that `def linearHeightFactor` (a
  `Classical.choose` whose body mentions a theorem) is reachable and identical on both sides; compare confirms it.

## 7. Not covered

Proof bodies and proof-route correspondence of the Solution; the official Comparator semantics of
`definition_names: []` (relied on `CHALLENGE_RECIPE.md` and the passing local diagnostic); other Challenge files;
Palomar allowlist and sandbox; manuscript errors elsewhere (the report's false printed L03/L04 do not enter T03/T04
as stated). Statement-level conclusion: the seven targets and two pinning types say what tex 286-339 says, with
Algorithm 1 correctly encoded, uniform sampling over the right sets, genuine `limsup`/`liminf`, and satisfiable
hypotheses.
