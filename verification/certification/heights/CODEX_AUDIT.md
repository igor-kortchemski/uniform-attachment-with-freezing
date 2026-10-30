# Independent Codex audit of the Heights interface

## Identity and method

Reviewed candidate base `4b3e78c6b9cd9db80f1b63fd85046e2805589123` on
30 October 2026. The reviewer did not author the interface or its proofs.
The mathematical source was independently reread at lines 244–249 and
285–339 of the manuscript in the development directory, since the isolated
candidate does not redistribute that file. Its SHA-256 is
`88953dd87165a14b0e643c5b3d0075d8ce5ec39cdcfc0c25d313570fc3ab00df`.

The current `Challenge/Heights.lean` has 400 lines and SHA-256
`23cd091c58b57e3672649bd7dc9fef88d88e4da320297b332cc1329641551462`.
The current configuration has ten selected targets and SHA-256
`612cff0d33ff05fed331d8b3fd293089a3b9e4e4422935abeda3eb2ad30f568c`.
The previous independent review concerned an earlier 389-line version and
nine targets; its findings were checked against the current source rather
than automatically relabelled as a review of this revision.

## Verdict

**No blocking mathematical statement-fidelity finding.** The seven main
conclusions are faithful to T03 and T04. The two height-factor targets and
the extinction-time pin preserve the specified constant and walk. This
verdict does not establish official Linux Comparator or Palomar acceptance.

| Current Challenge lines | Source conclusion | Result |
| --- | --- | --- |
| 314–318 | T03.I, active-uniform height in every real $L^p$, $p\geq1$ | Faithful. |
| 322–328 | T03.II, closed maximum window $[1-\varepsilon,e+\varepsilon]$ | Faithful. |
| 332–339 | T03.III, maximum $L^p$ limit when $\log n/h_n^+\to0$ | Faithful. |
| 343–352 | T04.I, deterministic logarithmic height scale | Faithful. |
| 356–367 | T04.II, all-vertex uniform height | Faithful. |
| 372–383 | T04.II, two conditionally independent uniform vertices' distance | Faithful, including coinciding samples. |
| 387–398 | T04.III, maximum constant with the specified $f(c)$ | Faithful. |

## Definitions and assumptions inspected

- `activeCount`, `extinctionTime` and `heightScale` (lines 50–66) are the
  actual unstopped walk, its first zero, and the post-step attachment
  reciprocal sum. Index zero is unused; including zero in the first-zero
  search changes nothing because the initial count is one.
- The standing strict-survival condition is already in the paper at
  line 286. It supplies positivity through the observation horizon. It
  does not introduce an extra asymptotic estimate or survival conditioning.
  Its row-zero requirement is automatic and does not restrict the source.
- `State`, `attach`, `freeze`, `step`, `transitionLaw` and `treeLaw`
  (lines 76–130) implement Algorithm 1 with a fresh uniform active choice
  at each step. Attachment includes the new vertex among the active ones;
  freezing retains its vertex, parent and height. The empty-active branch
  holds the state after absorption. Invalid selection leaves the state
  unchanged, but the uniform transition gives such a selection zero mass.
- The active-height kernel samples only active vertices; the full-height
  and pair kernels sample all vertices, including frozen ones. The pair
  law (lines 219–226) makes two draws given the same tree, includes the
  diagonal and records the genuine graph distance in its third coordinate.
  It does not assume independent sampled heights after mixing over trees.
- The literal source nested limits are encoded at lines 177–207, with
  one common cutoff and slope for each entire row. The near-origin
  maximum uses positive integer indices because $A_n>0$. Its empty-set
  convention and the special values at $n\leq1$ are asymptotically
  irrelevant. The real limsup/liminf sequences are bounded by the walk's
  elementary $|S_i|\leq i+1$ bound; totalized real order limits do not
  make the hypotheses vacuous.
- The cutoff is positive, divergent and sublogarithmic exactly as in T04.
  The slope is fixed in $(0,1]$ before the limiting index, and every
  moment exponent or probability tolerance is likewise fixed before
  the limit. No uniformity was silently lost by reordered quantifiers.
- The height-factor existence/uniqueness proof, its choice and its
  specification are included at lines 264–304. They use the exact source
  equation and enforce $f(c)>1$, including $c=1$. No estimate for the
  maximum is assumed as part of this definition.

The domains are mathematically nonempty. All-positive rows give the
linear case $c=1$, with $A_n=1+\sqrt{\log n}$. Repeating $(+,+,-)$ gives
slope $1/3$ and bounded count error. Alternating $(+,-)$ gives a positive
bounded population and $h_n^+$ growing linearly, so the extra condition
of T03.III also has genuine examples. These observations are mathematical
domain checks; this review does not present the earlier reviewer's
unretained scratch witness files as fresh machine evidence.

## Challenge integrity and proof evidence

The Challenge imports Mathlib only. Its eight deliberate holes are
selected comparison targets: the seven main conclusions and
`extinctionTime_le_iff`. The height-factor targets are proved in the file.
There is no replacement mathematical definition or assumed tail estimate.
`Solution/Heights.lean` imports the proved development and does not import
the Challenge.

The old comparison/replay evidence is applicable to the frozen Lean sources:
there are no changes to any `.lean` file, comparator configuration, toolchain
or dependency manifest between built commit `ab3d936` and base `4b3e78c`.
The recorded Heights comparison matches statements and reachable constants;
its solution export passes the recorded six checkers. Those runs are local
evidence, not a fresh run by this reviewer or an official Palomar report.

New independent evidence is in `CodexHeightsLocalStatements.lean` and
`codex-statements.log` in this directory. The joint Heights/LocalLimits probe
reconstructs eleven source-facing types, expanding the actual pair sampler
and nested assumptions rather than merely repeating theorem names. It
direct-checks current Solution imports with exit zero and queries thirteen
closures, all using only `propext`, `Classical.choice`, `Quot.sound`.
Seven of those examples check all seven Heights main conclusions.

No proof implementation or interface statement was edited. A full independent
rereading of every pre-existing Solution proof body was outside this scoped
interface review. No whole-manuscript completeness or publication acceptance
is inferred from this pass.
