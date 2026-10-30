# Recipe: building a Palomar Challenge/Solution pair for a group of main results

Reference pair (already working locally): `Challenge/Heights.lean`, `Solution/Heights.lean`,
`comparator/heights.json`, evidence in `verification/certification/heights/`.

## What Comparator actually checks (read from `Lake/Check/Compare.lean`)
Starting from the *types* of the target theorems, it follows every constant used in types **and in
values (definition bodies and theorem proof terms)**, transitively, and requires each project constant
reached to be **structurally identical** in the Challenge and the Solution environments. The target
theorems themselves are compared by statement only. Consequences:
1. The Challenge must contain, verbatim, every project definition reachable from the statements,
   and also every project *theorem* reachable through definition bodies (e.g. the `_proof_n` of a
   structure field, or an existence lemma used by `Classical.choose`), with the same proof text.
2. Only the targets may have `sorry` bodies. Never a `sorry` in a definition or helper lemma.
3. Terms must elaborate identically: reproduce for each copied declaration the same `namespace`, `open`,
   `open scoped`, `set_option` (e.g. `set_option backward.isDefEq.respectTransparency false`),
   `variable`, `noncomputable`, `@[simp]`/attribute context as in its source module. Use one
   `namespace ... end` block per source module, in module-dependency order.
4. The Challenge may import ONLY Mathlib (never `Freezing1`). Start from the union of the Mathlib
   `public import`s of the source modules involved (the transitive closure matters for instances; if
   a mismatch appears, add the missing Mathlib module imports of the source module).
5. Palomar limits: Challenge file <= 1000 lines and <= 100 KiB (aim well below); starts with `module`;
   uses `@[expose] public section`; each definition and target gets a precise docstring giving its
   ordinary mathematical meaning (docstrings do not affect comparison).

## Files to create for a group `X`
- `Challenge/X.lean` (statement file; module `Challenge.X`).
- `Solution/X.lean`: `module`, `public import Freezing1`, docstring. No new declarations needed
  because the target theorems already exist in the project with the same names and types.
- `comparator/x.json` (see `comparator/heights.json`): `challenge_module`, `solution_module`,
  `theorem_names`, `definition_names: []`, `permitted_axioms` = propext, Classical.choice, Quot.sound.
- Evidence directory `verification/certification/x/` with the diagnostic outputs.

## Workflow
1. Closure data: `python3 SCRATCH/extract.py LABEL` prints the project declarations (with module and line
   ranges, source text excerpts) reachable from a group's statements, where SCRATCH is
   `/private/tmp/claude-501/-Users-igor--claude-spares-spare-pgdWZg/5bdaa2ad-a45e-4f56-986a-69f4ce995350/scratchpad`
   and LABEL is one of `T05`, `T01`, `T02`, `SIR-all` (data in `SCRATCH/closure4.out`; regenerate or edit
   `SCRATCH/Closure4.lean` for other target lists: it runs with `lake env lean`). The script skips
   auto-generated names (`_proof_n`, `match_n`, ...) which come with their parent declaration. IMPORTANT:
   the listing includes *theorems reachable only through proof terms*; copy them too (verbatim).
2. Assemble the Challenge by hand from the real source files (copy exact text), module by module.
3. Direct check: `cd /Users/igor/LeanFormalization/freezing1 && lake env lean -DautoImplicit=false Challenge/X.lean`
   (expect only `declaration uses sorry` warnings on the targets).
4. Artifact build, serialized across agents ONLY via
   `SCRATCH/bl.sh Challenge.X Solution.X` (never plain `lake build`, never `lake clean`).
5. Local comparison diagnostic (NOT the official Comparator; no Linux sandbox is available on this Mac):
   `scripts/local-comparator-diagnostic.sh comparator/x.json SCRATCH/x-diag` prints
   `compare: statements and reachable constants match` and `axioms: only permitted axioms` on success
   and names the first mismatching constant otherwise. It takes about 5 minutes. On success copy
   `compare.log`, `run.log`, `leanchecker.log` into `verification/certification/x/`.
6. Statement-only check of non-vacuity of hypotheses: if the project has an existence lemma showing that
   the model hypotheses (e.g. a `PoissonSIRData`-type structure) are satisfiable, add it as an extra
   target theorem so reviewers can see the hypotheses are not vacuous.

## Rules
- Do not edit existing files other than creating the new files listed above. Do not change versions,
  pins, caches or the lakefile. Never use `--inadvisably-no-sandbox`; `lake comparator` cannot run here.
- Never weaken or reformulate a statement to make comparison easier: the Challenge copies the project's
  statements exactly (the project statements themselves are reviewed separately).
- Write notes in `verification/certification/x/NOTES.md`: list of target theorems with the manuscript
  item each one corresponds to, list of copied declarations with source module, the import list, anything
  that needed adjustment, and the final diagnostic result.
