# Uniform attachment with freezing: formalization instructions

## Project context

- Source: supplied `attachement-uniforme-1-final.tex`, titled *Uniform attachment with freezing*. The manuscript is intentionally omitted from this candidate export; its exact identity and locators are in [FORMALIZATION_REPORT.md](FORMALIZATION_REPORT.md).
- Library: `Freezing1`; entry point: `Freezing1.lean`. Add modules under
  `Freezing1/` and import completed modules from the entry point.
- Preserve Lean `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`, and the locked
  revisions in `lake-manifest.json`.
- Run Lean and Lake commands from this project directory, even when the chat
  uses the parent `LeanFormalization` workspace.

The companion scaling-limit paper is in `../freezing2/`. Keep reusable definitions in clearly named modules so they can later be shared through an explicit dependency.

## Local skills

Read the relevant local skill when its task arises. Load only the skills and
references needed for the current work. If automatic discovery does not list
them, open the linked files directly.

| Task | Skill |
| --- | --- |
| Proof development, Mathlib search, focused checks | [lean-workflow](.agents/skills/lean-workflow/SKILL.md) |
| Encodings, modules, target statements, proof planning | [lean-project-architecture](.agents/skills/lean-project-architecture/SKILL.md) |
| Source fidelity, coverage, proof correspondence, axioms | [lean-statement-audit](.agents/skills/lean-statement-audit/SKILL.md) |
| Observed elaboration slowness or requested benchmarks | [lean-elaboration](.agents/skills/lean-elaboration/SKILL.md) |
| Parallel proof tasks and integration | [lean-orchestrator](.agents/skills/lean-orchestrator/SKILL.md) |
| Requested GitHub publication, Palomar submission, or both | [lean-publication](.agents/skills/lean-publication/SKILL.md) |

## Formalization practice

- The intended target is the paper's mathematical results and their required
  dependencies. Maintain [FORMALIZATION_REPORT.md](FORMALIZATION_REPORT.md) at
  coherent milestones, prioritizing main results while retaining other in-scope
  claims as obligations. Inventory the source before claiming paper-wide coverage.
- Preserve the mathematical meaning, assumptions, boundary cases, quantifier
  order, and dependence of constants. Conditional helpers count as progress;
  their hypotheses must be proved before claiming the advertised result.
- Prefer the paper's main strategy and novel arguments. Record substantive
  alternative routes, corrections, and source ambiguities in the report.
  Distinguish verifying a result from checking the paper's own proof.
- Search the installed Mathlib revision before replacing library mathematics.
  Use `module` and the pinned toolchain's visibility conventions.
- Do not introduce custom axioms or proof holes in maintained proof code.
  Inspect transitive axiom dependencies when marking results proved, and apply
  the trust requirements of the chosen publication destination when applicable.
- Compile focused targets during development and affected consumers at
  integration. Use `lake build` for the whole project. Coordinate builds that
  write shared artifacts; preserve dependency caches and version pins.
- Resolve routine proof choices autonomously within the user's scope. Investigate
  uncertainty using the source and available evidence; continue independent work
  when a genuine unresolved issue blocks one part.
- Record useful manuscript observations in
  [MANUSCRIPT_RECOMMENDATIONS.md](MANUSCRIPT_RECOMMENDATIONS.md).
  Manuscript edits and publication follow the user's requested scope.
  The selected publication destination is the public GitHub repository
  `igor-kortchemski/uniform-attachment-with-freezing`, with four full Palomar
  mechanical checks requested. The user authorized preserving the old repository
  privately as `uniform-attachment-with-freezing-private` before reusing its name.
  Use Apache-2.0 for original code and project documentation; contributor and
  responsible maintainer: Igor Kortchemski. Preserve the manuscript's own rights.
  Palomar intake and review-dependent registration require their own authorized scope.
- The user requires checking the exact proposed Palomar actions before further
  external submissions or changes. Prepare locally and allow read-only inspection,
  then show the source commit, titles, metadata/configuration paths, maintainer
  relationship and proposed actions for approval. Do not dispatch new checks,
  withdraw or replace a submission, or register a result before that check.
  Once an explicit batch is approved, carry out that batch without asking again
  for its already approved steps. Registration still requires the user's decision
  on the exact returned review.

## Markdown mathematics

Use `$...$` for inline mathematics. Put each `$$` display delimiter on its own
line, with a blank line before the opening delimiter and after the closing one.
Use MathJax-compatible LaTeX without undefined custom macros. Do not use
backslash-parenthesis or backslash-bracket math delimiters in Markdown prose.
This convention does not change code examples or `.tex` files.
