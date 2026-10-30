# Independent audit of the SameLaw certification interface

Reviewed baseline: local candidate commit
`4b3e78c6b9cd9db80f1b63fd85046e2805589123`, 30 October 2026.
The reviewer did not author this Challenge, Solution or mathematical proof.
No existing Lean source, configuration or proof was changed in this audit.

## Verdict

The interface faithfully states T05 **as equality of the two canonical
observable laws**. The actual forward and reverse algorithms, their time
indices, labels, random choices and extinction endpoint match the source.
No invented model substitute, hidden probability estimate, vacuous domain
or demonstrated metaprogramming soundness bypass was found.

This is not a verdict that the official Linux Comparator or Palomar
pipeline accepts the candidate. The representation dictionary and the
remaining internal-name devices must remain explicit in its description.

## Source reconstruction and mathematical audit

The unchanged manuscript is read from the supplied development copy
`../freezing1/attachement-uniforme-1-final.tex`. Algorithm 1, lines 424–433,
starts from one active root, samples uniformly from all active vertices,
freezes on a negative sign and attaches on a positive sign. Algorithm 2,
lines 527–536, starts from $S_n$ isolated active labels and runs backwards:
negative signs adjoin a freezing-labelled singleton, while positive signs
merge a uniformly selected ordered pair, retaining the first root. T05,
lines 658–664, erases only the distinctions among active reverse labels and
asserts equality of the resulting double-labelled rooted tree laws.

In `Challenge/SameLaw.lean`:

- Lines 49–69 give the genuine raw sign walk and first zero. The only
  main premise, at lines 676–677, is $n\leq\tau(x)$, including equality.
  No survival or regularity estimate is added.
- Lines 80–159 implement the original forward process. Birth identifiers
  are attachment times; freezing times are retained. `transitionLaw`
  samples the true active finset, and iterated binds give fresh conditional
  choices. The empty-active branch agrees with source absorption.
- Lines 452–453 start the reverse process with the right isolated labels.
  `lawAfter` at lines 509–516 reads $x_n,x_{n-1},\ldots,x_1$.
  `joinLaw` samples `roots.offDiag`, uniformly over ordered distinct roots;
  the second root becomes a child of the first and receives edge label
  $i+1$. Negative signs adjoin exactly the vertex labelled $i+1$.
  This follows Algorithm 2, rather than the swapped-sign introductory typo.
- Lines 547–600 retain the canonical vertex set, actual graph, active
  status and all freezing labels. Reverse active labels alone are erased.
  The identifier of a non-root vertex is its incoming edge label; the root
  is identifier zero. Thus it is intrinsic to the double-labelled tree,
  rather than an independently chosen extra vertex ordering.
- Probability and support targets exclude junk zero pushforwards and
  ensure genuine finite trees/canonical coordinates on the used law.
  Generic invalid-choice/default branches are outside actual support, or
  are the specified absorbing behavior.

`Solution/SameLaw.lean` imports only the proved project entry point, never
the Challenge. `ConstructionEquivalence.lean:37–60` first proves equality
of the complete canonical state laws using actual positive-support point
masses, then pushes that equality to the common observable. Its proof
does not assume the printed false fixed-schedule support claim L04.

## Exact scope of the representation

The compared carrier is `CanonicalTree.Observable`, not a quotient type of
rooted double-labelled graph isomorphism classes. On the actual supports,
the canonical observable determines the root, adjacency, active/frozen
labels and incoming edge labels. Conversely the rooted double-labelled
tree determines these canonical identifiers. This is a faithful
representation of T05, but the full dictionary theorem on isomorphism
classes is not a compared target.

The project has additional checks such as
`CanonicalTree.reverse_edge_time` and `reverse_root_id`
(`CanonicalTreeObservable.lean:178–187`), and a stronger full-state law
equality. The selected pins include graph isomorphism and frozen labels,
but do not themselves export a complete quotient-law equivalence. Do not
describe the certified type as a literal isomorphism-class law equality
without disclosing this representation. The existing correspondence table
and `OPEN_OBLIGATIONS.md` already disclose it.

## Internal-name devices: technical review

The only environment mutation in this Challenge is the temporary
`setMainModule` block at lines 197 and 413. Its pinned implementation in
Lean v4.35.0, `Lean/Environment.lean:1184`, changes `header.mainModule` and
synchronizes the import realization context. It does not add, remove or
replace a mathematical constant, declaration type or value. Private-name
construction explicitly includes the module name
(`Lean/PrivateName.lean:29`), which accounts for the intended auxiliary
proof-name alignment.

The matcher option at line 507 is also explained by the pinned source:
`Lean/Meta/Match/Match.lean:1076–1132` puts the code-generation flag in the
matcher-cache key. Toggling it prevents sharing an otherwise identical
matcher from an earlier declaration, allowing the original declaration
name to be reproduced. It affects generated names/code generation; the
kernel declaration value remains subject to comparison.

These devices do **not** exempt the affected constants from export or
comparison. `LeanExport/Basic.lean:252,462` looks up requested constant
names and recursively exports their types/values and dependencies; it
does not select them by the temporary main-module name. The pinned
`lake/Lake/Check/Compare.lean:37–59` follows every reachable non-target
constant and requires structural equality, including values. The local
diagnostic actually calls those functions. Solution proof terms are also
checked separately by the recorded kernel replays.

Accordingly, no soundness defect is demonstrated by the presence of these
two constructs. They are fragile implementation details in a trusted
specification and remain a readability/compatibility concern. Their
acceptance by the official pipeline is unverified. Refactoring them away
would alter reachable proof/definition bodies and require new comparison
evidence; an unconditional claim that the present devices are forbidden or
necessarily rejected is not established by this audit.

## Evidence and small documentation findings

The baseline configuration selects **24 targets**, and the 680-line
Challenge has exactly 24 target `sorry` bodies. The other copied reachable
theorems have real proof bodies. `definition_names` is empty and the
permitted-axiom list is exactly the three standard axioms. Existing
`samelaw/NOTES.md` and the older independent review retain earlier totals
of 23 targets/675 lines; those totals should be updated or labelled as
historical. This is not a mathematical defect.

The recorded baseline comparison states that statements and reachable
constants match and only permitted axioms occur. Its two exports and all
six recorded kernel runs have exit zero. This audit inspected those logs;
it did not repeat the expensive export and six replay runs.

An additional independent probe, `CodexSameLawStatements.lean`, expands
both actual observable samplers, proves a non-vacuous all-positive source
domain, checks the zero-step endpoint and retains the exact frozen-label
interpretation. Its final ordinary imported check passes with exit zero,
four independently reconstructed examples, five standard-axiom closure
queries and no warnings, recorded in `codex-statements.log`. This probe is
not the official Comparator.

The manuscript's false fixed-schedule L04 claim and all other uncovered
assertions remain in the inventory. This scoped T05 audit does not certify
the whole paper, its original probability argument or Palomar acceptance.
