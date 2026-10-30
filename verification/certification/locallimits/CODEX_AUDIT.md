# Independent Codex audit of the LocalLimits interface

## Identity and method

Reviewed base `4b3e78c6b9cd9db80f1b63fd85046e2805589123`, 30 October 2026.
The reviewer independently reread manuscript lines 244–280, 881–889 and
the Bienaymé interpretation used by the T02 proof, then read current
Challenge definitions and the relevant model/ambient adapters. The paper
was read from the adjacent development directory; its unchanged SHA-256 is
`88953dd87165a14b0e643c5b3d0075d8ce5ec39cdcfc0c25d313570fc3ab00df`.
No mathematical source was edited.

`Challenge/LocalLimits.lean` has 846 lines, SHA-256
`dac7b298e9807b023be9f58f79695648db23f19967a4f59d964f04028b07416a`.
`comparator/locallimits.json` has 28 targets, SHA-256
`c2143821781f5ccefc5253c4912defefad1111799eecc0e927d13da3cf65e6a7`.
The previous independent review concerned an earlier configuration. Its
requested changes and newly added pins were checked in the current file.

## Verdict

**Pass for the explicitly chronological local-limit interface, with the
ambient-space certification boundary below.** No hidden estimate,
vacuous conclusion, changed sampling law or missed endpoint was found in
the selected formulations. The source's unrestricted ambient theorem is
mathematically equivalent on these actual objects and proved separately
in the development; that bridge is not part of this comparison interface.

| Current Challenge lines | Compared conclusion | Verdict |
| --- | --- | --- |
| 431–437 | T01's three equivalent assertions | Faithful in the chronological local space. |
| 442–452 | T01's common measurable pathwise limit and both weak-law limits | Faithful in that space. |
| 818–820 | T02 all-child Bienaymé branching law | Faithful. |
| 824–826 | T02 equality with the actual geometric Bienaymé law | Faithful. |
| 830–833 | Exact root offspring masses $(1-p)p^k$ | Faithful. |
| 839–844 | Almost-sure chronological plane convergence and its joint actual-history image law | Faithful. |

The 28 comparison targets are six main-result formulations plus 22
supporting pins; they are not 28 distinct conclusions of the paper.

## Model, topology and target definitions checked

The walk and first zero retain the source's sign convention and positive
indices. The two active-tree transitions are uniform over the actual
active set and the entire path law is the trajectory of those kernels.
Approximating T01 rows may become extinct before their observation time:
there is no unintended strict-survival premise on them, and the process
is held after extinction. Only the limiting schedule must never hit zero.
Coordinatewise eventual agreement is imposed at every positive index,
with no uniform agreement rank silently assumed.

`VertexRecord` and the coherent finite-ball carrier (lines 202–247) retain
all incoming-edge birth times and active/frozen vertex labels. Parent
heights and strictly older parents give genuine rooted tree paths. Balls
are finite, have unique vertex IDs and retain their boundary labels.
The topology is the product of discrete ball topologies and
`tendsto_iff_balls` pins eventual equality of each full ball. The default
of `localTreeOfState` is outside the almost-sure valid-state support;
the comparison selects both state validity and exact ball characterization.

The T01 predicates expand to existence of an actual weak probability-law
limit and almost-sure pathwise local convergence under the same actual
history law. They do not assume the desired limit or a priori tightness.
The reciprocal series (line 411) is indexed exactly as the theorem states,
using the post-step active count at freezing steps. Its nonnegative partial
sums diverging to positive infinity express the asserted divergence.

The pathwise limit definition chooses a limit if one exists, with a fixed
default otherwise. T01's common-limit theorem explicitly supplies its
almost-everywhere measurability and convergence. The new T02 pins at
lines 771–789 likewise supply actual almost-sure labelled convergence,
measurability and the iid-sign mixture transition. Thus probability-law
mapping is not justified merely by a potentially default-valued definition.

The annealed path law (lines 664–743) integrates a fresh sign of probability
$p$ at every actual tree transition; it does not postulate a law of iid
subtrees. Its full finite-prefix identification with the original iid-sign
construction is proved in `ForwardAnnealedHistory.map_prefix_eq_iid_sign_mixture`
(outside the selected Challenge targets). The recursion itself also
specifies the intended averaged history, so the selected conclusions
are genuine tree-history statements rather than unrelated marginals.

The plane projection follows child birth times in increasing order and
then forgets labels. `prune` maps a true iid offspring field to canonical
Ulam–Harris coordinates. `IsBienayme` tests the root law and the full joint
family of all child subtrees given its size, rather than only one child or
offspring expectations. The existence/uniqueness pin gives a genuine law.
The geometric measure is evaluated at success parameter $1-p$, so the
specified atom is $(1-p)p^k$. The excluded case $p=1$ would use Mathlib's
totalized zero-success default; it is not used to justify the theorem.
$p=0$ is included and gives the single-root plane tree.

## Ambient-space certification boundary

The Challenge does not contain the full unrestricted unordered labelled
space of source lines 881–889. Its docstring at lines 235–240 now says so.
The project genuinely proves the required bridge, not just a prose
assertion:

- `LocalTree.isClosedEmbedding_toUnordered`
  (`ChronologicalAmbientEmbedding.lean:87`) proves the chronological image
  is closed and has the induced source topology.
- `LocalTree.exists_weakLimit_iff_ambient`
  (`ChronologicalAmbientLaws.lean:28`) proves weak-limit existence in either
  space is equivalent, with no new support hypothesis.
- `LocalTree.ambient_weakLimit_supported` derives support of ambient weak
  limits rather than assuming it.
- `source_diagonalLocalConvergence_iff`,
  `source_almostSureLocalConvergence_iff`,
  `source_local_convergence_equivalences` and the common-limit/annealed
  wrappers in `MainLocalAmbient` supply the full ambient source conclusions.

Their statements and the central closed-image construction were inspected.
The new probe also checks the full-ambient equivalence against the actual
Solution import. However these bridges are not selected in
`comparator/locallimits.json`; the official record for this interface must
describe its chronological statement. Describing it as a mechanically
compared unrestricted-ambient theorem would overstate its selected scope.
The existing `OPEN_OBLIGATIONS.md` appropriately records this boundary.

## Internal declaration devices and evidence

Unlike SameLaw/Sir, this file does not call `setMainModule`. It does use
`bootstrap.genMatcherCode false` at lines 603 and 686 and explicit
`historyKernel._proof_1`/`_proof_2` declarations at lines 717–737 to align
auxiliary declarations with the multi-module development. Their bodies were
read: they are actual finite-index/measurability proofs, not assumed model
identities or mathematical substitutes. The matcher setting occurs around
the ordinary recursive `follow` and annealed `treeLaw` definitions. These
devices should be included in the general implementation-disclosure list,
which currently emphasizes SameLaw/Sir. Their acceptability to the official
Linux pipeline remains untested; the local match is not acceptance evidence.

All 28 deliberate holes are selected comparison targets. The surrounding
model definitions contain no extra axiom or assumed convergence estimate.
`Solution/LocalLimits.lean` imports the actual development, not Challenge.
Recorded comparison/replay evidence can be reused for the unchanged frozen
Lean files, dependencies and configs between `ab3d936` and `4b3e78c`; this
review did not rerun those expensive local exports or checkers.

Fresh independent evidence is the joint
`../heights/CodexHeightsLocalStatements.lean`, ordinary imported exit zero
in `../heights/codex-statements.log`: eleven reconstructed examples and
thirteen standard-three axiom closures across the two interfaces. It
expands T01's three assertions and reciprocal sum, checks the genuine full
ambient theorem separately, expands the T02 law to an iid-field pushforward
and checks the $p=0$ root mass. It does not import Challenge holes.

No official Comparator, NanoDa pipeline, Palomar acceptance or complete
manuscript coverage is claimed by this interface review.
