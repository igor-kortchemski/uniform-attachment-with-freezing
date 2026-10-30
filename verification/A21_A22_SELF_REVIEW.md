# A21/A22: degrees, local convergence, and conditional attachment

This is the author's implementation review, not an independent audit. It
concerns the proof at source lines 893–906 in
`attachement-uniforme-1-final.tex`. The integrating agent performs the
independent statement review and owns the coverage record and artifact
builds. Existing T01 statements and proofs were not changed.

## Exact scope and carriers

The state is the original `Forward.State`, with persistent birth IDs,
actual graph edges, active IDs, parent and height functions, and displayed
freezing labels. The law is the previously constructed
`ForwardInfiniteHistory.fullLaw x`, whose one-step conditional law is the
original uniform-active-vertex kernel. The local tree is the existing
`Forward.localTreeOfState`; every complete finite ball retains birth IDs,
incoming-edge timestamps, parent data, heights, and displayed labels.

`Forward.vertexDegree s r` counts the actual neighbours of $r$ among
`s.vertices`, including its parent when $r$ is not the root. It specializes
to the existing root degree at $r=0$. All degree/local and eventual-freezing
predicates quantify every ID that actually occurs and explicitly include
the root. Held steps after extinction are included.

## A21: deterministic equivalence

`exists_local_limit_iff_all_degrees_stabilize` from
`ForwardDegreeLocalCriterion.lean` (in namespace
`ForwardInfiniteHistory`) proves, for every valid
legal-or-held trajectory $H$,

$$
\bigl(\exists T,\ T_n\longrightarrow T\text{ locally}\bigr)
\quad\Longleftrightarrow\quad
\text{every occurring vertex has an eventually constant finite degree}.
$$

The intermediate equivalent statement is that each ID's degree is bounded
over all times. No eventual-freezing or probabilistic premise appears in
this deterministic result.

The proof checks the source's implicit geometric argument in both
directions. Neighbour sets grow monotonically. Bounded cardinalities make
each neighbour set eventually constant. An induction on radius then makes
each finite radius vertex set eventually constant. Parent and height data
of old vertices persist; a displayed freezing label changes at most once,
so each old record eventually stabilizes even if it never freezes. Thus
the complete labelled balls stabilize. Conversely, after an occurring
vertex's height has stabilized, all of its neighbours lie in the ball of
radius one larger; eventual equality of that finite ball bounds its degree.

The source's attachment density bound $n\leq 2\#(\mathsf P\cap[1,n])$
is already checked by `le_two_mul_plusCount` in `Path.lean`. The printed
post-step attachment reciprocal series is the existing `heightScale` and
diverges by `tendsto_heightScale_atTop`. The true pre-step attachment
hazards dominate it, as proved in `AttachmentReciprocalSeries`. The
harmonic argument uses the previously verified count-of-attachments lower
bound; it does not certify the adjacent-transposition proof elsewhere in
the paper.

Subsequent separate milestone: the actual adjacent-transposition proof is
now independently reviewed in `verification/A32_ADJACENT_SWAP_AUDIT.md`.
That later certificate is distinct from this A21 implementation route.

## A22: freezing, exact conditional independence, and Borel–Cantelli

The deterministic implication is separate:
`degree_constant_after_freezing` and
`all_degrees_stabilize_of_all_eventually_frozen` prove that an actually
frozen vertex's degree stays fixed, and hence that simultaneous eventual
freezing implies stabilization of all occurring degrees.

For the converse, suppose the schedule never becomes extinct. For every
birth ID $r$, let

$$
E_r=\{H:\ r\text{ remains active at every time }r+k,\ k\geq0\}.
$$

At attachment time $i>r$, the actual selected parent is stored in the
persistent field `(H i).parent i`. For every finite set
$F\subset\{i>r:X_i=+1\}$ and binary pattern $\varepsilon$, the theorem
`fullLaw_survival_attachmentPattern` derives from the original kernels

$$
\mathbb P\!\left(E_r\cap
 \bigcap_{i\in F}\{\mathbf 1_{\{r\text{ selected at }i\}}=\varepsilon_i\}\right)
=\mathbb P(E_r)\prod_{i\in F}
 \left(\frac1{S_{i-1}}\right)^{\varepsilon_i}
 \left(1-\frac1{S_{i-1}}\right)^{1-\varepsilon_i}.
$$

The Lean factors use two Boolean cases, not real powers. The finite
horizon proof first keeps survival to the terminal horizon and the whole
finite pattern in the same genuine tree law. Continuity from above on the
same coherent infinite history then supplies $E_r$. The parent-at-birth
field is proved equal to the final persistent parent field, rather than
assumed to be an independent auxiliary mark.

When $\mathbb P(E_r)>0$, `conditional_attachmentPattern` normalizes this
identity. `conditional_postBirthAttachment_iIndepSet` proves independence
of the actual post-birth attachment events under that conditional
probability measure; their exact probabilities are $1/S_{i-1}$. Events at
all other times are empty. The divergent pre-step reciprocal series gives
`conditional_postBirthAttachment_tsum_eq_top`. The installed second
Borel–Cantelli theorem yields
`conditional_infinitely_many_attachments`.

`postBirthAttachment_degree_jump` checks that each such event is a literal
unit increment of the actual graph degree. Monotonicity then proves
`conditional_vertexDegree_tendsto_atTop`. The null-safe statement
`restrict_survival_vertexDegree_tendsto_atTop` uses restriction to $E_r$
and is valid even when that event has probability zero. Countable
intersection over all IDs supplies the simultaneous almost-sure
degree/freezing equivalence. Finite extinction is handled separately by
the actual held absorbed trajectory. The final source-facing export is
`fullLaw_local_limit_iff_all_eventually_frozen_all_schedules`.

This checks the corrected conditional-independence and Borel–Cantelli
argument itself; it is not inferred from T01 or a marginal non-tightness
estimate. The freezing converse is an almost-sure statement, not a
deterministic claim about every legal choice sequence.

The already verified `ForwardLifetimeEvents`, `ForwardLifetimeLimit`, and
`ForwardLifetimeCriterion` supply the actual infinite survival product and
its equivalence with divergence of the printed freezing reciprocal
series. Their pre-step/post-step comparison is retained.

## Source corrections retained explicitly

S04 is not discharged by claiming the printed probabilities are correct.
The correct forward selection denominator at step $i$ is $S_{i-1}$.
`ForwardSelectionSourceChecks.selectionIndexSchedule_refutes_printed_product`
formally checks the schedule $(+1,-1,+1,+1,\ldots)$: the original root's
actual survival probability at time $2$ is $1/2$, while the printed finite
product is $0$.
`selectionIndexSchedule_actual_never_frozen_probability` additionally
proves that the actual infinite never-frozen-root event has probability
$1/2$ for that schedule.

The source also writes the attachment events for $i\geq r$ at a vertex
born at time $r$. Selection of that vertex is possible only at $i>r$.
`birth_step_not_selection_of_newborn` checks the distinction: a newborn's
actual degree changes from $0$ before birth to $1$ at birth
deterministically, even when the pre-step active population is $2$. Thus
its birth jump is not a selection event with probability $1/2$. The
corrected proof uses strict post-birth times throughout; discarding this
single time does not change divergence or the main conclusion.

## Evidence and integration status

The following actual-file direct checks completed with exit code zero and
no diagnostics:

- `ForwardVertexDegree.lean`: `/tmp/forward-vertex-degree2.log`.
- `ForwardDegreeLocalCriterion.lean`: `/tmp/forward-degree-local.log`.
- `ForwardAttachmentPatterns.lean`: `/tmp/forward-attachment-patterns5.log`.
- `ForwardConditionalAttachments.lean`: `/tmp/forward-conditional-attachments3.log`.
- `ForwardSelectionSourceChecks.lean`: `/tmp/forward-selection-sourcechecks5.log`.
- `ForwardFreezingDegrees.lean`: `/tmp/forward-freezing-degrees3.log`.

The integrating agent has built all six modules. Durable build evidence
is recorded in:

- `verification/vertex-degree-forest-cut-state-build.log`.
- `verification/forward-degree-local-criterion-build.log`.
- `verification/attachment-patterns-plane-labelled-topology-build.log`.
- `verification/conditional-attachments-forest-slots-block-height-build.log`.
- `verification/forest-reconstruction-selection-source-checks-build.log`.
- `verification/forward-freezing-degrees-build.log`.

The actual expanded statement/axiom probe
`verification/A21A22Statements.lean` passed with exit code zero and no
diagnostics. It contains eight expanded examples and fourteen axiom
closures; every closure uses only `propext`, `Classical.choice`, and
`Quot.sound`. The author check is `/tmp/a21-a22-statements.log`; the
integrating agent also ran that authored probe and retained
`verification/a21-a22-statements.log`. Running the authored probe does not
by itself constitute independent semantic review.

Recommended coverage reconciliation: A21 is proved;
A22's corrected mathematical conclusion and conditional argument are
proved, while the literal post-step selection/product formulas remain
refuted under S04, with the strict birth-index correction recorded here.
No mathematical proof obligation remains in the corrected A21/A22 scope.
