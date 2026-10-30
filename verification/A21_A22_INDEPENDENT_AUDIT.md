# Independent review of A21–A22

The integrating reviewer read source lines 893–906 and reconstructed the
claims before comparing the implementation. The six degree/attachment
modules were written by a different proof worker. This review also checks
the independently written `AttachmentDensity` specialization. The source
hash and scope are unchanged from `FORMALIZATION_REPORT.md`.

The degree is the cardinality of actual graph neighbours among existing
vertices, including the parent of a nonroot vertex. Every occurring birth
ID and the root are quantified. Validity and legal-or-held transitions are
structural premises supplied almost surely by the original history law;
they do not contain a degree bound or eventual-freezing assumption.

The deterministic local-convergence equivalence checks both directions.
Monotone finite neighbour sets stabilize under a cardinality bound, and
induction on radius makes the vertex sets of all finite balls stabilize.
Old parent/height data persist. A displayed freezing label changes at most
once, so its stabilization does not assume that the vertex freezes.
Conversely, each old vertex's neighbours lie in a fixed finite-radius ball,
whose eventual agreement bounds its degree. This is the existing
chronological labelled local-tree carrier, with its proved graph/ball
interpretation; it does not settle the broader arbitrary-label A20 domain.

For a birth ID $r$, the conditioning event is actual infinite survival,
$E_r=\{r\text{ remains active at all times }r+k\}$. Finite mixed selection
patterns and survival are first evaluated together using the original
uniform transition kernels. Continuity from above yields their joint
probabilities with $E_r$. Persistent parents are proved to agree with the
parents recorded at birth. Only after this factorization is established
does normalization prove conditional independence. No independent
auxiliary choices or independence premise replaces the source process.

At an attachment time $i>r$, the true parameter is $1/S_{i-1}$. The
divergence of the true hazard sum and the installed second Borel–Cantelli
lemma imply infinitely many unit increments of the actual degree.
Restriction to $E_r$ handles null events without an invalid conditional
probability. Countable intersection gives the simultaneous almost-sure
degree/freezing equivalence. Finite extinction is separately handled by
the actual held path. The final all-schedules theorem has no hidden
nonextinction or positive-survival premise.

`attachment_density_ge_half` proves the literal density assertion for
every $n\ge1$ under nonextinction. The printed post-step attachment sum is
exactly the already proved height scale. Its divergence is thus checked
through that lower bound; the manuscript's particular density-to-harmonic
argument is replaced. The separate bubble-sorting argument A32 remains
outside this audit.

S04 remains a correction, not a verified literal formula. The schedule
$(+,-,+,+,\ldots)$ has actual never-frozen-root probability $1/2$, while
the printed product is zero. The birth endpoint must also be strict:
a newborn's birth-degree jump is deterministically one and is not selection
of that newborn. Both defects have formal counterexamples in
`ForwardSelectionSourceChecks`. Removing that endpoint does not change
divergence or the corrected conclusion.

Verdict: corrected A21/A22 conclusions and the conditional-independence /
Borel–Cantelli proof strategy are verified. Existing T01 uses its earlier
root-degree route; its proof was not replaced by this audit. No claim is
made that the incorrect printed denominators are true.

Evidence: `A21A22IndependentStatements.lean` reconstructs five expanded
examples, including raw graph-degree bounds, actual conditional events,
null-safe divergence, all schedules, and density/printed-sum divergence.
Its direct check passed in `a21-a22-independent-statements.log`; six
closures use only `propext`, `Classical.choice`, and `Quot.sound`. The
worker's separate eight-example/fourteen-closure probe remains an authored
check, not the source of this independent-review designation. Full build
and namespace closure evidence is recorded in the main report.
