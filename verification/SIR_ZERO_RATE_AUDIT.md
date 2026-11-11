# Independent audit of the physical zero-contact branch

Reviewed root-authored modules: `PoissonContactOptional.lean`,
`SIROptionalContactProtocol.lean`, `SIRZeroRateLaw.lean` and
`SIRPhysicalZeroRate.lean`. This audit and its probe were written by a
different agent. Scope is the zero-intensity branch of the source SIR setup
and history identification at lines 2026–2046. The older positive-rate
physical history construction has separate author/self-review and independent
root review records.

## Carrier and actual event protocol

`OptionalPath = Unit ⊕ ArrivalPath` includes a genuine empty process. Its count
is zero at every observation time. A present contact process retains its
whole original arrival sequence. For an empty contact coordinate,
`optionalEventTime` returns `none`, the absence of an event. No numeric zero,
large finite substitute or rate-zero exponential random variable is used as
a contact time. Recovery coordinates remain genuine finite lifetimes.

`hasOptionalPoissonCounts_zero_iff` proves that zero Poisson counting marginals
are equivalent to the whole path law being the Dirac mass at the empty
process. The forward direction uses simultaneous zero counts at all natural
times: any nonempty arrival path has a finite first point and hence a
positive count at some integer time. The converse explicitly verifies that
the empty process has the source's zero Poisson marginals.

The next event is a strict finite winner among live slots. Its comparisons
ignore absent contacts and compare actual absolute event times. Initially
there is one active root, so when all contact paths are empty, its recovery
is the unique finite event. The exact recursion gives the recovered-root
frame at every event index after the first one. The active set is empty and
the whole frame is held thereafter.

## Tree, count and physical-time identities

`SIRZeroRateLaw.lean` derives the original embedded kernel's root-recovery
transition at rate zero, then proves the entire embedded history is the
Dirac law of that initial/recovered-root path. This equality is proved from
the actual kernel, not imposed by naming a deterministic replacement law.

`zeroRate_physical_tree_fullLaw` identifies the actual optional-contact
protocol's complete tree path with that same embedded law. Its source contact
count assumptions force all paths empty on one almost-sure event. No
independence premise is needed in this degenerate case. The source's stronger
independent-period/independent-process setup therefore implies the theorem's
hypotheses.

The projected count law is identified with `countsFullLaw 0 n`. The
independent probe additionally reconstructs the same equality for literal
susceptible and active label cardinalities, using actual population validity
at time zero and after root recovery. It also composes the zero physical
history with the root's A66 adapter, keeping all counts and all trees of a
prefix jointly in the original forward-word mixture.

`zeroRate_physical_absorption` explicitly takes the root lifetime law
$\mathrm{Exp}(1)$. It proves that lifetime is positive almost surely, that the
physical event time is exactly that lifetime, and that every later frame is
the same absorbed frame. The tree/count identities need no waiting-time law
because their discrete genealogy is deterministic. All population sizes,
including no initially susceptible individuals, are covered.

## Verification and limits of this audit

`verification/SIRZeroRateStatements.lean` checks empty-process equivalence,
absence of a contact event, the complete physical tree law, literal physical
counts, complete-prefix A66 composition and positive exponential recovery
timing. The actual-file direct check passes with zero diagnostics: four
expanded examples, two independently reconstructed literal-count/A66
composition theorems and seven transitive axiom probes. Every probed closure
is contained in `propext`, `Classical.choice` and `Quot.sound`
(a local log, not retained). Root artifact integration passed
separately in
`verification/sir-physical-zero-rate-build.log`.

No source mismatch, artificial clock or unproved history-independence
premise was found. This audit certifies only the zero branch of the optional
carrier. It does not assert a theorem for positive-intensity arbitrary
optional-path data; the already proved positive-rate source carrier remains
separate until that additional transport is proved.
