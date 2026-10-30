# A77 final pair interface: independent semantic review

The reviewer read source lines 2199–2203 and the new
`SIRCaptureCoefficientObservedPairs` module, including the relevant
`Observed` and `Source` interfaces. The reviewer did not author these
modules. This is a scoped review of the final pair lift, not a second
independent proof audit of the whole same-coefficient concentration route.

For each adaptive word, `wordObservedBirthPairKernel` first draws one
actual terminal forward tree from its genuine fixed-word law. Only then
does it take the product of two copies of that tree's conditional uniform
vertex law, mapped by the same actual reverse-birth clock. The outer word
mixture retains the actual SIR word probabilities. Thus both vertices
come from the same random terminal tree and are independent conditionally
on that tree. The definition is not the product of two separately mixed
terminal marginal laws. No unconditional independence is asserted.

The actual forward vertex set is nonempty almost surely, by the proved
validity and root membership. Consequently each conditional uniform law,
its clock pushforward, the conditional product, and both outer mixtures
are genuine probability measures. The proof handles the totalized
off-support words through existing valid fixed-word tree laws, and uses
the actual feasible-word identification for the source semantics.

Both projections of the pair law equal the previously verified actual
single reverse-birth law, for every row. These exact marginal identities
are proved before taking limits. `actualTerminalReverseBirthPairLaw_same_epsilon`
then applies the single-sample estimate and rewrites both projections.
It neither multiplies marginal probabilities nor assumes that a survival
gate is independent of the terminal tree.

The final `source_same_epsilon_two_reverse_births` has exactly the source
rate ratio, $\lambda>1$, and $0<\varepsilon<t_0$. For all sufficiently
large $n$, it proves

$$
1-\varepsilon\leq
\mathbb P\bigl(b(V_1)\leq n(t_0-\varepsilon)\bigr)
=\mathbb P\bigl(b(V_2)\leq n(t_0-\varepsilon)\bigr).
$$

The real threshold and non-strict event match the printed formula. An
eventual lower bound by $1-\varepsilon$ is stronger than the printed
$1-\varepsilon+o(1)$ lower estimate. The law is unconditional, retaining
the early-extinction/survival mixture. It is not a statement obtained by
conditioning only on the surviving branch.

The clock is the genuine reverse clock, defined through the forward
freezing timestamp minus one, with the correct active-label convention.
The separate `Observed` results prove that forward chronological membership
is implied by this reverse-clock event. They do not equate the two notions
of birth. The native plane-prefix pair result in `Source` is consequently
separate from the literal reverse-clock pair display.

No mismatch was found in the pair sampling semantics, equality of the two
marginals, threshold/indexing, or quantifier order. The main A77 scalar
route already has a separate parent independent review with six expanded
examples and twelve closures. Subsequently the final `Source`/`ObservedPairs`
artifact batch passed 4,114 jobs in
`capture-source-pairs-one-susceptible-build.log`. The implementing worker's
ordinary imported eight-example/thirty-one-closure probe also passed with
exit zero in `sir-capture-coefficient-statements.log`, with only the standard
three axioms. This is authored imported evidence, not this review's imported
probe; the earlier source-combined check remains separately recorded in
`sir-capture-coefficient-source-statements.log`. This semantic review does
not claim an independent imported kernel probe of the two final modules or
a global publication verdict.

The parent subsequently independently checked the complete A77 interface,
including the literal pair marginals, with seven expanded examples and
fifteen closures. That distinct evidence is recorded in
`SIR_CAPTURE_COEFFICIENT_INDEPENDENT_AUDIT.md` and
`sir-capture-coefficient-independent-statements.log`.
