# Source A60–A61: actual auxiliary Bernoulli coupling

Source scope: `attachement-uniforme-1-final.tex`, lines 1911–1977. This record is an authored source review and proof correspondence record; independent review is requested from the integrating agent. It does not claim whole-paper coverage.

## Mathematical scope

The construction uses the genuine reverse-history transition law. Its augmented sample retains the entire original history and records the first vertex's actual increment and an auxiliary coin. At source step $i$, the first increment has parameter

$$
p_i=rac{mathbf{1}_{{x_i=1}}}{S_i},
$$

and the auxiliary coin has parameter

$$
q_i=rac{mathbf{1}_{{x_i=1}}}{S_i-1}.
$$

Every actual attachment step at or before extinction has $S_igeq2$, so both parameters are valid, including the extinction endpoint. Freeze steps have both parameters zero. Lean transition index $j$ is source step $j+1$; words are stored in descending step order.

`BernoulliPairCouplingKernel` fills an auxiliary coin independently when the two roots already coincide before the step, or when the actual first increment is one. If the roots are distinct and the first increment is zero, the auxiliary coin is the actual second increment. The actual history marginal is unchanged. The proof derives the product law of the first increment and auxiliary coin from their actual Bernoulli marginals, exclusion before coalescence, and $(1-p_i)q_i=p_i$. No conditional independence is assumed.

`BernoulliPairCouplingBlock` iterates those kernels and preserves the whole actual block-history law. The complete first and auxiliary words have independent Bernoulli product laws; every first coordinate is identified with the actual increment of the completed common history. Every second increment satisfies the source's before-step coalescence formula. `BernoulliPairCouplingSeparated` proves joined roots never split and, on distinct bottom roots, the true second block-height gain is at most the auxiliary sum. The distinct-root event is retained throughout; it is never treated as an independent event.

`BernoulliPairCouplingThinning` takes fresh, independent retention coins of parameters $1-p_i$ and defines $\widetilde Y_i=\xi_i\eta_i$. This gives the original independent $p_i$ word law and $\widetilde Y_i\leq\xi_i$ almost surely. `BernoulliPairCouplingComplete` puts these fresh coins on the very same probability space as the original whole history and both driver words. Its driver-triple law is an actual product measure. The original first word and the thinned word are also independent.

## Paper arguments checked

The following source steps now have direct proofs using this construction:

- The actual two-height increment representation, full auxiliary independence, and domination on the separated-bottom-root event.
- Product factorization of the two independent driver-tail events and the final enlarged-tail square bound in `eq:ksi`.
- The monotone thinning construction and equality in law with the first increment family.
- The exact crossing-event identity for the difference of the enlarged and original tail probabilities.
- Markov's bound for the positive integer discrepancy and its exact expectation.
- The reciprocal identity

$$
\mathbb E\!\left[\sum_i(\xi_i-\widetilde Y_i)\right]
=\sum_i(q_i-p_i)
=\sum_i\frac{\mathbf{1}_{\{x_i=1\}}}{S_i(S_i-1)}.
$$

- The uniform $O(1/a)$ discrepancy on fixed-ratio blocks $(a,aC]$, under the source near-origin linear profile and diverging cutoff. The constants are uniform in the two vertices, threshold, row index, and admissible block index.
- The final actual pair-tail bound by the product of its two true marginal tails plus $L/a$, through coalescence decomposition, this coupling, thinning, and Markov. The existing stronger pair supersolution theorem is not used in this proof route. Its earlier alternate verification remains valid and separate.

The explicit finite and asymptotic consumers are in `BernoulliPairCouplingTails`, `BernoulliPairCouplingError`, and `BernoulliPairCouplingConclusions`. Taking $a=C^k$ gives the source geometric blocks. The theorem is proved for every admissible valid starting history, so it applies to the actual Markov continuation without any extra law-identification premise.

## Source correction S24

The prose at line 1915 claims that $Y_i=1$ and $\mathrm{coal}(v,w)\leq i-1$ exclude coalescence with the component of $w$ during that step. Equality $\mathrm{coal}=i-1$ permits exactly such a current merge. `source_current_merge_boundary` proves a concrete event of probability $1/2$ under the actual reverse kernel: the all-attachment schedule with two roots, source step $1$, first increment one, roots merging during that step, and coalescence time zero.

The displayed formula following that prose is preserved. It uses whether the roots were already joined **before** the step, namely $\mathrm{coal}\geq i$. The code expresses that condition by equality of the roots in the predecessor state. The counterexample refutes the prose boundary assertion, rather than the displayed coupling formula.

## Proof evidence and remaining scope

Each frozen component has a direct Lean check with `-DautoImplicit=false`; the integrating agent owns all artifact-writing Lake builds. Root artifact evidence includes `bernoulli-pair-actual-build.log`, `bernoulli-pair-words-build.log`, `bernoulli-pair-block-build.log`, `pair-thinning-separated-component-path-build.log`, and `bernoulli-pair-complete-build.log` in this directory.

`BernoulliPairCouplingStatements.lean` reconstructs five expanded source-facing types and queries 24 transitive axiom closures. Its current ordinary imported direct check passes with exit zero and no diagnostics beyond the requested axiom output, recorded in `bernoulli-pair-coupling-statements.log`. All 24 closures contain exactly `propext`, `Classical.choice`, and `Quot.sound`. The final complete integration build and independent source review are owned by the integrating agent; this authored probe does not replace them.

A62's full tall-root second-moment and variance bookkeeping remains separately tracked by the project inventory, even though its previous stronger actual-process proof is available. The present record specifically certifies the previously bypassed A60–A61 auxiliary-coupling route and preserves S24. Other retained paper obligations and publication checks remain in `FORMALIZATION_REPORT.md`.
