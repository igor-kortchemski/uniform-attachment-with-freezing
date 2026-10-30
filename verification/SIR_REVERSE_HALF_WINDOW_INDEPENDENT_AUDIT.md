# Independent review of the SIR half-window reduction

Reviewed source: `attachement-uniforme-1-final.tex`, lines 2275–2285. Reviewed new modules: `SIRReverseHalfWindow.lean` and `SIRCountsExtinctionIndex.lean`; affected definitions and dependencies read: `SIRReversedHeightIdentity`, `SIRLateAttachmentBudget.birthCharge`, the actual `countsFullLaw`, and `SIRStrongCounts.countsFullLaw_triangle_tendsto_zero`. The reviewer did not write the two new modules. This is an independent automated review, not human review.

## Statement fidelity

The original displayed identity is still false under the printed forward index, as already recorded in S14. The feasible one-infection/two-recovery counterexample gives $1/2$ for that forward charge and zero for its claimed reverse expression. The new work does not certify that identity. It uses the corrected pre-step birth charge

$$
\sum_{i=n}^{\tau-1}\frac{\mathbf{1}_{\{U_{i+1}<U_i\}}}{I_i}.
$$

With the source reverse index $j=\tau-i$, this is exactly

$$
\sum_{j=1}^{\tau-n}\frac{\mathbf{1}_{\{U_{\tau-j+1}<U_{\tau-j}\}}}{I_{\tau-j}}.
$$

`intervalBirthCharge_lastHalf_reverse` has the exact upper limit $\min(\lfloor n/2\rfloor,\tau-n)$ and the same denominator and event. Natural subtraction and empty interval sums correctly handle $\tau<n$, $n=0$, and zero-length windows. These finite initial cases are retained, rather than hidden behind an asymptotic restriction.

`boundedExtinctionIndex` is total on arbitrary histories through a deterministic sentinel at $2n+1$. It is measurable. On the actual count-history law, the proved absorption theorem gives $I_{2n+1}=0$, so the sentinel definition is exactly the first infectious-population zero. The exported almost-sure theorem proves both zero at the index and strict positivity at every earlier index. It adds no survival, reverse-law, or assumed extinction premise to the actual-process conclusion. The bound $2n+1$ matches the model's initial state of $n$ susceptibles and one infectious vertex.

## Proof correspondence

The source says the stopped triangle fluid limit makes the omitted early part negligible. The new proof checks precisely that step. For every candidate $\tau\leq2n+1$, the split point is

$$
\tau-\min(\lfloor n/2\rfloor,\tau-n).
$$

Its upper bound is $n+\lfloor n/2\rfloor+2$. For $n\geq8$, the actual triangle-profile good event with error $n/8$ bounds the infectious population below by $n/8$ on the early summation interval. Each birth charge is at most $8/n$, and the sum is bounded by the explicit constant $16$. No assertion about reversed increments enters this estimate.

The stochastic early-remainder theorem derives its exceptional event from the actual stopped-chain triangle theorem under $n\lambda_n\to\infty$. It works uniformly over every $\tau\leq2n+1$, hence at the genuine first-zero index. Eventual positivity of $\log n$ and divergence of $\varepsilon\log n$ are proved where division is used. There is no conditioning on future extinction or on an auxiliary event.

`countsFullLaw_late_charge_reduced_to_lastHalf` is correctly a sufficiency theorem. It takes convergence of the last-half charge as an explicit premise and proves convergence of the entire corrected post-$n$ charge by the exact split and a union bound at tolerance $\varepsilon/2$. Thus the source statement “it suffices to prove” is checked. This theorem does not purport to prove its last-window premise.

## Coverage verdict and limits

The corrected deterministic reversal, exact finite half-window, genuine first-zero carrier, fluid negligibility of the early remainder, and logical last-window reduction are faithful and proved. This closes the previously retained corrected A84 half-window argument. The literal printed reversed-sum equality remains refuted. The actual reverse iid domination under random extinction in A85 and the resulting localized source argument in A86 remain separate obligations; they are not implied by this milestone. The already proved forward harmonic-budget route to the full late-charge limit remains an alternative proof.

The independently reconstructed probe is `SIRReverseHalfWindowIndependentStatements.lean`: five expanded examples and ten transitive axiom queries. Its ordinary imported direct check passes with exit zero and no diagnostics beyond the requested axiom output, recorded in `sir-reverse-half-window-independent-statements.log`. The bounded-index definition is axiom-free; the other nine closures contain exactly `propext`, `Classical.choice`, and `Quot.sound`. Root artifact evidence for the reviewed modules is `sir-half-window-reverse-word-build.log` (3,948 jobs).
