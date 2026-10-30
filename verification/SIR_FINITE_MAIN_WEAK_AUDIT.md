# Independent review of the finite-rate terminal weak limits

Reviewer: `sir_parameter`. This reviewer authored the geometric random-environment estimates, but did **not** author `TwoPointMixtureLimit.lean`, `SIRGeometricSurvivalScalar.lean`, `SIRSampleMarginals.lean`, or `MainSIRUniformSamplesFinite.lean`. The independent verdict below concerns those final assembly modules; it does not relabel the authored geometric inputs as independently reviewed.

Source: T07.I.b, `attachement-uniforme-1-final.tex` lines 2079–2093, with its argument at 2199–2223. Statement fidelity and final weak-limit assembly pass for the constructed embedded epidemic.

The scalar source laws are the exact conditionally uniform samples of the complete terminal plane tree at horizon $2n+1$, divided by $\log n$. `SIRSampleMarginals.lean` proves the second-coordinate marginal equals the actual sampled-height or sampled-pair-distance pushforward. Thus introducing the Boolean early-survival coordinate does not change the scalar law. The pair kernel retains independent uniform choices conditional on the same tree, including equal vertices.

The two limits use the exact constants $\lambda/(\lambda-1)$ and $2\lambda/(\lambda-1)$. Their targets are explicit pushforwards of the same concrete geometric Bienaymé law by the scalar that equals the relevant constant on the event that the tree has infinitely many vertices, and zero otherwise. The geometric law uses attachment probability $\lambda/(1+\lambda)$, hence the source offspring-success parameter $1/(1+\lambda)$. The checked extinction/survival identification supplies the event probability. No fresh event with an assumed distribution is substituted for that concrete survival event.

`TwoPointMixture.marginal_tendsto` proves weak convergence through bounded continuous tests. Its error bound separates concentration near the two possible Boolean-gated values from the bounded-test contribution of the bad event. The root main wrappers supply the proved actual gate-probability and concentration results. The literal source-ratio specializations retain arbitrary rate sequences and derive $n\lambda_n\to\lambda$; they do not replace the sequence by $\lambda/n$.

`SIRFiniteUniformLimitStatements.lean` independently reconstructs two explicit actual-sample identities, two limits with the concrete geometric target expanded, and both literal source-ratio specializations. `sir-finite-uniform-limit-statements.log` passes without diagnostics and reports six closures containing only `propext`, `Classical.choice`, and `Quot.sound`. The root dependency-aware build also passes for the final main module.

These exports are honestly named as embedded results. The physical continuous-time epidemic identification is a separate bridge and is not certified by this review. The different random-environment proof route and the checked manuscript arguments are recorded in `SIR_FINITE_UNIFORM_SAMPLING_NOTES.md`.
