# Joint adaptive tree-prefix review

Independent reviewer: the `sir_parameter` worker, which did not author `SIRTreePrefixWordMixture.lean` or `SIRTreePrefixWordObservations.lean`. The review concerns the discrete history component of source A66, together with its use for T07.I.b. Statement fidelity and the reconstructed joint observations pass.

`conditionalTreePrefixWordLaw` recursively appends an actual `signedTreeLaw` update. Its phase theorem identifies **every** count coordinate with `countsPrefixWord`, rather than only the endpoint. Mixing uses the Bernoulli parameter determined by that same count history. The exact entire-prefix mixture therefore preserves the dependence of the event signs on earlier infections. The feasible-word event has full actual sign-word measure and is used when identifying the conditional plane-tree law. Absorption and arbitrary horizons remain in the statements.

`SIRTreePrefixWordStatements.lean` independently reconstructs the full-prefix equality, all count coordinates, and the joint integral of an earlier infectious-count survival gate with a final uniform height or pair-distance observation. Both pair samples are from the same terminal plane state, using `PlaneForward.pairDataKernel`, which retains conditional independence and diagonal pairs. The final observation was not combined with a gate by appealing to separate marginals.

The direct check in `sir-tree-prefix-word-statements.log` passes without diagnostics; all four reconstructed closures use only `propext`, `Classical.choice`, and `Quot.sound`. This checks the embedded discrete model. The independent-exponential or Poisson continuous-time history identification is a separate bridge outside this review.
