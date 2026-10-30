# A03 finite extinction-conditioned plane example — authored self-review

Scope: source `attachement-uniforme-1-final.tex`, lines 271–274, second Examples bullet. This is an **authored** review by the integrating agent who also wrote the proof; it is not an independent audit. No independent reviewer has read these modules.

## Source claim

For iid symmetric signs, conditionally on the first active-zero time $\tau=n$, $\mathcal T_n(\mathbf X)$ is a uniform plane tree when the plane order is chosen uniformly at random.

## What is proved

All names are in `Freezing1.*`. Files: `FinitePlaneConditionalGeometry`, `FinitePlaneConditionalBounds`, `FinitePlaneAtomMass`, `FinitePlaneUniformLaw`, `FinitePlaneExtinctionTime`, `FinitePlaneConditionedUniform`.

1. `FinitePlaneClass m` (abbrev) is the type of finite plane trees with exactly $m$ vertices, a `Fintype` by coding trees through their offspring values on bounded addresses; nonempty for $m\ge1$ (star).
2. `ForwardAnnealed.planeLimitLaw_atom`: for every $p<1$ and every finite plane tree with $m$ vertices, the **actual** chronological plane limit law of the iid-sign chain gives mass $(1-p)^m p^{m-1}$. It is proved by strong induction on the true vertex count, from `planeLimitLaw_fixedPoint`, the exact preimage of a point under `graft`, and the first-child/remainder vertex-count identity. No assumed Bienaymé law or atom mass.
3. `PlaneForward.ae_vertex_active_time_count`: almost surely, before the first absorption, $2|V_k| = |A_k|+1+k$ (a one-step identity for attachment and for freezing on valid states). Consequently (`ae_extinctionTimeIs_iff_finiteVertexCount`) $\{\tau=2m-1\}$ equals, almost surely, the event that the limiting plane tree is finite with exactly $m$ vertices; the limit equals the held terminal state (`chainLimit_eq_shape_of_absorbed`).
4. `PlaneTree.finitePlaneUniform m` is the explicit average of Dirac masses over `FinitePlaneClass m`; `cond_finitePlaneSet_eq_uniform` shows that a measure with a common nonzero finite atom mass on the class, conditioned on the class, is that uniform law.
5. `ForwardAnnealed.iid_signs_conditioned_extinction_uniform_plane` (and `_at_time`): for $p\in(0,1)$ and $m\ge1$ the event $\{\tau=2m-1\}$ has positive probability, and the law of the terminal plane tree conditioned on it is `finitePlaneUniform m`. `measure_extinctionTimeIs` gives the exact probability $|\mathrm{FinitePlaneClass}(m)|(1-p)^m p^{m-1}$, and `measure_extinctionTimeIs_even` proves even times have probability zero. The source case is $p=1/2$.

## Departures and caveats (not hidden)

- **Chronological order (superseded for the reordering part).** The reordering invariance is now proved by `FinitePlaneShuffle*` (`iid_signs_conditioned_extinction_uniform_plane_shuffled`; see `A03_SHUFFLE_NOTES.md`). The statement of this note is about the plane tree with the paper's own chronological ordering of children (the one used by Theorem BGW/T02). The phrase "when the plane order ... is chosen uniformly at random" would additionally require that an independent uniform reordering of siblings leaves the uniform law invariant. This is true (doubly stochastic kernel on a finite class) but is **not yet formalized**; it stays an open sub-obligation of A03. Planned route: reorder by random insertion of the first child into the recursively shuffled remainder, with exact remove/insert bijections built from `graft`, `child`, `dropFirst`.
- **Annealed formulation.** The theorem is about the actual iid-sign Markov chain `PlaneForward.fullLaw p initial` (signs mixed in, as in T02 `iid_signs_geometric_local_limit`); $\tau$ is a function of the active-count path, so conditioning the annealed law on $\{\tau=n\}$ is conditioning the pair (iid signs, tree) on $\tau(\mathbf X)=n$.
- **Generality.** The proof uses only $0<p<1$; the symmetric case is the source's. For $p>1/2$ extinction is not almost sure; the finite-extinction events still have the stated exact probabilities.
- The source says "for every $n\ge1$"; odd $n=2m-1$ have positive probability, even $n$ probability zero. Both are exported. The source's "non constant" qualifier is not needed (the constant sequence has $\tau=\infty$ and zero probability).

## Evidence

- Direct checks (`lake env lean -DautoImplicit=false`): `FinitePlaneConditionalBounds` (after two local repairs of the stopped draft: explicit `T` arguments, `simp only [C]` for a local `let`), `FinitePlaneAtomMass`, `FinitePlaneUniformLaw`, `FinitePlaneExtinctionTime`, `FinitePlaneConditionedUniform`: exit 0, no diagnostics.
- Artifact builds and the integrated default build include all six modules.
- Authored imported probe `verification/A03FiniteConditionedPlaneStatements.lean`, log `verification/a03-finite-conditioned-plane-statements.log`: exit 0; ten axiom queries all `[propext, Classical.choice, Quot.sound]`. It states, independently of the proof modules' notation, the exact conditional atom mass $1/|\mathrm{class}|$ for each class member, zero mass outside, the time-$n$ reading, parity, and the almost-sure event equivalence.
