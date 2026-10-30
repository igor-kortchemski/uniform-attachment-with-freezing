# Independent review of A03: finite conditioned plane trees

Verdict: **no blocking mathematical or statement-fidelity finding in this scope**.
The finite-extinction-conditioned uniform plane-shape example, including the
independent uniform reordering of siblings, is proved with the necessary
parity and positive-conditioning-mass qualifications. This is a scoped review;
it does not certify whole-paper coverage or publication readiness.

The reviewer did not author the mathematical modules. This review independently
read source lines 271–274 of `attachement-uniforme-1-final.tex`, unchanged
SHA-256 `88953dd87165a14b0e643c5b3d0075d8ce5ec39cdcfc0c25d313570fc3ab00df`,
and inspected the new finite-plane geometry, bounds, atom mass, uniform law,
extinction-time and shuffle definitions and proofs. It also checked the relevant
existing full-history plane projection and annealed-history interpretation.

The source's symmetric iid case is the specialization $p=1/2$ of the proved
case $0<p<1$. If the first zero occurs at time $n$, its tree has
$(n+1)/2$ vertices and $n$ is odd. The formalization uses $n=2m-1$,
$m\geq1$, proves strictly positive conditioning mass there, and separately
proves even times have probability zero. It never treats conditioning on an
impossible even time as a probability law with the advertised distribution.
The tree being uniform is its ordinary unlabelled plane shape; no uniformity
of edge timestamps or freezing labels is claimed.

The target carrier is all finite Ulam plane trees with exactly $m$ actual
vertices, not an inductively generated subclass whose completeness is assumed.
`FinitePlaneConditionalBounds.lean:109` defines the full subtype. Bounded
addresses and bounded offspring counts give an injective finite coordinate
map, hence its finite type. `finitePlaneUniform` at
`FinitePlaneUniformLaw.lean:46` is the normalized sum of Dirac masses over
this entire subtype; its probability property uses $m\geq1$ explicitly.

`planeLimitLaw_atom` derives the exact atom mass
$(1-p)^m p^{m-1}$ from the already proved actual-chain fixed-point law,
the singleton preimage under grafting and actual vertex-count induction.
There is no assumed atom estimate, assumed uniformity, or extra branching-law
premise in the final result. The vertex/active/time invariant
$2|V_k|=|A_k|+1+k$ is proved from both true legal transition types before
first extinction. The almost-sure event equivalence at
`FinitePlaneExtinctionTime.lean:125` identifies the genuine first zero with
the limiting shape having exactly $m$ vertices. Absorption and uniqueness of
the limit justify observing the actual tree at time $2m-1$ itself.
Thus the conditional theorem is not inferred from a limiting marginal alone.

The annealed formulation uses the actual chronological plane Markov history.
The previously proved full finite-history iid-sign mixture and the complete
map to the plane history (`ForwardAnnealedHistory.lean:111`,
`ForwardPlaneHistory.lean:119`) identify this model with the original iid
schedule construction. First extinction depends on its active-count history.
No independence after conditioning on extinction is assumed.

The reordering at `FinitePlaneShuffleDef.lean:184` is an actual recursive
random procedure: a product of the child-subtree reordering laws and a fresh
uniform permutation of all root children. The product atom identity is
proved, as is the uniform permutation law. Unrolling the finite recursion
therefore gives independent uniform sibling permutations at every vertex,
rather than an arbitrarily chosen invariant kernel. The output preserves
finiteness and vertex count. Symmetry of the finite transition matrix gives
its column sums and hence invariance of the full finite uniform law.

The final shuffled statement (`FinitePlaneShuffleMain.lean:149`) retains
the true extinction conditioning. The independent probe additionally composes
the time-$2m-1$ observation with this kernel and expands the target into the
complete normalized Dirac sum. The infinite-tree identity fallback for the
shuffle is outside the finite conditioning support; its characterization is
explicit. The auxiliary recursive `SameUnordered` relation is used only in
the finite-tree setting. Its separate identification with the project's A20
unordered quotient is not claimed by this review and is not needed to carry
out the sibling-permutation procedure on the actual chronological tree.

Current evidence:

- The root's fresh default artifact build passes 4,631 jobs, including all
  reviewed modules: `verification/codex-review-build.log`.
- `verification/CodexA03IndependentStatements.lean` independently reconstructs
  six statements: completeness/finiteness of the shape carrier, exact atoms,
  the first-zero/size event equivalence, the at-extinction-time shuffled law,
  positive odd-time mass, and even-time nullity.
- Its actual imported check, `lake env lean -DautoImplicit=false
  verification/CodexA03IndependentStatements.lean`, exits zero. The nine
  queried transitive closures use only `propext`, `Classical.choice`, and
  `Quot.sound`; output is in `verification/codex-a03-independent-statements.log`.
- No proof module was modified in this review. Only this note and the
  independent statement probe were added.

The mechanical evidence is ordinary Lean compilation and axiom inspection,
not independent kernel replay, Comparator verification, or a Palomar report.
