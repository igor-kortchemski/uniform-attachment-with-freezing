# A03 uniform plane reordering: definition, faithfulness, proof route, evidence

Source: `attachement-uniforme-1-final.tex`, lines 271-274, second Examples bullet: for iid symmetric signs, conditionally on $\tau=n$, $T_n$ is a uniform plane tree when the plane order among the vertices of $T_n$ is chosen uniformly at random.

The already proved theorem `ForwardAnnealed.iid_signs_conditioned_extinction_uniform_plane` gives the conditional law of the **chronological** plane tree (uniform on the class of finite plane trees with $m$ vertices, for $\tau=2m-1$). The new modules prove that an independent uniform reordering of the children at every vertex leaves that uniform law invariant, which is the part of the source statement that concerns a **uniformly random** plane order.

## Files

- `Freezing1/FinitePlaneShuffleDef.lean`: tree from a list of children, independent product, uniform permutation law, the recursive reordering `shufflePMF`.
- `Freezing1/FinitePlaneShuffleLaw.lean`: one-level formula for the transition mass, finiteness and vertex-count preservation, symmetry, doubly stochastic matrix on the finite class.
- `Freezing1/FinitePlaneShuffleUnordered.lean`: the law depends only on the unordered tree.
- `Freezing1/FinitePlaneShuffleMain.lean`: measure wrapper `shuffleLaw`, Markov kernel, invariance of `finitePlaneUniform m`, final A03 statement.
- `verification/A03ShuffleStatements.lean` and `verification/a03-shuffle-statements.log`: authored exact-type probe and its log.

## Definition

Notation: `child T j` is the $j$-th child subtree (1-indexed), `degree T` the root degree, `graft A B` puts `A` as new first child of the root of `B`.

- `ofList : List Tree → Tree` (`[] ↦ leaf`, `A :: L ↦ graft A (ofList L)`) and `ofChildren A := ofList (List.ofFn A)` for `A : Fin d → Tree` rebuild a tree from the ordered list of its children. Proved: `degree_ofChildren`, `child_ofChildren` (the $(i+1)$-th child of `ofChildren A` is `A i`), `ofChildren_child_eq` (every tree of degree $d$ is `ofChildren` of its $d$ children), `ofChildren_eq_iff`, and the count formula $|ofChildren\ A| = 1+\sum_i |A_i|$.
- `piFin n μ : PMF (Fin n → α)` is the independent product of $n$ laws (proved: mass $\prod_i \mu_i(f_i)$, `piFin_apply`).
- `uniformPerm d : PMF (Equiv.Perm (Fin d))` is uniform (mass $1/d!$ each, `uniformPerm_apply`). (`PMF.uniformOfFintype` is deprecated in the pinned Mathlib, so it is defined directly with `PMF.ofFintype`.)
- `shufflePMF : Tree → PMF Tree` is defined by well-founded recursion on `finiteVertexCount`:

$$\mathrm{shuffle}(T)=\text{if } T \text{ has finitely many vertices: }\ (\sigma,A)\mapsto \mathrm{ofChildren}\big(i\mapsto A_{\sigma(i)}\big),\ \ \sigma\sim\mathrm{Unif}(\mathfrak S_d),\ A\sim\bigotimes_{i=1}^{d}\mathrm{shuffle}(T_i),$$

  with $d=$ `degree T`, $T_i=$ `child T i`, and $\sigma$ independent of $A$ (`shufflePMF_of_finite`, literally the unfolding equation). Otherwise `shufflePMF T = PMF.pure T`.
- `shuffleLaw T : Measure Tree := (shufflePMF T).toMeasure`, a probability measure (instance), proved measurable `measurable_shuffleLaw`, hence `shuffleKernel : Kernel Tree Tree`.
- **Junk case, stated:** for a tree with infinitely many vertices the "reordering" is the identity (`shuffleLaw_of_not_finite : shuffleLaw T = Measure.dirac T`). No claim is made for infinite trees; all invariance statements are for finite plane trees.

## Faithfulness to "independent uniform permutation of the children at every vertex"

1. Unfolding the recursion at a finite tree gives exactly: reorder each child subtree recursively (the $d$ child reorderings are independent: product measure `piFin`), then permute the $d$ children by one uniform $\sigma\in\mathfrak S_d$ independent of the child reorderings. Unrolling to the leaves, every vertex of $T$ gets its own uniform permutation of its own children, independent over vertices (independence across vertices is the product structure, independence of a vertex's permutation from its descendants' is the `bind` over `σ` of a law not depending on `σ`). Faithful uniform-permutation form (not the random-insertion variant), so no extra one-level lemma is needed.
2. The transition mass is the explicit formula `shufflePMF_apply_eq` (for trees with the same root degree $d$)
$$K(T,S)=\frac1{d!}\sum_{\sigma\in\mathfrak S_d}\prod_{j=1}^{d}K(T_j,S_{\sigma^{-1}(j)}),$$
and $K(T,S)=0$ if the root degrees differ (`shufflePMF_apply_of_degree_ne`). Sanity: `shufflePMF_leaf : shufflePMF leaf = pure leaf`.
3. Independence of the plane representative. "Choose the plane order of the unordered tree $T_n$ uniformly at random" is the same as "reorder the children of any plane representative of $T_n$ uniformly". `SameUnordered T T'` (recursively: same root degree and a permutation of the children matching child subtrees up to `SameUnordered`) is the notion of equality of unordered rooted trees used. Proved: `SameUnordered.shufflePMF_eq : SameUnordered T T' → FiniteVertices T → shufflePMF T = shufflePMF T'`, and the one-level corollary `shufflePMF_ofChildren_perm` (permuting the root children does not change the law). So reordering the chronological plane tree is the uniformly random plane order of the underlying unordered tree $T_n$.

## Proof route (differs from the suggested tuple bijection, avoids it)

Instead of a bijection between trees of degree $d$ and size $m$ and $d$-tuples of trees, double stochasticity is obtained from the **symmetry** of the kernel:

1. One-level formula (`shufflePMF_apply_eq`): from `PMF.bind_apply`, `PMF.map_apply`, `piFin_apply`; the sum over the child tuples collapses to the single tuple $A_j=S_{\sigma^{-1}j}$ because `ofChildren` is injective on children (`ofChildren_eq_iff`).
2. Finiteness and vertex-count preservation (`shufflePMF_support`, `finiteVertices_of_shufflePMF`): strong induction on `finiteVertexCount`, using the formula, `finiteVertexCount_child_lt`, the count formula $|T|=1+\sum_i|T_i|$ (`finiteVertexCount_eq_one_add_sum`, via `ofChildren_child_eq` and `finiteVertexCount_graft`) and `Equiv.sum_comp` for the permutation.
3. Symmetry $K(T,S)=K(S,T)$ for finite $T,S$ (`shufflePMF_symm`): strong induction using the induction hypothesis on all child pairs, `Equiv.prod_comp` ($j=\sigma k$) and the substitution $\sigma\mapsto\sigma^{-1}$ in the sum.
4. Rows sum to one (`sum_shuffleMatrix_row`, from `PMF.tsum_coe` and the support in the class), hence by symmetry columns do (`sum_shuffleMatrix_column`): the matrix on `FinitePlaneClass m` is doubly stochastic.
5. Invariance (`finitePlaneUniform_bind_shuffleLaw`): `Measure.bind_apply`, `lintegral` against the Dirac sum, `shuffleLaw_apply_class` (the law restricted to the class is the finite sum), exchange of the finite sums and the column-sum identity.
6. Final statement: rewrite the conditioned law with the already proved uniform theorem, then apply invariance.

## Exported statements (exact types)

```lean
theorem Freezing1.PlaneTree.finitePlaneUniform_bind_shuffleLaw (m : ℕ) :
    (finitePlaneUniform m).bind shuffleLaw = finitePlaneUniform m

theorem Freezing1.ForwardAnnealed.iid_signs_conditioned_extinction_uniform_plane_shuffled
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (m : ℕ) (hm : 1 ≤ m) :
    0 < PlaneForward.fullLaw p PlaneForward.initial {H | ExtinctionTimeIs (2 * m - 1) H} ∧
      (((PlaneForward.fullLaw p PlaneForward.initial)[|{H | ExtinctionTimeIs (2 * m - 1) H}]).map
          PlaneForward.chainLimit).bind shuffleLaw = finitePlaneUniform m
```

The invariance holds for every $m$ (for $m=0$ the class is empty and both sides vanish); the probe restates it with the hypothesis `1 ≤ m`.

## Evidence

All commands run from the repository root; Lean/Mathlib v4.35.0, `-DautoImplicit=false`.

| Item | Check | Result |
| --- | --- | --- |
| `Freezing1/FinitePlaneShuffleDef.lean` (208 lines) | `lake env lean -DautoImplicit=false` | exit 0, no output |
| `Freezing1/FinitePlaneShuffleLaw.lean` (203 lines) | same | exit 0, no output |
| `Freezing1/FinitePlaneShuffleUnordered.lean` (101 lines) | same | exit 0, no output |
| `Freezing1/FinitePlaneShuffleMain.lean` (159 lines) | same | exit 0, no output |
| artifacts | `bl.sh Freezing1.FinitePlaneShuffleUnordered`, then `bl.sh Freezing1.FinitePlaneShuffleMain` (lock wrapper) | both `Build completed successfully` |
| `verification/A03ShuffleStatements.lean` | same direct check | exit 0, log `verification/a03-shuffle-statements.log`: 23 `example`s elaborate, 14 `#print axioms` all `[propext, Classical.choice, Quot.sound]` |

No `sorry`, no custom axiom, no `native_decide`/`bv_decide`, no `import Mathlib`. Only the specific Mathlib/Freezing1 modules are imported.

## Caveats

- Infinite trees: reordering is the identity (junk, stated above and proved as `shuffleLaw_of_not_finite`).
- `SameUnordered` is a self-contained recursive notion of unordered equality on `PlaneTree.Tree`; it is not connected to the project's separate unordered-tree quotient (`UnorderedLocal`, A20), so a bridge between the two is not claimed.
- The final statement inherits from the earlier theorem the hypotheses $0<p<1$ and the encoding "extinction time $2m-1$ ⇔ $m$ vertices" (the source writes $\tau=n$ and counts vertices as in the chronological construction). The reordering step itself makes no assumption beyond finiteness.
- Nothing was added to `Freezing1.lean` or `FORMALIZATION_REPORT.md` (out of scope for this worker). Integration needs `import Freezing1.FinitePlaneShuffleMain` and a report entry that A03's uniform-plane-order obligation is now proved.
- The finite-class doubly stochastic property is proved through symmetry (and the explicit one-level formula), not through the tuple bijection route.
