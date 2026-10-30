# Independent review of A06 and the new A87 moment recursion

The reviewer independently read source lines 286, 316–357 and 2326–2330,
the four `LinearBush*` modules, `ForwardActiveHeightMgf`, the relevant
sampling/height definitions and the current coverage entries. The reviewer
did not author these implementations and did not modify proof sources.
The source and declared whole-paper scope are unchanged.

## Verdict

The new finite-sampling, GH non-tightness and fixed-state generating-function
results are mathematically meaningful and passed the current imported
checks. No false axiom, hidden tail estimate or broken mathematical encoding
was found in this scope. They do **not** complete the whole source A06 or
the original conditional stochastic-domination claim in A87.

## A06: genuine proved scope and remaining bridges

`LinearBushSamplingMatrix.lean:97` samples the actual finite vertex set
independently given one actual forward tree, then records all pair distances.
The diagonal is zero, and repetitions among sampled vertices remain included.
The pair projection is derived from the actual product measure. The finite
union argument at line 240 proves convergence of every finite matrix to
the deterministic matrix with off-diagonal entry $(c+1)/c$.

`LinearBushGHPacking.lean:95` proves a true uniform packing bound on compact
subsets of Mathlib's GH space, using a finite net and realized GH distances.
`LinearBushGHTree.lean:74` equips the actual vertex set with graph distance
divided by the positive scale; connectivity is derived under the actual
tree law. The triangle and zero-distance axioms use genuine graph
reachability. The default value at line 102 is used only on invalid states
or at vanishing/nonpositive logarithmic scales; the actual asymptotic proof
supplies validity and eventually positive logarithms.

The compact-escape statement at line 154 and
`linear_not_isTightMeasureSet` at line 217 concern the actual pushforward
probability laws on the Borel GH space. They are stronger than merely
showing a particular sampled configuration fails to be compact.

**Open coverage, blocking a complete A06 verdict:** these modules do not
define the measured GHP space or prove the continuous forgetful map from
it to GH. Thus the final GHP non-tightness inference remains outside Lean.
Similarly `longDendronMatrix` and `longDendronSampleLaw`
(`LinearBushSamplingMatrix.lean:38,54`) define matrix formulas directly;
they do not construct a long dendron or prove their equivalence to Janson's
object/topology. No formal theorem of convergence in that named topology
is exported. The current A06 row accurately marks these parts partial.

One documentary correction is warranted: the A06 row calls strict `hτ`
slightly stronger than the paper. The standing setup at source line 286
already requires $\tau(X^n)>n$. The same strict assumption in these
linear-regime theorems is faithful; no additional finite-row repair was
found necessary here.

## A87: moment identity is not an exported stochastic-order theorem

The one-step calculations at `ForwardActiveHeightMgf.lean:75,107` are
consistent with the original transition: attachment multiplies the active
height generating function by $(S+c)/(S+1)$, while uniformly deleting an
active vertex leaves its average unchanged in expectation when the active
set survives. The positivity hypotheses supply that condition.

The exact recursion at line 219 uses an arbitrary valid initial state
with the actual active population, the original fixed schedule and genuine
future transition kernels. There is no assumed moment or tail bound.
The newborn identity at line 261 adds one deterministic edge. The final
bound at line 319 has exactly the form

$$
\mathbb E[c^{H_{n+k+1}}]\leq
c^{H+1}\prod_{i=0}^{k-1}\left(1+p_i(c-1)\right),\qquad c\geq1,
$$

where $p_i$ is zero at freezing steps and $1/S_{n+i+1}$ at attachment
steps, with $S$ read **after** that step. The deterministic extra edge and
the index convention are essential for interpreting this corrected result.

**Coverage finding:** the exported type is an exponential-moment inequality,
not stochastic ordering of the newborn height against an explicitly
independent Bernoulli sum. Bounds on these increasing exponential tests
alone are not a general characterization of first-order stochastic order.
The stronger exact generating-function identity can support a further
law-identification proof, but that proof and its resulting tail-order
statement have not been exported. A repository search found no consumer
of the new `treeLawFrom` identities outside this module. In particular the
new module does not itself instantiate a conditional law under the random
SIR extinction index and count trajectory.

Accordingly the bold report phrase “per-vertex conditional domination now
proved” and module introduction at lines 13–17 should be read or revised
to say **fixed-state generating-function identity and corrected moment
bound proved**. The row's following qualification, saying no stochastic
ordering/coupling is constructed, is accurate. The original A87 stochastic
domination and future-conditioned random-mean argument remain uncertified.
This is a missing formal bridge, not a refutation of the corrected target.

## Current proof evidence

Root's fresh artifact build passed all 4,631 default jobs. The independent
`CodexBushMgfStatements.lean` probe reconstructs three exact statements:
the expanded same-tree sampling kernel with literal star entries, the
actual Borel GH-law non-tightness, and the newborn moment bound specialized
to the true initial tree maximum. It passed ordinary imported checking
with exit zero in `codex-bush-mgf-statements.log`; seven queried transitive
closures contain only `propext`, `Classical.choice`, `Quot.sound`.

The review checks statement meaning and the described proof mechanisms.
It is not independent kernel replay, Comparator or Palomar verification,
nor a whole-paper coverage verdict.
