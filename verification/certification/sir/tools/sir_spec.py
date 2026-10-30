
def tgt(mod, a, b):
    t = src(mod, a, b)
    for suf in (' := by', ' :='):
        if t.endswith(suf):
            t = t[:-len(suf)]
            break
    else:
        raise SystemExit('bad target end ' + mod + str(a))
    return t + ' := by\n  sorry'


SET = 'set_option backward.isDefEq.respectTransparency false'
GM = 'set_option bootstrap.genMatcherCode false in\n'
import os
COUNTS = os.environ.get('COUNTS', '0') == '1'
TREE = os.environ.get('TREE', '0') == '1'
FIRST = os.environ.get('FIRST', '1') == '1'

emit('''module

public import Mathlib.Tactic
public import Mathlib.Tactic.DeriveCountable
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.SetTheory.Descriptive.Tree
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
public import Mathlib.Topology.UnitInterval
public import Mathlib.Order.Hom.Set

/-!
# Challenge: the stochastic SIR infection tree (Theorems `thm:SIRlocallimit` and `thm:SIR`)

Source: *Uniform attachment with freezing*, `attachement-uniforme-1-final.tex`, Section "Application:
contact-tracing in a stochastic SIR dynamics". Statements (for the *physical* epidemic): Theorem
`thm:SIRlocallimit` (I), (II) and Theorem `thm:SIR` (I)(a), (I)(b), (II)(a), (II)(b); nothing else.

For each `n`, `Ω n` is a probability space carrying, for every directed clock slot `c` of the `n + 1`
individuals, a random datum `X n c`: the infectious period (a real number) for a recovery slot, an
entire arrival path (the contact process of `v` towards `w`, indexed by the infection age of `v`) for a
contact slot. `PoissonSIRData (mu n) n (rate n) (X n)` says that all these data are independent, that
infectious periods are exponential of parameter one and that every contact path has Poisson counting
marginals of intensity `rate n`. The epidemic is the deterministic protocol `poissonFullContactRun`:
individual `0` is infectious at the start; at each step the earliest live clock of an infectious
source fires (a recovery, or the next point of a contact path after the current infection age,
towards a still susceptible individual) and the tree and the counts are updated. The laws
`physical...Law` are pushforwards of `mu n` by this protocol. The limits are `geometricProbabilityLaw`,
`geometricSurvivalPathLaw`, `geometricSurvivalScalarLaw`. Two extra target theorems are sanity checks
on `PoissonSIRData` (not manuscript statements): `PoissonContact.first_law` (Poisson counting marginals
give exponential first arrivals) and `PoissonSIRData.treePathLaw_eq` (the physical history (susceptible
count, infection tree) is the paper's chain of uniform attachment with freezing driven by the Markov
chain `(U, I)`).

The theorem bodies are holes. Technical remarks (no statement is affected). The development's
declarations are copied verbatim, but Lean derives auxiliary names from the module being compiled, so that
(i) `run_cmd ... setMainModule` lines make the private auxiliary declarations (from `omega`, `simp`,
`deriving Countable`) carry the name of the development module they come from, (ii) the matchers of
`Present` and `ClockDatum` are generated with `bootstrap.genMatcherCode false` and the matcher
`advanceClockFrame.match_1` and the proof `geometricSurvivalScalarLaw._proof_1` are written out, since
Lean otherwise shares them with an earlier identical one within a single file. See `NOTES.md`.
-/

@[expose] public section

set_option linter.style.haveILetI false
set_option linter.auxLemma false
''')
emit()

# ---------------------------------------------------------------- Plane trees
emit('/-! ## Plane trees -/')
emit()
block(['namespace Freezing1.PlaneTree', 'open Filter MeasureTheory Set', 'open scoped Topology Classical', SET], [
    D('''An Ulam--Harris address: the finite list of child indices (each `≥ 1`) leading from the root
of a plane tree to one of its vertices; the root is the empty list.''', src('PlaneTree', 25)),
    D('The discrete sigma-algebra on the countable set of addresses.', src('PlaneTree', 27)),
    src('PlaneTree', 28),
    D('An offspring field gives a number of children `f u` to every address `u`.', src('PlaneTree', 30)),
    D('''A canonical offspring field: an address `u ++ [j]` which is not one of the `f u` children
`1 ≤ j ≤ f u` of `u` has offspring count zero.''', src('PlaneTree', 32, 33)),
    D('''Locally finite rooted plane trees, encoded by their canonical offspring fields (number of
children of the vertex at each address; zero at absent addresses). The topology is the subspace
topology of the product topology on `Address → ℕ` (`ℕ` discrete): the topology of local convergence.''',
      src('PlaneTree', 50)),
    D('The sigma-algebra on plane trees is the Borel sigma-algebra of the local topology.',
      src('PlaneTree', 53, 54)),
    D('The degree of a tree: the number of children of its root.', src('PlaneTree', 56)),
    D('The tree reduced to its root.', src('PlaneTree', 63)),
    D('The subtree rooted at the `j`-th child of the root.', src('PlaneTree', 90, 93)),
], 'end Freezing1.PlaneTree')

block(['namespace Freezing1.PlaneTree', 'open MeasureTheory', 'open scoped Classical'], [
    D('''Pruning of an offspring field: the count at `u` is kept if `u` is an existing vertex (each
index along `u` is an existing child index of its parent) and replaced by `0` otherwise.''',
      src('PlaneTreePruning', 20, 22)),
    src('PlaneTreePruning', 24, 35),
    D('The plane tree obtained by pruning an offspring field.', src('PlaneTreePruning', 37)),
], 'end Freezing1.PlaneTree')

block(['namespace Freezing1.PlaneTree', 'open scoped Classical'], [
    D('''`Present T u`: the address `u` is a vertex of `T`; the empty address is the root, and `j :: u`
is a vertex iff `1 ≤ j ≤ degree T` and `u` is a vertex of the `j`-th subtree.''',
      GM + src('PlaneTreeGeometry', 20, 22)),
], 'end Freezing1.PlaneTree')

block(['namespace Freezing1.PlaneTree', 'open MeasureTheory ProbabilityTheory',
       'open scoped ENNReal Classical'], [
    D('The product law over all addresses of independent offspring counts with common law `μ`.',
      src('PlaneBienaymeLaw', 22, 23)),
    src('PlaneBienaymeLaw', 25, 28),
    D('''The Bienaymé (Galton--Watson) tree law with offspring law `μ`: the pruning of an iid
offspring field.''', src('PlaneBienaymeLaw', 30, 31)),
    src('PlaneBienaymeLaw', 33, 36),
    D('''The Bienaymé tree law with geometric offspring law `G(1 - p)`, `μ(k) = (1 - p) p ^ k`
(Mathlib's `geometricMeasure` with success probability `1 - p`).''', src('PlaneBienaymeLaw', 54, 55)),
    src('PlaneBienaymeLaw', 57, 60),
], 'end Freezing1.PlaneTree')

block(['namespace Freezing1.PlaneTree', 'open MeasureTheory Filter', 'open scoped Classical'], [
    D('The tree has finitely many vertices (the set of present addresses is finite).',
      src('PlaneFiniteExtinction', 25)),
], 'end Freezing1.PlaneTree')

# ---------------------------------------------------------------- PlaneForward
emit('/-! ## Finite plane states and uniform sampling of their vertices -/')
emit()
block(['namespace Freezing1.PlaneForward', 'open PlaneTree', 'open scoped Classical'], [
    D('''A raw finite state of the growing tree: the finite set of addresses created so far and its
subset of active (not yet frozen) addresses.''', src('PlaneFiniteState', 21, 24)),
    D('The discrete sigma-algebra on finite states.', src('PlaneFiniteState', 26, 27)),
    D('The state consisting of the root only, which is active.', src('PlaneFiniteState', 29)),
    D('The vertices of `s` that are direct children of `u`.', src('PlaneFiniteState', 31, 32)),
    D('The number of children of `u` among the vertices of `s`.', src('PlaneFiniteState', 34)),
    D('The address `u ++ [childCount s u + 1]` of the next child of `u`.', src('PlaneFiniteState', 36, 37)),
    D('Attach a new active child to `u`.', src('PlaneFiniteState', 39, 40)),
    D('Freeze `u`: remove it from the active set, keeping the vertices.', src('PlaneFiniteState', 42)),
    D('''Ulam--Harris validity of a finite state: the root is a vertex, active vertices are vertices,
the vertex set is prefix closed, and the children of `u` are exactly `u ++ [j]`, `1 ≤ j ≤ childCount s u`.''',
      src('PlaneStateValidity', 20, 25)),
    src('PlaneStateValidity', 27, 32),
    src('PlaneStateValidity', 34, 36),
    src('PlaneStateValidity', 38, 43),
    D('''The plane tree whose offspring counts are the child counts of a valid state (the leaf for an
invalid state).''', src('PlaneStateValidity', 45, 46)),
], 'end Freezing1.PlaneForward', fake='Freezing1.PlaneFiniteState')

block(['namespace Freezing1.FiniteUniform', 'open MeasureTheory', 'open scoped ENNReal Classical'], [
    src('FiniteUniformPairs', 20, 26),
], 'end Freezing1.FiniteUniform', fake='Freezing1.FiniteUniformPairs')

block(['namespace Freezing1.PlaneForward', 'open MeasureTheory ProbabilityTheory',
       'open scoped ENNReal Classical'], [
    D('''The parent--child graph on addresses: two vertices of `s` are adjacent when one is the other
extended by one index.''', src('PlaneFiniteGraph', 23, 33)),
    D('''The pair kernel of a finite state. For a nonempty vertex set take two independent uniform vertices
`u`, `v` (the diagonal `u = v` is allowed) and return `(|u|, |v|, dist u v)`, the two heights and the graph
distance in the parent graph; for an empty vertex set return `(0, 0, 0)`.''',
      src('PlaneFiniteGraph', 35, 41)),
    src('PlaneFiniteGraph', 43, 51),
], 'end Freezing1.PlaneForward', fake='Freezing1.PlaneFiniteGraph')

if TREE:
    block(['namespace Freezing1.PlaneForward', 'open MeasureTheory ProbabilityTheory',
           'open scoped ENNReal Classical', SET], [
        src('ForwardPlaneKernel', 25, 30),
    ], 'end Freezing1.PlaneForward', fake='Freezing1.ForwardPlaneKernel')

block(['namespace Freezing1.InterleavedChain', 'open MeasureTheory ProbabilityTheory',
       'open scoped ENNReal Classical', src('InterleavedChainCylinders', 22)], [
    src('InterleavedChainCylinders', 24, 25),
    src('InterleavedChainCylinders', 27, 28),
], 'end Freezing1.InterleavedChain')

block(['namespace Freezing1.PlaneForward', 'open MeasureTheory ProbabilityTheory',
       'open scoped ENNReal Classical'], [
    D('''The vertex-height kernel of a finite state: the law of the height (address length) of a uniformly
chosen vertex among all vertices, frozen ones included; `δ₀` for an empty vertex set.''',
      src('MainSIRUniformHeightStrong', 20, 23)),
    src('MainSIRUniformHeightStrong', 25, 38),
], 'end Freezing1.PlaneForward', fake='Freezing1.MainSIRUniformHeightStrong')

# ---------------------------------------------------------------- SIR counts / tree states
emit('/-! ## Counts, labelled population, infection probabilities, fluid profile and path space -/')
emit()
block(['namespace Freezing1.SIR'], [
    D('The numbers `(U, I)` of susceptible and infectious individuals.', src('SIRCounts', 20, 23)),
    D('The discrete sigma-algebra on counts.', src('SIRCounts', 25, 26)),
] + ([
    D('The initial counts `(n, 1)`: `n` susceptibles and one infectious individual.', src('SIRCounts', 28)),
    D('Counts after an infection `(U - 1, I + 1)` (natural subtraction).', src('SIRCounts', 29)),
    D('Counts after a recovery `(U, I - 1)` (natural subtraction).', src('SIRCounts', 30)),
    D('''One step of the counts: absorbed if `I = 0`; `true` is an infection (kept if `U = 0`), `false` a
recovery.''', src('SIRCounts', 32, 34)),
] if COUNTS else []), 'end Freezing1.SIR', fake='Freezing1.SIRCounts' if COUNTS else None)

block(['namespace Freezing1.SIR', 'open PlaneTree', 'open scoped Classical'], [
    D('''The tree-level state: the number of still susceptible individuals and the finite plane state of
the infection tree.''', src('SIRTreeState', 21, 24)),
    D('The discrete sigma-algebra on tree states.', src('SIRTreeState', 26, 27)),
] + ([
    D('The initial tree state: `n` susceptibles and the root-only tree.', src('SIRTreeState', 29)),
    D('Infection below the vertex `u`: one susceptible fewer, a new active child of `u`.',
      src('SIRTreeState', 36, 37)),
    D('Recovery of the vertex `u`: freeze it.', src('SIRTreeState', 39, 40)),
    D('''The step of the tree state at the vertex `u` for the sign `true` (infection, unless no one is
susceptible) or `false` (recovery); nothing happens if `u` is not active.''', src('SIRTreeState', 42, 46)),
] if TREE else []), 'end Freezing1.SIR', fake='Freezing1.SIRTreeState')

block(['namespace Freezing1.SIR', 'open PlaneTree', 'open scoped Classical', SET], [
    D('The `n + 1` labelled individuals; individual `0` is the initial infective.',
      src('SIRClockPopulation', 23)),
    D('''A clock slot: `(v, none)` is the recovery clock (infectious period) of `v` and `(v, some w)` is
the contact clock of `v` towards `w`.''', src('SIRClockPopulation', 24)),
    D('''A labelled population state: the susceptible and the infectious individuals, the chronological
address of each individual in the infection tree, and the plane state of the infection tree.''',
      src('SIRClockPopulation', 26, 31)),
    D('Forget the labels: the number of susceptibles and the plane state of the tree.',
      src('SIRClockPopulation', 39, 40)),
    D('Individual `0` is infectious at the root, all others are susceptible.',
      src('SIRClockPopulation', 51, 52)),
    D('''Possible contact targets: `none` (the recovery slot) or a susceptible individual.''',
      src('SIRClockPopulation', 116, 117)),
    D('''The live clock slots: infectious sources paired with an available target. Contacts towards
non-susceptible individuals are ignored.''', src('SIRClockPopulation', 119, 120)),
    D('''Infection of the susceptible `w` by `v`: `w` becomes infectious, receives the next child
address of `v`, and the tree gets a new active vertex.''', src('SIRClockPopulationUpdates', 22, 26)),
    D('Recovery of `v`: it leaves the infectious set and its tree vertex is frozen.',
      src('SIRClockPopulationUpdates', 28, 30)),
    D('''The event of a clock slot: if it is live, `(v, none)` recovers `v` and `(v, some w)` infects `w`;
otherwise nothing happens.''', src('SIRClockPopulationUpdates', 160, 166)),
], 'end Freezing1.SIR')

# ---------------------------------------------------------------- Probability, profiles, path space
block(['namespace Freezing1.SIR', 'open Filter', 'open scoped Topology', SET], [
    D('The function `x ↦ x / (1 + x)`.', src('SIRProbability', 24)),
    src('SIRProbability', 26, 27),
    src('SIRProbability', 29, 31),
    D('The infection probability `rate * u / (1 + rate * u)` of the count chain with `u` susceptibles.',
      src('SIRProbability', 62, 64)),
], 'end Freezing1.SIR')

block(['namespace Freezing1.SIR', 'open Filter Set', 'open scoped Topology ContDiff', SET], [
    D('The map `z ↦ z + lam * exp z`.', src('SIRFluidProfile', 31)),
    src('SIRFluidProfile', 33, 37),
    src('SIRFluidProfile', 39, 41),
    src('SIRFluidProfile', 43, 58),
    D('For `lam > 0`, `expLinear lam` as an order isomorphism of `ℝ`.', src('SIRFluidProfile', 60, 61)),
    D('''The susceptible fluid profile `g_λ(t)`: for `λ > 0`, `exp` of the inverse of `z ↦ z + λ exp z` at
`λ (1 - t)`, i.e. the solution of `log g + λ g = λ (1 - t)`, i.e. of `g' = -λ g / (1 + λ g)`, `g(0) = 1`.
(The value `1` for `λ ≤ 0` is a junk default.)''', src('SIRFluidProfile', 66, 67)),
    D('The infectious fluid profile `2 - 2 g_λ(t) - t`.', src('SIRFluidProfile', 184)),
], 'end Freezing1.SIR')

block(['namespace Freezing1.SIR', 'open Filter Set MeasureTheory',
       'open scoped Topology UniformConvergence NNReal ENNReal Classical'], [
    D('The compact time window `[0, m]` of nonnegative reals.', src('SIRPathSpace', 24)),
    D('The family of windows `[0, m]`, `m ∈ ℕ`, exhausting the nonnegative reals.', src('SIRPathSpace', 26)),
    D('''Real functions on nonnegative times with the topology of uniform convergence on every compact
time set (equivalently on every window `[0, m]`), and its Borel sigma-algebra.''', src('SIRPathSpace', 53, 56)),
    D('The scaled path of a word of length `2n + 2`: `t ↦ w k / n` with `k = min ⌊n t⌋ (2n + 1)`.',
      src('SIRPathSpace', 90, 92)),
    D('''The scaled infectious count path `t ↦ I_{⌊n t⌋} / n` of a counts history `H`, stopped at step
`2n + 1` (the epidemic ends by then).''', src('SIRPathSpace', 94, 95)),
    D('The path `t ↦ max (2 - 2 g_λ(t) - t) 0`, the fluid limit on survival.', src('SIRPathSpace', 117, 118)),
    D('The identically zero path.', src('SIRPathSpace', 120)),
], 'end Freezing1.SIR', fake='Freezing1.SIRPathSpace')

block(['namespace Freezing1.SIR', 'open MeasureTheory ProbabilityTheory Set',
       'open scoped NNReal ENNReal Classical'], [
    D('''The path `max (2 - 2 g_λ(t) - t) 0 · 1_A`, where `A` is the event that the tree is infinite
(survival).''', src('SIRGeometricSurvivalPath', 20, 21)),
    D('''The law of that path under the Bienaymé tree with offspring law `G(1 - λ/(1 + λ))`: the limit law
of Theorem `thm:SIR` (I)(a).''', src('SIRGeometricSurvivalPath', 26, 29)),
    D('The scalar `c · 1_A`, `A` the event that the tree is infinite.', src('SIRGeometricSurvivalScalar', 17, 18)),
    '''-- the auxiliary proof of the next definition, named explicitly (it is a copy of
-- `geometricSurvivalPathLaw._proof_1` and would otherwise be shared with it)
theorem geometricSurvivalScalarLaw._proof_1 (lam : ℝ≥0) :
    IsProbabilityMeasure (PlaneTree.geometricBienaymeLaw (infectionProbability lam 1)) := inferInstance''',
    D('''The law of `c · 1_A` under the Bienaymé tree with offspring law `G(1 - λ/(1 + λ))`: the limit law of
Theorem `thm:SIR` (I)(b).''', src('SIRGeometricSurvivalScalar', 24, 27).replace('inferInstance⟩', 'geometricSurvivalScalarLaw._proof_1 lam⟩')),
], 'end Freezing1.SIR')

block(['namespace Freezing1.SIR', 'open Filter MeasureTheory ProbabilityTheory',
       'open scoped Topology ENNReal NNReal Classical', SET], [
    D('''The law of the Bienaymé tree with offspring law `G(1 - p)`, as a probability measure: the limit
law of Theorem `thm:SIRlocallimit` (I) for `p = λ/(1 + λ)`.''', src('MainSIRLocalLimit', 135, 136)),
], 'end Freezing1.SIR')

# ---------------------------------------------------------------- Markov chains (extras)
if COUNTS or TREE:
    block(['namespace Freezing1', 'open MeasureTheory ProbabilityTheory', 'open scoped ENNReal Classical',
           'namespace CountableMarkovChain', src('InterleavedChainKernel', 23)], [
        D('The kernel of the path history `(x₀, ..., xₙ) ↦ α xₙ`.', src('InterleavedChainKernel', 25, 28)),
        src('InterleavedChainKernel', 30, 35),
        D('The Ionescu--Tulcea law of the Markov chain with kernel `α` started at `x`.',
          src('InterleavedChainKernel', 37, 39)),
    ], 'end CountableMarkovChain\n\nend Freezing1')
    if COUNTS:
        block(['namespace Freezing1.SIR', 'open MeasureTheory ProbabilityTheory',
               'open scoped ENNReal NNReal Classical'], [
            D('''The transition kernel of the paper's Markov chain `(U, I)`: infection with probability
`λ_n U / (1 + λ_n U)`, recovery with probability `1 / (1 + λ_n U)`; `I = 0` is absorbing.''',
              src('SIRCountLaw', 23, 26)),
            src('SIRCountLaw', 28, 33),
            D('The law of the whole path of the Markov chain `(U, I)` started from `(n, 1)`.',
              src('SIRCountLaw', 88, 89)),
        ], 'end Freezing1.SIR')
    if TREE:
        block(['namespace Freezing1.SIR', 'open MeasureTheory ProbabilityTheory',
               'open scoped ENNReal NNReal Classical'], [
            D('''The kernel of one step of the infection tree: apply the sign to a uniformly chosen active
vertex.''', src('SIRTreeLaw', 24, 27)),
            src('SIRTreeLaw', 29, 36),
            D('''The infection-tree chain: the sign is drawn with the infection probability, then applied at a
uniform active vertex (uniform attachment with freezing).''', src('SIRTreeLaw', 66, 69)),
            src('SIRTreeLaw', 71, 75),
            D('The law of the whole history of the infection-tree chain started from `n` susceptibles.',
              src('SIRTreeLaw', 140, 141)),
        ], 'end Freezing1.SIR', fake=None)

# ---------------------------------------------------------------- Poisson contact data
emit('/-! ## Poisson contact paths, the full contact protocol and the physical laws -/')
emit()
block(['namespace Freezing1.SIR.PoissonContact', 'open Filter MeasureTheory ProbabilityTheory Set',
       'open scoped ENNReal NNReal Classical Topology', SET], [
    D('''An entire locally finite simple counting path, given by its arrival times: a strictly increasing
real sequence, positive at `0` and tending to infinity.''', src('SIRPoissonFirstArrival', 24)),
    D('The sigma-algebra on arrival paths induced from the product sigma-algebra of `ℕ → ℝ`.',
      src('SIRPoissonFirstArrival', 26, 27)),
    D('The first arrival of a path.', src('SIRPoissonFirstArrival', 29)),
    src('SIRPoissonFirstArrival', 38, 39),
    src('SIRPoissonFirstArrival', 41, 42),
    src('SIRPoissonFirstArrival', 96, 99),
] + ([
    D('Poisson counting marginals of intensity `r > 0` give an exponential first arrival of parameter `r`.',
      tgt('SIRPoissonFirstArrival', 101, 103)),
] if FIRST else []), 'end Freezing1.SIR.PoissonContact')

block(['namespace Freezing1.SIR', 'open MeasureTheory ProbabilityTheory',
       'open scoped ENNReal NNReal Classical', SET], [
    D('A clock array assigns a real delay to every clock slot.', src('SIRPreassignedClocks', 25)),
    D('''The slot `c` is the strict winner of the race among the live slots: live and strictly smaller than
every other live slot.''', src('SIRPreassignedClocks', 30, 32)),
    D('''The unique live slot with strictly smallest value if there is one; `none` otherwise (the process
then holds).''', src('SIRPreassignedClocks', 40, 42)),
    D('''A clock frame: the population state, the current time and the infection (birth) time of every
individual.''', src('SIRPreassignedClocks', 104)),
    '-- projections of a frame: population, current time, infection (birth) times\n' + src('SIRPreassignedClocks', 106, 108),
    D('The initial frame: initial population at time zero, all birth times zero.',
      src('SIRPreassignedClocks', 110)),
    D('''The remaining value of a slot: its delay (measured from the infection time of its source) minus
the current infection age of the source.''', src('SIRPreassignedClocks', 115, 116)),
    '''-- the matcher of `match c.2 with | none => _ | some w => _` in the next definition, written out
abbrev advanceClockFrame.match_1.{u_1} {n : ℕ} (motive : Option (Individual n) → Sort u_1)
    (x : Option (Individual n)) (h_1 : Unit → motive none)
    (h_2 : (w : Individual n) → motive (some w)) : motive x :=
  Option.casesOn (motive := fun x => motive x) x (h_1 ()) fun val => h_2 val''',
    D('''Advance the frame to the firing of the slot `c`: time moves by the remaining value of `c`, the
population undergoes the event, and a newly infected individual gets the new time as birth time.''',
      src('SIRPreassignedClocks', 127, 133).replace('''  let births := match c.2 with
    | none => F.birthTime
    | some w => Function.update F.birthTime w time''', '''  let births := advanceClockFrame.match_1 (fun _ => Individual n → ℝ) c.2 (fun _ => F.birthTime)
    (fun w => Function.update F.birthTime w time)''')),
    D('''One step of the frame: the strictly earliest live slot fires; if there is none the frame is
unchanged.''', src('SIRPreassignedClocks', 135, 139)),
], 'end Freezing1.SIR')

block(['namespace Freezing1.SIR', 'open MeasureTheory ProbabilityTheory',
       'open scoped ENNReal NNReal Classical', SET], [
    D('''The random datum of a slot: a real number for a recovery slot `(v, none)` (the infectious period
of `v`) and an entire arrival path for a contact slot `(v, some w)`.''', GM + src('SIRPoissonClockArray', 24, 27)),
    src('SIRPoissonClockArray', 29, 31),
    D('A complete family of clock data for all directed pairs.', src('SIRPoissonClockArray', 44)),
], 'end Freezing1.SIR')

block(['namespace Freezing1.SIR', 'open MeasureTheory Set', 'open scoped Classical', SET], [
    D('''The first arrival of the path `a` strictly after `t`, i.e. the point whose index is the number of
arrivals at or before `t`.''', src('SIRPoissonFullContacts', 24, 25)),
    D('''The delays used in the frame `F`: the infectious period for a recovery slot, and for a contact slot
`(v, some w)` the next arrival of its path after the current infection age `F.time - F.birthTime v` of `v`.''',
      src('SIRPoissonFullContacts', 35, 39)),
    src('SIRPoissonFullContacts', 95, 98),
    D('The full contact protocol run for `k` steps from the initial frame.', src('SIRPoissonFullContacts', 100, 102)),
], 'end Freezing1.SIR')

block(['namespace Freezing1.SIR', 'open MeasureTheory ProbabilityTheory',
       'open scoped ENNReal NNReal Classical', SET], [
    D('The tree state (susceptible count and infection tree) after `k` steps of the full protocol.',
      src('SIRPoissonFullContactLaw', 25, 26)),
], 'end Freezing1.SIR')

# ---------------------------------------------------------------- physical laws
block(['namespace Freezing1.SIR', 'open Filter MeasureTheory ProbabilityTheory',
       'open scoped ENNReal NNReal Classical Topology', SET], [
    D('''The source's independent recovery periods and directed contact processes, indexed by the infection
age: the data `X c`, `c : ClockSlot n`, are measurable and mutually independent under `mu`; each recovery
period `X (v, none)` is exponential of parameter one; each contact path `X (v, some w)` has, for every
`t ≥ 0`, a Poisson law of parameter `rate * t` for its number of points in `[0, t]`. Positivity of the rate
is kept separate.''', src('SIRPhysicalLaws', 28, 35)),
    src('SIRPhysicalLaws', 37),
    D('''The law of the history `k ↦ (susceptible count, infection tree)` of the physical epidemic driven
by `X`.''', src('SIRPhysicalLaws', 39, 42)),
    D('The law of the history of counts `k ↦ (U, I)` of the physical epidemic.',
      src('SIRPhysicalLaws', 44, 48)),
    D('''The law of the full infection tree of the physical epidemic at step `2 n + 1`, when it has
ceased: the plane tree of all individuals ever infected (frozen vertices included).''',
      src('SIRPhysicalLaws', 50, 53)),
    D('''The law of the stopped infectious count path `t ↦ I_{⌊n t⌋} / n` of the physical epidemic, in the
space of paths with uniform convergence on compact time sets.''', src('SIRPhysicalLaws', 55, 57)),
    D('The law of the height of a uniformly sampled vertex of the actual tree after `k` steps (frozen ones included).',
      src('SIRPhysicalLaws', 60, 63)),
    D('''The law of (height of `V₁`, height of `V₂`, graph distance between them) for two vertices that are
conditionally independent given the same actual tree after `k` steps, each uniform among all its vertices;
the diagonal `V₁ = V₂` is part of this law.''', src('SIRPhysicalLaws', 67, 70)),
], 'end Freezing1.SIR')

block(['namespace Freezing1.SIR', 'open Filter MeasureTheory ProbabilityTheory',
       'open scoped ENNReal NNReal Classical Topology', SET, 'section FixedPopulation',
       src('SIRPhysicalFiniteLimits', 26)], [
    src('SIRPhysicalFiniteLimits', 28, 38),
    src('SIRPhysicalFiniteLimits', 40, 43),
    src('SIRPhysicalFiniteLimits', 45, 48),
    D('''The law of the height of a uniform vertex of the full terminal tree (step `2 n + 1`) divided by
`log n`.''', src('SIRPhysicalFiniteLimits', 50, 55)),
    D('''The law of the graph distance between two independent uniform vertices of the full terminal tree
(step `2 n + 1`) divided by `log n`.''', src('SIRPhysicalFiniteLimits', 57, 62)),
    'end FixedPopulation',
], 'end Freezing1.SIR')

# ---------------------------------------------------------------- targets
emit('/-! ## Theorems `thm:SIRlocallimit` and `thm:SIR` for the physical epidemic -/')
emit()
block(['namespace Freezing1.SIR', 'open Filter MeasureTheory ProbabilityTheory',
       'open scoped ENNReal NNReal Classical Topology', SET, 'section Limits',
       src('SIRPhysicalFiniteLimits', 87, 89)], [
    D('''Theorem `thm:SIR` (I)(b), first limit. If `λ_n ∼ λ/n` with `λ > 1` (`λ_n = rate n`, hypothesis
`hratio`), then conditionally on the full infection tree the height of a uniform vertex divided by `ln n`
converges in distribution to `λ/(λ-1) · 1_A`, `A` the survival event of the Bienaymé tree with offspring law
`G(1/(1+λ))`. The source data assumption is needed only for large `n`.''',
      tgt('SIRPhysicalFiniteLimits', 93, 98)),
    D('''Theorem `thm:SIR` (I)(b), second limit. With `V₁`, `V₂` conditionally independent uniform vertices
of the full infection tree (possibly equal), the graph distance divided by `ln n` converges in
distribution to `2λ/(λ-1) · 1_A`.''', tgt('SIRPhysicalFiniteLimits', 108, 113)),
    'end Limits',
], 'end Freezing1.SIR')

block(['namespace Freezing1.SIR', 'open Filter MeasureTheory ProbabilityTheory',
       'open scoped ENNReal NNReal Classical Topology', SET, src('SIRPhysicalLimits', 29, 31)], [
    D('''Theorem `thm:SIRlocallimit` (I). If `λ_n ∼ λ/n` for some `λ > 0` (`λ_n = rate n`, hypothesis
`hratio`), the full infection tree `T^n` converges in distribution for the local topology to the Bienaymé
tree with offspring law `G(1/(1+λ))`. The source data assumption is needed only for large `n`.''',
      tgt('SIRPhysicalLimits', 35, 40)),
    D('''Theorem `thm:SIRlocallimit` (II). If `λ_n ≫ 1/n` (the ratio `rate n / (1/n)` tends to infinity),
the laws of the full infection tree are not tight for the local topology.''',
      tgt('SIRPhysicalLimits', 63, 67)),
    D('''Theorem `thm:SIR` (I)(a). If `λ_n ∼ λ/n` with `λ > 1`, the infectious count path
`(I_{⌊nt⌋}/n)_{t ≥ 0}` converges in distribution, uniformly on compact sets, to
`max(2 - 2 g_λ(t) - t, 0) · 1_A`, `A` the survival event of the Bienaymé tree with offspring law
`G(1/(1+λ))`.''', tgt('SIRPhysicalLimits', 73, 78)),
    D('''Theorem `thm:SIR` (II)(a). If `λ_n ≫ 1/n`, `sup_{0 ≤ t ≤ 2} |I_{⌊nt⌋}/n - min(t, 2-t)|` tends to
zero in probability: the probability that it is at least `eps` tends to zero, for every `eps > 0`.''',
      tgt('SIRPhysicalLimits', 88, 94)),
    D('''Theorem `thm:SIR` (II)(b), height. If `λ_n ≫ 1/n`, the height of a uniform vertex of the full
infection tree divided by `ln n` converges in probability to `1`.''', tgt('SIRPhysicalLimits', 103, 108)),
    D('''Theorem `thm:SIR` (II)(b), distance. If `λ_n ≫ 1/n`, the distance between two independent uniform
vertices of the full infection tree (possibly equal) divided by `ln n` converges in probability to `2`.''',
      tgt('SIRPhysicalLimits', 117, 122)),
    D('''Theorem `thm:SIR` (II)(b), maximum. If `λ_n ≫ 1/n`, the height of the full infection tree (maximal
address length of its vertices at step `2 n + 1`) divided by `ln n` converges in probability to `e`.''',
      tgt('SIRPhysicalLimits', 131, 137)),
], 'end Freezing1.SIR')

# ---------------------------------------------------------------- extras: meaning of the hypothesis
if COUNTS or TREE:
    emit('/-! ## Sanity statements on the meaning of `PoissonSIRData` -/')
    emit()
    tl = []
    if TREE:
        tl += [D('''Under `PoissonSIRData` and a positive rate, the physical history of the infection tree is the
uniform attachment with freezing of the paper, with the infection probabilities of its Markov chain.''',
                 tgt('SIRPhysicalLaws', 75, 76))]
    if COUNTS:
        tl += [D('''Under `PoissonSIRData` and a positive rate, the physical history of counts `(U, I)` is the
paper's Markov chain started at `(n, 1)`.''', tgt('SIRPhysicalLaws', 80, 81))]
    block(['namespace Freezing1.SIR', 'open Filter MeasureTheory ProbabilityTheory',
           'open scoped ENNReal NNReal Classical Topology', SET, src('SIRPhysicalLaws', 37),
           src('SIRPhysicalLaws', 72, 73)], tl, 'end Freezing1.SIR')

emit('-- restore the name of this module (see the `setMainModule` remark in the header)')
emit('run_cmd Lean.modifyEnv (·.setMainModule `Challenge.Sir)')
