module

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

The counting history `(U, I)` of the fluid statements is read as (number of susceptibles, number of
active tree vertices = infectious individuals); no target pins this reading. The satisfiability of
`PoissonSIRData` (existence of a probability space carrying independent exponential periods and Poisson
contact processes) is mathematically standard but is not a target of this file unless stated in the
accompanying notes.

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


/-! ## Plane trees -/

namespace Freezing1.PlaneTree
open Filter MeasureTheory Set
open scoped Topology Classical
set_option backward.isDefEq.respectTransparency false
/-- An Ulam--Harris address: the finite list of child indices (each `≥ 1`) leading from the root
of a plane tree to one of its vertices; the root is the empty list. -/
abbrev Address := List ℕ
/-- The discrete sigma-algebra on the countable set of addresses. -/
instance : MeasurableSpace Address := ⊤
instance : DiscreteMeasurableSpace Address := ⟨fun _ => trivial⟩
/-- An offspring field gives a number of children `f u` to every address `u`. -/
abbrev Offspring := Address → ℕ
/-- A canonical offspring field: an address `u ++ [j]` which is not one of the `f u` children
`1 ≤ j ≤ f u` of `u` has offspring count zero. -/
def Canonical (f : Offspring) : Prop :=
  ∀ (u : Address) (j : ℕ), ¬(1 ≤ j ∧ j ≤ f u) → f (u ++ [j]) = 0
/-- Locally finite rooted plane trees, encoded by their canonical offspring fields (number of
children of the vertex at each address; zero at absent addresses). The topology is the subspace
topology of the product topology on `Address → ℕ` (`ℕ` discrete): the topology of local convergence. -/
abbrev Tree := {f : Offspring // Canonical f}
/-- The sigma-algebra on plane trees is the Borel sigma-algebra of the local topology. -/
instance : MeasurableSpace Tree := borel Tree
instance : BorelSpace Tree := ⟨rfl⟩
/-- The degree of a tree: the number of children of its root. -/
def degree (T : Tree) : ℕ := T.val []
/-- The tree reduced to its root. -/
def leaf : Tree := ⟨fun _ => 0, fun _ _ _ => rfl⟩
/-- The subtree rooted at the `j`-th child of the root. -/
def child (T : Tree) (j : ℕ) : Tree :=
  ⟨fun u => T.val (j :: u), by
    intro u k hk
    exact T.property (j :: u) k hk⟩
end Freezing1.PlaneTree

namespace Freezing1.PlaneTree
open MeasureTheory
open scoped Classical
/-- Pruning of an offspring field: the count at `u` is kept if `u` is an existing vertex (each
index along `u` is an existing child index of its parent) and replaced by `0` otherwise. -/
def pruneRaw (f : Offspring) : Address → ℕ
  | [] => f []
  | j :: u => if 1 ≤ j ∧ j ≤ f [] then pruneRaw (fun v => f (j :: v)) u else 0
theorem canonical_pruneRaw (f : Offspring) : Canonical (pruneRaw f) := by
  intro u j
  induction u generalizing f with
  | nil =>
      simp only [List.nil_append, pruneRaw]
      intro hj
      rw [ite_eq_right hj]
  | cons i u ih =>
      by_cases hi : 1 ≤ i ∧ i ≤ f []
      · simpa only [List.cons_append, pruneRaw, ite_eq_left hi] using
          ih (fun v => f (i :: v))
      · simp [List.cons_append, pruneRaw, hi]

/-- The plane tree obtained by pruning an offspring field. -/
def prune (f : Offspring) : Tree := ⟨pruneRaw f, canonical_pruneRaw f⟩
end Freezing1.PlaneTree

namespace Freezing1.PlaneTree
open scoped Classical
set_option bootstrap.genMatcherCode false in
/-- `Present T u`: the address `u` is a vertex of `T`; the empty address is the root, and `j :: u`
is a vertex iff `1 ≤ j ≤ degree T` and `u` is a vertex of the `j`-th subtree. -/
def Present (T : Tree) : Address → Prop
  | [] => True
  | j :: u => 1 ≤ j ∧ j ≤ degree T ∧ Present (child T j) u
end Freezing1.PlaneTree

namespace Freezing1.PlaneTree
open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
/-- The product law over all addresses of independent offspring counts with common law `μ`. -/
noncomputable def offspringFieldLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Measure Offspring := Measure.infinitePi (fun _ : Address => μ)
instance offspringFieldLaw_probability (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (offspringFieldLaw μ) := by
  unfold offspringFieldLaw
  infer_instance
/-- The Bienaymé (Galton--Watson) tree law with offspring law `μ`: the pruning of an iid offspring field. -/
noncomputable def bienaymeLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] : Measure Tree :=
  (offspringFieldLaw μ).map prune
instance bienaymeLaw_probability (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (bienaymeLaw μ) := by
  unfold bienaymeLaw
  infer_instance
/-- The Bienaymé tree law with geometric offspring law `G(1 - p)`, `μ(k) = (1 - p) p ^ k`
(Mathlib's `geometricMeasure` with success probability `1 - p`). -/
noncomputable def geometricBienaymeLaw (p : unitInterval) : Measure Tree :=
  bienaymeLaw (geometricMeasure (unitInterval.symm p))
instance geometricBienaymeLaw_probability (p : unitInterval) :
    IsProbabilityMeasure (geometricBienaymeLaw p) := by
  unfold geometricBienaymeLaw
  infer_instance
end Freezing1.PlaneTree

namespace Freezing1.PlaneTree
open MeasureTheory Filter
open scoped Classical
/-- The tree has finitely many vertices (the set of present addresses is finite). -/
def FiniteVertices (T : Tree) : Prop := {u : Address | Present T u}.Finite
end Freezing1.PlaneTree

/-! ## Finite plane states and uniform sampling of their vertices -/

run_cmd Lean.modifyEnv (·.setMainModule `Freezing1.PlaneFiniteState)
namespace Freezing1.PlaneForward
open PlaneTree
open scoped Classical
/-- A raw finite state of the growing tree: the finite set of addresses created so far and its
subset of active (not yet frozen) addresses. -/
structure State where
  vertices : Finset Address
  active : Finset Address
  deriving DecidableEq, Countable
/-- The discrete sigma-algebra on finite states. -/
instance : MeasurableSpace State := ⊤
instance : MeasurableSingletonClass State := ⟨fun _ => trivial⟩
/-- The state consisting of the root only, which is active. -/
def initial : State := ⟨{[]}, {[]}⟩
/-- The vertices of `s` that are direct children of `u`. -/
noncomputable def children (s : State) (u : Address) : Finset Address :=
  s.vertices.filter fun w => ∃ j : ℕ, w = u ++ [j]
/-- The number of children of `u` among the vertices of `s`. -/
noncomputable def childCount (s : State) (u : Address) : ℕ := (children s u).card
/-- The address `u ++ [childCount s u + 1]` of the next child of `u`. -/
noncomputable def newChild (s : State) (u : Address) : Address :=
  u ++ [childCount s u + 1]
/-- Attach a new active child to `u`. -/
noncomputable def attach (s : State) (u : Address) : State :=
  ⟨insert (newChild s u) s.vertices, insert (newChild s u) s.active⟩
/-- Freeze `u`: remove it from the active set, keeping the vertices. -/
def freeze (s : State) (u : Address) : State := ⟨s.vertices, s.active.erase u⟩
/-- Ulam--Harris validity of a finite state: the root is a vertex, active vertices are vertices,
the vertex set is prefix closed, and the children of `u` are exactly `u ++ [j]`, `1 ≤ j ≤ childCount s u`. -/
structure Valid (s : State) : Prop where
  root_mem : [] ∈ s.vertices
  active_subset : s.active ⊆ s.vertices
  prefix_closed : ∀ u v : Address, u ++ v ∈ s.vertices → u ∈ s.vertices
  children_iff : ∀ u ∈ s.vertices, ∀ j : ℕ,
    u ++ [j] ∈ s.vertices ↔ 1 ≤ j ∧ j ≤ childCount s u
theorem Valid.children_eq_empty_of_not_mem {s : State} (hs : Valid s)
    {u : Address} (hu : u ∉ s.vertices) : children s u = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hw, j, rfl⟩ := Finset.mem_filter.mp hw
  exact hu (hs.prefix_closed u [j] hw)
theorem Valid.childCount_zero_of_not_mem {s : State} (hs : Valid s)
    {u : Address} (hu : u ∉ s.vertices) : childCount s u = 0 := by
  rw [childCount, hs.children_eq_empty_of_not_mem hu, Finset.card_empty]
theorem Valid.childCount_canonical {s : State} (hs : Valid s) : Canonical (childCount s) := by
  intro u j hj
  apply hs.childCount_zero_of_not_mem
  intro hmem
  have hu := hs.prefix_closed u [j] hmem
  exact hj ((hs.children_iff u hu j).mp hmem)
/-- The plane tree whose offspring counts are the child counts of a valid state (the leaf for an invalid state). -/
noncomputable def shape (s : State) : Tree :=
  if hs : Valid s then ⟨childCount s, hs.childCount_canonical⟩ else leaf
end Freezing1.PlaneForward

run_cmd Lean.modifyEnv (·.setMainModule `Freezing1.FiniteUniformPairs)
namespace Freezing1.FiniteUniform
open MeasureTheory
open scoped ENNReal Classical
theorem uniformOfFinset_probability {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {A : Finset α} (hA : A.Nonempty) :
    IsProbabilityMeasure (Measure.uniformOfFinset A) := by
  constructor
  rw [Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true]
  exact ENNReal.div_self (by exact_mod_cast hA.card_pos.ne') (by simp)
end Freezing1.FiniteUniform

run_cmd Lean.modifyEnv (·.setMainModule `Freezing1.PlaneFiniteGraph)
namespace Freezing1.PlaneForward
open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
/-- The parent--child graph on addresses: two vertices of `s` are adjacent when one is the other extended by one index. -/
def parentGraph (s : State) : SimpleGraph PlaneTree.Address where
  Adj u v := u ∈ s.vertices ∧ v ∈ s.vertices ∧
    ((∃ j : ℕ, v = u ++ [j]) ∨ (∃ j : ℕ, u = v ++ [j]))
  symm := ⟨by
    intro u v h
    exact ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨by
    intro u h
    rcases h.2.2 with ⟨j, he⟩ | ⟨j, he⟩ <;>
      have hh := congrArg List.length he <;>
      simp only [List.length_append, List.length_singleton] at hh <;> omega⟩

/-- The pair kernel of a finite state. For a nonempty vertex set take two independent uniform vertices
`u`, `v` (the diagonal `u = v` is allowed) and return `(|u|, |v|, dist u v)`, the two heights and the graph
distance in the parent graph; for an empty vertex set return `(0, 0, 0)`. -/
noncomputable def pairDataKernel : Kernel State (ℕ × ℕ × ℕ) where
  toFun s := if s.vertices.Nonempty then
    (Measure.uniformOfFinset s.vertices).bind fun u =>
      (Measure.uniformOfFinset s.vertices).map fun v =>
        (u.length, v.length, (parentGraph s).dist u v)
    else Measure.dirac (0, 0, 0)
  measurable' := measurable_of_countable _
instance pairDataKernel_markov : IsMarkovKernel pairDataKernel := by
  constructor
  intro s
  change IsProbabilityMeasure (if s.vertices.Nonempty then _ else _)
  split_ifs with hs
  · haveI := FiniteUniform.uniformOfFinset_probability hs
    exact isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
      (Filter.Eventually.of_forall fun _ => by infer_instance)
  · infer_instance
end Freezing1.PlaneForward

run_cmd Lean.modifyEnv (·.setMainModule `Freezing1.ForwardPlaneKernel)
namespace Freezing1.PlaneForward
open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
set_option backward.isDefEq.respectTransparency false
theorem uniform_active_probability (s : State) (h : s.active.Nonempty) :
    IsProbabilityMeasure (Measure.uniformOfFinset s.active) := by
  constructor
  rw [Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true]
  exact ENNReal.div_self (by exact_mod_cast h.card_pos.ne') (by simp)
end Freezing1.PlaneForward

namespace Freezing1.InterleavedChain
open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]
/-- Finite words over a countable state space carry the discrete sigma-algebra. -/
instance wordMeasurableSpace (E : Type*) [Countable E] : MeasurableSpace (List E) := ⊤
instance wordMeasurableSingletonClass (E : Type*) [Countable E] :
    MeasurableSingletonClass (List E) := ⟨fun _ => trivial⟩
end Freezing1.InterleavedChain

run_cmd Lean.modifyEnv (·.setMainModule `Freezing1.MainSIRUniformHeightStrong)
namespace Freezing1.PlaneForward
open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
/-- The vertex-height kernel of a finite state: the law of the height (address length) of a uniformly
chosen vertex among all vertices, frozen ones included; `δ₀` for an empty vertex set. -/
noncomputable def vertexHeightKernel : Kernel State ℕ where
  toFun s := if s.vertices.Nonempty then (Measure.uniformOfFinset s.vertices).map List.length
    else Measure.dirac 0
  measurable' := measurable_of_countable _
instance vertexHeightKernel_markov : IsMarkovKernel vertexHeightKernel := by
  constructor
  intro s
  change IsProbabilityMeasure (if s.vertices.Nonempty then _ else _)
  split_ifs with hs
  · have hp : IsProbabilityMeasure (Measure.uniformOfFinset s.vertices) := by
      constructor
      rw [Measure.uniformOfFinset_apply]
      simp only [Set.mem_univ, Finset.filter_true]
      exact ENNReal.div_self (by exact_mod_cast hs.card_pos.ne') (by simp)
    have := hp
    exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable
      |>.mpr inferInstance
  · infer_instance
end Freezing1.PlaneForward

/-! ## Counts, labelled population, infection probabilities, fluid profile and path space -/

namespace Freezing1.SIR
/-- The numbers `(U, I)` of susceptible and infectious individuals. -/
structure Counts where
  susceptible : ℕ
  infectious : ℕ
  deriving DecidableEq, Countable
/-- The discrete sigma-algebra on counts. -/
instance : MeasurableSpace Counts := ⊤
instance : DiscreteMeasurableSpace Counts := ⟨fun _ => trivial⟩
end Freezing1.SIR

run_cmd Lean.modifyEnv (·.setMainModule `Freezing1.SIRTreeState)
namespace Freezing1.SIR
open PlaneTree
open scoped Classical
/-- The tree-level state: the number of still susceptible individuals and the finite plane state of the infection tree. -/
structure TreeState where
  susceptible : ℕ
  tree : PlaneForward.State
  deriving DecidableEq, Countable
/-- The discrete sigma-algebra on tree states. -/
instance : MeasurableSpace TreeState := ⊤
instance : DiscreteMeasurableSpace TreeState := ⟨fun _ => trivial⟩
/-- The initial tree state: `n` susceptibles and the root-only tree. -/
def initialTreeState (n : ℕ) : TreeState := ⟨n, PlaneForward.initial⟩
/-- Infection below the vertex `u`: one susceptible fewer, a new active child of `u`. -/
noncomputable def infectTreeState (z : TreeState) (u : Address) : TreeState :=
  ⟨z.susceptible - 1, PlaneForward.attach z.tree u⟩
/-- Recovery of the vertex `u`: freeze it. -/
def recoverTreeState (z : TreeState) (u : Address) : TreeState :=
  ⟨z.susceptible, PlaneForward.freeze z.tree u⟩
/-- The step of the tree state at the vertex `u` for the sign `true` (infection, unless no one is
susceptible) or `false` (recovery); nothing happens if `u` is not active. -/
noncomputable def treeStep (z : TreeState) (sign : Bool) (u : Address) : TreeState :=
  if u ∈ z.tree.active then
    if sign then if z.susceptible = 0 then z else infectTreeState z u
    else recoverTreeState z u
  else z
end Freezing1.SIR

namespace Freezing1.SIR
open PlaneTree
open scoped Classical
set_option backward.isDefEq.respectTransparency false
/-- The `n + 1` labelled individuals; individual `0` is the initial infective. -/
abbrev Individual (n : ℕ) := Fin (n + 1)
/-- A clock slot: `(v, none)` is the recovery clock (infectious period) of `v` and `(v, some w)` is
the contact clock of `v` towards `w`. -/
abbrev ClockSlot (n : ℕ) := Individual n × Option (Individual n)
/-- A labelled population state: the susceptible and the infectious individuals, the chronological
address of each individual in the infection tree, and the plane state of the infection tree. -/
structure PopulationState (n : ℕ) where
  susceptible : Finset (Individual n)
  active : Finset (Individual n)
  address : Individual n → Address
  tree : PlaneForward.State
  deriving DecidableEq, Countable
/-- Forget the labels: the number of susceptibles and the plane state of the tree. -/
def PopulationState.project {n : ℕ} (z : PopulationState n) : TreeState :=
  ⟨z.susceptible.card, z.tree⟩
/-- Individual `0` is infectious at the root, all others are susceptible. -/
def initialPopulation (n : ℕ) : PopulationState n :=
  ⟨Finset.univ.erase 0, {0}, fun _ => [], PlaneForward.initial⟩
/-- Possible contact targets: `none` (the recovery slot) or a susceptible individual. -/
noncomputable def PopulationState.availableTargets {n : ℕ} (z : PopulationState n) :
    Finset (Option (Individual n)) := insert none (z.susceptible.image some)
/-- The live clock slots: infectious sources paired with an available target. Contacts towards
non-susceptible individuals are ignored. -/
noncomputable def PopulationState.liveSlots {n : ℕ} (z : PopulationState n) :
    Finset (ClockSlot n) := z.active ×ˢ z.availableTargets
/-- Infection of the susceptible `w` by `v`: `w` becomes infectious, receives the next child
address of `v`, and the tree gets a new active vertex. -/
noncomputable def infectPopulation {n : ℕ} (z : PopulationState n)
    (v w : Individual n) : PopulationState n :=
  ⟨z.susceptible.erase w, insert w z.active,
    Function.update z.address w (PlaneForward.newChild z.tree (z.address v)),
    PlaneForward.attach z.tree (z.address v)⟩
/-- Recovery of `v`: it leaves the infectious set and its tree vertex is frozen. -/
def recoverPopulation {n : ℕ} (z : PopulationState n) (v : Individual n) : PopulationState n :=
  ⟨z.susceptible, z.active.erase v, z.address,
    PlaneForward.freeze z.tree (z.address v)⟩
/-- The event of a clock slot: if it is live, `(v, none)` recovers `v` and `(v, some w)` infects `w`;
otherwise nothing happens. -/
noncomputable def populationStep {n : ℕ} (z : PopulationState n)
    (c : ClockSlot n) : PopulationState n :=
  if c ∈ z.liveSlots then
    match c.2 with
    | none => recoverPopulation z c.1
    | some w => infectPopulation z c.1 w
  else z
end Freezing1.SIR

namespace Freezing1.SIR
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
/-- The function `x ↦ x / (1 + x)`. -/
noncomputable def infectionFraction (x : ℝ) : ℝ := x / (1 + x)
theorem infectionFraction_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ infectionFraction x := by
  exact div_nonneg hx (by linarith)
theorem infectionFraction_le_one {x : ℝ} (hx : 0 ≤ x) : infectionFraction x ≤ 1 := by
  apply (div_le_one₀ (by linarith : 0 < 1 + x)).mpr
  linarith
/-- The infection probability `rate * u / (1 + rate * u)` of the count chain with `u` susceptibles. -/
noncomputable def infectionProbability (rate : NNReal) (u : ℕ) : unitInterval :=
  ⟨infectionFraction ((rate : ℝ) * u),
    infectionFraction_nonneg (by positivity), infectionFraction_le_one (by positivity)⟩
end Freezing1.SIR

namespace Freezing1.SIR
open Filter Set
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
/-- The map `z ↦ z + lam * exp z`. -/
noncomputable def expLinear (lam z : ℝ) : ℝ := z + lam * Real.exp z
theorem expLinear_strictMono {lam : ℝ} (hlam : 0 < lam) : StrictMono (expLinear lam) := by
  intro x y hxy
  have he := (Real.exp_lt_exp.mpr hxy)
  dsimp [expLinear]
  exact add_lt_add hxy (mul_lt_mul_of_pos_left he hlam)
theorem expLinear_continuous (lam : ℝ) : Continuous (expLinear lam) := by
  unfold expLinear
  fun_prop
theorem expLinear_surjective {lam : ℝ} (hlam : 0 < lam) : Function.Surjective (expLinear lam) := by
  intro y
  let a := y - lam * Real.exp y
  have hmul : 0 ≤ lam * Real.exp y := mul_nonneg hlam.le (Real.exp_pos y).le
  have hab : a ≤ y := by dsimp [a]; linarith
  have hlow : expLinear lam a ≤ y := by
    have he := Real.exp_le_exp.mpr hab
    have hm := mul_le_mul_of_nonneg_left he hlam.le
    dsimp [a, expLinear] at *
    linarith
  have hhigh : y ≤ expLinear lam y := by
    dsimp [expLinear]
    linarith
  obtain ⟨z, _, hz⟩ := intermediate_value_Icc hab (expLinear_continuous lam).continuousOn
    ⟨hlow, hhigh⟩
  exact ⟨z, hz⟩

/-- For `lam > 0`, `expLinear lam` as an order isomorphism of `ℝ`. -/
noncomputable def expLinearIso (lam : ℝ) (hlam : 0 < lam) : ℝ ≃o ℝ :=
  (expLinear_strictMono hlam).orderIsoOfSurjective _ (expLinear_surjective hlam)
/-- The susceptible fluid profile `g_λ(t)`: for `λ > 0`, `exp` of the inverse of `z ↦ z + λ exp z` at
`λ (1 - t)`, i.e. the solution of `log g + λ g = λ (1 - t)`, i.e. of `g' = -λ g / (1 + λ g)`, `g(0) = 1`.
(The value `1` for `λ ≤ 0` is a junk default.) -/
noncomputable def fluidProfile (lam t : ℝ) : ℝ :=
  if hlam : 0 < lam then Real.exp ((expLinearIso lam hlam).symm (lam * (1 - t))) else 1
/-- The infectious fluid profile `2 - 2 g_λ(t) - t`. -/
noncomputable def infectiousProfile (lam t : ℝ) : ℝ := 2 - 2 * fluidProfile lam t - t
end Freezing1.SIR

run_cmd Lean.modifyEnv (·.setMainModule `Freezing1.SIRPathSpace)
namespace Freezing1.SIR
open Filter Set MeasureTheory
open scoped Topology UniformConvergence NNReal ENNReal Classical
/-- The compact time window `[0, m]` of nonnegative reals. -/
def timeWindow (m : ℕ) : Set ℝ≥0 := Icc 0 m
/-- The family of windows `[0, m]`, `m ∈ ℕ`, exhausting the nonnegative reals. -/
def timeWindows : Set (Set ℝ≥0) := Set.range timeWindow
/-- Real functions on nonnegative times with the topology of uniform convergence on every compact
time set (equivalently on every window `[0, m]`), and its Borel sigma-algebra. -/
abbrev PopulationPath := ℝ≥0 →ᵤ[timeWindows] ℝ

instance : MeasurableSpace PopulationPath := borel PopulationPath
instance : BorelSpace PopulationPath := ⟨rfl⟩
/-- The scaled path of a word of length `2n + 2`: `t ↦ w k / n` with `k = min ⌊n t⌋ (2n + 1)`. -/
noncomputable def populationPathOfWord (n : ℕ) (w : Fin (2 * n + 2) → ℕ) : PopulationPath :=
  UniformOnFun.ofFun timeWindows fun t =>
    (w ⟨min ⌊(n : ℝ) * (t : ℝ)⌋₊ (2 * n + 1), by omega⟩ : ℝ) / n
/-- The scaled infectious count path `t ↦ I_{⌊n t⌋} / n` of a counts history `H`, stopped at step
`2n + 1` (the epidemic ends by then). -/
noncomputable def scaledPopulationPath (n : ℕ) (H : ℕ → Counts) : PopulationPath :=
  populationPathOfWord n (fun i => (H i).infectious)
/-- The path `t ↦ max (2 - 2 g_λ(t) - t) 0`, the fluid limit on survival. -/
noncomputable def positiveProfilePath (lam : ℝ) : PopulationPath :=
  UniformOnFun.ofFun timeWindows fun t => max (infectiousProfile lam t) 0
/-- The identically zero path. -/
noncomputable def zeroPopulationPath : PopulationPath := UniformOnFun.ofFun timeWindows fun _ => 0
end Freezing1.SIR

namespace Freezing1.SIR
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Classical
/-- The path `max (2 - 2 g_λ(t) - t) 0 · 1_A`, where `A` is the event that the tree is infinite (survival). -/
noncomputable def geometricSurvivalPath (lam : ℝ≥0) (T : PlaneTree.Tree) : PopulationPath :=
  if ¬PlaneTree.FiniteVertices T then positiveProfilePath lam else zeroPopulationPath
/-- The law of that path under the Bienaymé tree with offspring law `G(1 - λ/(1 + λ))`: the limit law
of Theorem `thm:SIR` (I)(a). -/
noncomputable def geometricSurvivalPathLaw (lam : ℝ≥0) : ProbabilityMeasure PopulationPath :=
  ProbabilityMeasure.map
    (⟨PlaneTree.geometricBienaymeLaw (infectionProbability lam 1), inferInstance⟩ :
      ProbabilityMeasure PlaneTree.Tree) (geometricSurvivalPath lam)
/-- The scalar `c · 1_A`, `A` the event that the tree is infinite. -/
noncomputable def geometricSurvivalScalar (_lam : ℝ≥0) (c : ℝ) (T : PlaneTree.Tree) : ℝ :=
  if ¬PlaneTree.FiniteVertices T then c else 0
-- the auxiliary proof of the next definition, named explicitly (it is a copy of
-- `geometricSurvivalPathLaw._proof_1` and would otherwise be shared with it)
theorem geometricSurvivalScalarLaw._proof_1 (lam : ℝ≥0) :
    IsProbabilityMeasure (PlaneTree.geometricBienaymeLaw (infectionProbability lam 1)) := inferInstance
/-- The law of `c · 1_A` under the Bienaymé tree with offspring law `G(1 - λ/(1 + λ))`: the limit law of
Theorem `thm:SIR` (I)(b). -/
noncomputable def geometricSurvivalScalarLaw (lam : ℝ≥0) (c : ℝ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    (⟨PlaneTree.geometricBienaymeLaw (infectionProbability lam 1), geometricSurvivalScalarLaw._proof_1 lam⟩ :
      ProbabilityMeasure PlaneTree.Tree) (geometricSurvivalScalar lam c)
end Freezing1.SIR

namespace Freezing1.SIR
open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal Classical
set_option backward.isDefEq.respectTransparency false
/-- The law of the Bienaymé tree with offspring law `G(1 - p)`, as a probability measure: the limit
law of Theorem `thm:SIRlocallimit` (I) for `p = λ/(1 + λ)`. -/
noncomputable def geometricProbabilityLaw (p : unitInterval) : ProbabilityMeasure PlaneTree.Tree :=
  ⟨PlaneTree.geometricBienaymeLaw p, inferInstance⟩
end Freezing1.SIR

namespace Freezing1
open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace CountableMarkovChain
variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]
/-- The kernel of the path history `(x₀, ..., xₙ) ↦ α xₙ`. -/
noncomputable def historyKernel (α : Kernel E E) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → E) E where
  toFun H := α (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
  measurable' := α.measurable.comp (measurable_pi_apply _)
instance historyKernel_markov (α : Kernel E E) [IsMarkovKernel α] (n : ℕ) :
    IsMarkovKernel (historyKernel α n) := by
  constructor
  intro H
  change IsProbabilityMeasure (α (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
  infer_instance
/-- The Ionescu--Tulcea law of the Markov chain with kernel `α` started at `x`. -/
noncomputable def fullLaw (α : Kernel E E) [IsMarkovKernel α] (x : E) :
    Measure (ℕ → E) :=
  Kernel.traj (X := fun _ => E) (historyKernel α) 0 (fun _ => x)
end CountableMarkovChain

end Freezing1

namespace Freezing1.SIR
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
/-- The kernel of one step of the infection tree: apply the sign to a uniformly chosen active vertex. -/
noncomputable def signedTreeLaw (z : TreeState) (sign : Bool) : Measure TreeState :=
  if z.tree.active.Nonempty then
    (Measure.uniformOfFinset z.tree.active).map (treeStep z sign)
  else Measure.dirac z
instance signedTreeLaw_probability (z : TreeState) (sign : Bool) :
    IsProbabilityMeasure (signedTreeLaw z sign) := by
  unfold signedTreeLaw
  split_ifs with h
  · have := PlaneForward.uniform_active_probability z.tree h
    exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable
      |>.mpr inferInstance
  · infer_instance
/-- The infection-tree chain: the sign is drawn with the infection probability, then applied at a
uniform active vertex (uniform attachment with freezing). -/
noncomputable def treeKernel (rate : ℝ≥0) : Kernel TreeState TreeState where
  toFun z := (bernoulliMeasure true false (infectionProbability rate z.susceptible)).bind
    (signedTreeLaw z)
  measurable' := measurable_of_countable _
instance treeKernel_markov (rate : ℝ≥0) : IsMarkovKernel (treeKernel rate) := by
  constructor
  intro z
  exact isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
    (Filter.Eventually.of_forall fun sign => signedTreeLaw_probability z sign)
/-- The law of the whole history of the infection-tree chain started from `n` susceptibles. -/
noncomputable def treeFullLaw (rate : ℝ≥0) (n : ℕ) : Measure (ℕ → TreeState) :=
  CountableMarkovChain.fullLaw (treeKernel rate) (initialTreeState n)
end Freezing1.SIR

/-! ## Poisson contact paths, the full contact protocol and the physical laws -/

namespace Freezing1.SIR.PoissonContact
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Classical Topology
set_option backward.isDefEq.respectTransparency false
/-- An entire locally finite simple counting path, given by its arrival times: a strictly increasing
real sequence, positive at `0` and tending to infinity. -/
def ArrivalPath := {a : ℕ → ℝ // 0 < a 0 ∧ StrictMono a ∧ Tendsto a atTop atTop}
/-- The sigma-algebra on arrival paths induced from the product sigma-algebra of `ℕ → ℝ`. -/
instance : MeasurableSpace ArrivalPath := inferInstanceAs (MeasurableSpace {a : ℕ → ℝ //
  0 < a 0 ∧ StrictMono a ∧ Tendsto a atTop atTop})
/-- The first arrival of a path. -/
def first (a : ArrivalPath) : ℝ := a.1 0
theorem exists_later (a : ArrivalPath) (t : ℝ) : ∃ k : ℕ, t < a.1 k :=
  (a.2.2.2.eventually_gt_atTop t).exists
/-- The number of arrivals at or before `t`. -/
noncomputable def count (a : ArrivalPath) (t : ℝ) : ℕ := Nat.find (exists_later a t)
/-- The exact marginal specification used from a rate-`r` Poisson process.
No exponential waiting-time law is part of this specification. -/
def HasPoissonCounts (nu : Measure ArrivalPath) (r : ℝ≥0) : Prop :=
  ∀ t : ℝ≥0, nu.map (fun a => count a (t : ℝ)) = poissonMeasure (r * t)
/-- Poisson counting marginals of intensity `r > 0` give an exponential first arrival of parameter `r`. -/
theorem first_law (nu : Measure ArrivalPath) [IsProbabilityMeasure nu]
    (r : ℝ≥0) (hr : 0 < r) (hcounts : HasPoissonCounts nu r) :
    nu.map first = expMeasure (r : ℝ) := by
  sorry
end Freezing1.SIR.PoissonContact

namespace Freezing1.SIR
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
set_option backward.isDefEq.respectTransparency false
/-- A clock array assigns a real delay to every clock slot. -/
abbrev ClockArray (n : ℕ) := ClockSlot n → ℝ
/-- The slot `c` is the strict winner of the race among the live slots: live and strictly smaller than every other live slot. -/
def StrictLiveWinner {n : ℕ} (z : PopulationState n) (t : ClockArray n)
    (c : ClockSlot n) : Prop :=
  c ∈ z.liveSlots ∧ ∀ d ∈ z.liveSlots, d ≠ c → t c < t d
/-- The unique live slot with strictly smallest value if there is one; `none` otherwise (the process then holds). -/
noncomputable def firstLiveClock {n : ℕ} (z : PopulationState n)
    (t : ClockArray n) : Option (ClockSlot n) :=
  if h : ∃ c, StrictLiveWinner z t c then some h.choose else none
/-- A clock frame: the population state, the current time and the infection (birth) time of every individual. -/
abbrev ClockFrame (n : ℕ) := PopulationState n × ℝ × (Individual n → ℝ)
-- projections of a frame: population, current time, infection (birth) times
def ClockFrame.population {n : ℕ} (F : ClockFrame n) : PopulationState n := F.1
def ClockFrame.time {n : ℕ} (F : ClockFrame n) : ℝ := F.2.1
def ClockFrame.birthTime {n : ℕ} (F : ClockFrame n) : Individual n → ℝ := F.2.2
/-- The initial frame: initial population at time zero, all birth times zero. -/
def initialClockFrame (n : ℕ) : ClockFrame n := (initialPopulation n, 0, fun _ => 0)
/-- The remaining value of a slot: its delay (measured from the infection time of its source) minus
the current infection age of the source. -/
def remainingClock {n : ℕ} (F : ClockFrame n) (omega : ClockArray n) (c : ClockSlot n) : ℝ :=
  omega c - (F.time - F.birthTime c.1)
-- the matcher of `match c.2 with | none => _ | some w => _` in the next definition, written out
abbrev advanceClockFrame.match_1.{u_1} {n : ℕ} (motive : Option (Individual n) → Sort u_1)
    (x : Option (Individual n)) (h_1 : Unit → motive none)
    (h_2 : (w : Individual n) → motive (some w)) : motive x :=
  Option.casesOn (motive := fun x => motive x) x (h_1 ()) fun val => h_2 val
/-- Advance the frame to the firing of the slot `c`: time moves by the remaining value of `c`, the
population undergoes the event, and a newly infected individual gets the new time as birth time. -/
noncomputable def advanceClockFrame {n : ℕ} (F : ClockFrame n) (omega : ClockArray n)
    (c : ClockSlot n) : ClockFrame n :=
  let time := F.time + remainingClock F omega c
  let births := advanceClockFrame.match_1 (fun _ => Individual n → ℝ) c.2 (fun _ => F.birthTime)
    (fun w => Function.update F.birthTime w time)
  (populationStep F.population c, time, births)
/-- One step of the frame: the strictly earliest live slot fires; if there is none the frame is unchanged. -/
noncomputable def clockFrameStep {n : ℕ} (F : ClockFrame n) (omega : ClockArray n) :
    ClockFrame n :=
  match firstLiveClock F.population (remainingClock F omega) with
  | none => F
  | some c => advanceClockFrame F omega c
end Freezing1.SIR

namespace Freezing1.SIR
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
set_option backward.isDefEq.respectTransparency false
set_option bootstrap.genMatcherCode false in
/-- The random datum of a slot: a real number for a recovery slot `(v, none)` (the infectious period
of `v`) and an entire arrival path for a contact slot `(v, some w)`. -/
def ClockDatum {n : ℕ} (c : ClockSlot n) : Type :=
  match c.2 with
  | none => ℝ
  | some _ => PoissonContact.ArrivalPath
instance clockDatum_measurableSpace {n : ℕ} (c : ClockSlot n) : MeasurableSpace (ClockDatum c) := by
  rcases c with ⟨v, w⟩
  cases w <;> simp only [ClockDatum] <;> infer_instance
/-- A complete family of clock data for all directed pairs. -/
abbrev PoissonClockData (n : ℕ) := (c : ClockSlot n) → ClockDatum c
end Freezing1.SIR

namespace Freezing1.SIR
open MeasureTheory Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
/-- The first arrival of the path `a` strictly after `t`, i.e. the point whose index is the number of
arrivals at or before `t`. -/
noncomputable def PoissonContact.nextArrival (a : PoissonContact.ArrivalPath) (t : ℝ) : ℝ :=
  a.1 (PoissonContact.count a t)
/-- The delays used in the frame `F`: the infectious period for a recovery slot, and for a contact slot
`(v, some w)` the next arrival of its path after the current infection age `F.time - F.birthTime v` of `v`. -/
noncomputable def nextContactDelayArray {n : ℕ} (F : ClockFrame n) (data : PoissonClockData n) :
    ClockArray n :=
  fun c => match c with
  | (v, none) => data (v, none)
  | (v, some w) => PoissonContact.nextArrival (data (v, some w)) (F.time - F.birthTime v)
/-- A full contact-process step uses the next actual point after the
current infection age in each live contact path. It never resamples a path. -/
noncomputable def poissonFullContactStep {n : ℕ} (F : ClockFrame n) (data : PoissonClockData n) :
    ClockFrame n := clockFrameStep F (nextContactDelayArray F data)
/-- The full contact protocol run for `k` steps from the initial frame. -/
noncomputable def poissonFullContactRun (n : ℕ) (data : PoissonClockData n) : ℕ → ClockFrame n
  | 0 => initialClockFrame n
  | k + 1 => poissonFullContactStep (poissonFullContactRun n data k) data
end Freezing1.SIR

namespace Freezing1.SIR
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
set_option backward.isDefEq.respectTransparency false
/-- The tree state (susceptible count and infection tree) after `k` steps of the full protocol. -/
noncomputable def poissonFullContactTreePath (n : ℕ) (data : PoissonClockData n)
    (k : ℕ) : TreeState := (poissonFullContactRun n data k).population.project
end Freezing1.SIR

namespace Freezing1.SIR
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology
set_option backward.isDefEq.respectTransparency false
/-- The source's independent recovery periods and directed contact processes, indexed by the infection
age: the data `X c`, `c : ClockSlot n`, are measurable and mutually independent under `mu`; each recovery
period `X (v, none)` is exponential of parameter one; each contact path `X (v, some w)` has, for every
`t ≥ 0`, a Poisson law of parameter `rate * t` for its number of points in `[0, t]`. The rate is thereby
forced to be positive (rate `0` contradicts the counting marginals on entire arrival paths). Only the
count marginals are prescribed, which suffices: the protocol reads the first point of each path only. -/
structure PoissonSIRData {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (n : ℕ) (rate : ℝ≥0)
    (X : (c : ClockSlot n) → Ω → ClockDatum c) : Prop where
  measurable : ∀ c, Measurable (X c)
  independent : iIndepFun X mu
  recovery_law : ∀ v : Individual n, mu.map (X (v, none)) = expMeasure 1
  contact_counts : ∀ v w : Individual n,
    PoissonContact.HasPoissonCounts (mu.map (X (v, some w))) rate

variable {Ω : Type*} [MeasurableSpace Ω]
/-- The law of the history `k ↦ (susceptible count, infection tree)` of the physical epidemic driven by `X`. -/
noncomputable def physicalTreePathLaw (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) : ProbabilityMeasure (ℕ → TreeState) :=
  ProbabilityMeasure.map (⟨mu, inferInstance⟩ : ProbabilityMeasure Ω)
    (fun omega => poissonFullContactTreePath n (fun c => X c omega))
/-- The law of the history of counts `k ↦ (U, I)` of the physical epidemic. -/
noncomputable def physicalCountsPathLaw (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) : ProbabilityMeasure (ℕ → Counts) :=
  ProbabilityMeasure.map (⟨mu, inferInstance⟩ : ProbabilityMeasure Ω) (fun omega k =>
    let z := (poissonFullContactRun n (fun c => X c omega) k).population
    (⟨z.susceptible.card, z.active.card⟩ : Counts))
/-- The law of the full infection tree of the physical epidemic at step `2 n + 1`, when it has
ceased: the plane tree of all individuals ever infected (frozen vertices included). -/
noncomputable def physicalTerminalTreeLaw (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) : ProbabilityMeasure PlaneTree.Tree :=
  ProbabilityMeasure.map (⟨mu, inferInstance⟩ : ProbabilityMeasure Ω) (fun omega => PlaneForward.shape
    (poissonFullContactRun n (fun c => X c omega) (2 * n + 1)).population.tree)
/-- The law of the stopped infectious count path `t ↦ I_{⌊n t⌋} / n` of the physical epidemic, in the
space of paths with uniform convergence on compact time sets. -/
noncomputable def physicalPopulationPathLaw (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) : ProbabilityMeasure PopulationPath :=
  ProbabilityMeasure.map (physicalCountsPathLaw mu n X) (scaledPopulationPath n)
/-- The law of the height of a uniformly sampled vertex of the actual tree after `k` steps (frozen ones included). -/
noncomputable def physicalUniformHeightLaw (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) (k : ℕ) : Measure ℕ :=
  ((physicalTreePathLaw mu n X : Measure (ℕ → TreeState)).map
    (fun H => (H k).tree)).bind PlaneForward.vertexHeightKernel
/-- The law of (height of `V₁`, height of `V₂`, graph distance between them) for two vertices that are
conditionally independent given the same actual tree after `k` steps, each uniform among all its vertices;
the diagonal `V₁ = V₂` is part of this law. -/
noncomputable def physicalPairDataLaw (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) (k : ℕ) : Measure (ℕ × ℕ × ℕ) :=
  ((physicalTreePathLaw mu n X : Measure (ℕ → TreeState)).map
    (fun H => (H k).tree)).bind PlaneForward.pairDataKernel
end Freezing1.SIR

namespace Freezing1.SIR
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology
set_option backward.isDefEq.respectTransparency false
section FixedPopulation
variable {Ω : Type*} [MeasurableSpace Ω]
theorem physical_sampleLaw_probability (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) (k : ℕ)
    {α : Type*} [MeasurableSpace α] (K : Kernel PlaneForward.State α) [IsMarkovKernel K] :
    IsProbabilityMeasure (((physicalTreePathLaw mu n X : Measure (ℕ → TreeState)).map
      (fun H => (H k).tree)).bind K) := by
  have hm : Measurable (fun H : ℕ → TreeState => (H k).tree) :=
    (measurable_of_countable TreeState.tree).comp (measurable_pi_apply k)
  have : IsProbabilityMeasure ((physicalTreePathLaw mu n X : Measure (ℕ → TreeState)).map
      (fun H => (H k).tree)) :=
    Measure.isProbabilityMeasure_map_iff hm.aemeasurable |>.mpr inferInstance
  exact isProbabilityMeasure_bind K.aemeasurable (Filter.Eventually.of_forall fun _ => inferInstance)
instance physicalUniformHeightLaw_probability (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) (k : ℕ) :
    IsProbabilityMeasure (physicalUniformHeightLaw mu n X k) :=
  physical_sampleLaw_probability mu n X k PlaneForward.vertexHeightKernel
instance physicalPairDataLaw_probability (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) (k : ℕ) :
    IsProbabilityMeasure (physicalPairDataLaw mu n X k) :=
  physical_sampleLaw_probability mu n X k PlaneForward.pairDataKernel
/-- The law of the height of a uniform vertex of the full terminal tree (step `2 n + 1`) divided by `log n`. -/
noncomputable def physicalTerminalUniformHeightScaledLaw
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    (⟨physicalUniformHeightLaw mu n X (2 * n + 1), inferInstance⟩ : ProbabilityMeasure ℕ)
    (fun h : ℕ => (h : ℝ) / Real.log (n : ℝ))
/-- The law of the graph distance between two independent uniform vertices of the full terminal tree
(step `2 n + 1`) divided by `log n`. -/
noncomputable def physicalTerminalUniformDistanceScaledLaw
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    (⟨physicalPairDataLaw mu n X (2 * n + 1), inferInstance⟩ : ProbabilityMeasure (ℕ × ℕ × ℕ))
    (fun z : ℕ × ℕ × ℕ => (z.2.2 : ℝ) / Real.log (n : ℝ))
end FixedPopulation
end Freezing1.SIR

/-! ## Theorems `thm:SIRlocallimit` and `thm:SIR` for the physical epidemic -/

namespace Freezing1.SIR
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology
set_option backward.isDefEq.respectTransparency false
section Limits
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (mu : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (mu n)]
  (X : (n : ℕ) → (c : ClockSlot n) → Ω n → ClockDatum c)
/-- Theorem `thm:SIR` (I)(b), first limit. If `λ_n ∼ λ/n` with `λ > 1` (`λ_n = rate n`, hypothesis
`hratio`), then conditionally on the full infection tree the height of a uniform vertex divided by `ln n`
converges in distribution to `λ/(λ-1) · 1_A`, `A` the survival event of the Bienaymé tree with offspring law
`G(1/(1+λ))`. The source data assumption is needed only for large `n`. -/
theorem physical_sir_uniform_height_limit_of_source_ratio (rate : ℕ → ℝ≥0)
    (lam : ℝ≥0) (hlam : 1 < (lam : ℝ))
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1))
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n)) :
    Tendsto (fun n => physicalTerminalUniformHeightScaledLaw (mu n) n (X n)) atTop
      (𝓝 (geometricSurvivalScalarLaw lam ((lam : ℝ) / ((lam : ℝ) - 1)))) := by
  sorry
/-- Theorem `thm:SIR` (I)(b), second limit. With `V₁`, `V₂` conditionally independent uniform vertices
of the full infection tree (possibly equal), the graph distance divided by `ln n` converges in
distribution to `2λ/(λ-1) · 1_A`. -/
theorem physical_sir_uniform_distance_limit_of_source_ratio (rate : ℕ → ℝ≥0)
    (lam : ℝ≥0) (hlam : 1 < (lam : ℝ))
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1))
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n)) :
    Tendsto (fun n => physicalTerminalUniformDistanceScaledLaw (mu n) n (X n)) atTop
      (𝓝 (geometricSurvivalScalarLaw lam (2 * (lam : ℝ) / ((lam : ℝ) - 1)))) := by
  sorry
end Limits
end Freezing1.SIR

namespace Freezing1.SIR
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology
set_option backward.isDefEq.respectTransparency false
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (mu : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (mu n)]
  (X : (n : ℕ) → (c : ClockSlot n) → Ω n → ClockDatum c)
/-- Theorem `thm:SIRlocallimit` (I). If `λ_n ∼ λ/n` for some `λ > 0` (`λ_n = rate n`, hypothesis
`hratio`), the full infection tree `T^n` converges in distribution for the local topology to the Bienaymé
tree with offspring law `G(1/(1+λ))`. The source data assumption is needed only for large `n`. -/
theorem physical_sir_geometric_local_limit_of_source_ratio (rate : ℕ → ℝ≥0)
    (lam : ℝ≥0) (hlam : 0 < lam)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1))
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n)) :
    Tendsto (fun n => physicalTerminalTreeLaw (mu n) n (X n)) atTop
      (𝓝 (geometricProbabilityLaw (infectionProbability lam 1))) := by
  sorry
/-- Theorem `thm:SIRlocallimit` (II). If `λ_n ≫ 1/n` (the ratio `rate n / (1/n)` tends to infinity),
the laws of the full infection tree are not tight for the local topology. -/
theorem physical_sir_not_tight_of_source_ratio (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n)) :
    ¬IsTightMeasureSet (Set.range fun n =>
      (physicalTerminalTreeLaw (mu n) n (X n) : Measure PlaneTree.Tree)) := by
  sorry
/-- Theorem `thm:SIR` (I)(a). If `λ_n ∼ λ/n` with `λ > 1`, the infectious count path
`(I_{⌊nt⌋}/n)_{t ≥ 0}` converges in distribution, uniformly on compact sets, to
`max(2 - 2 g_λ(t) - t, 0) · 1_A`, `A` the survival event of the Bienaymé tree with offspring law
`G(1/(1+λ))`. -/
theorem physical_sir_fluid_limit_of_source_ratio (rate : ℕ → ℝ≥0)
    (lam : ℝ≥0) (hlam : 1 < (lam : ℝ))
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1))
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n)) :
    Tendsto (fun n => physicalPopulationPathLaw (mu n) n (X n)) atTop
      (𝓝 (geometricSurvivalPathLaw lam)) := by
  sorry
/-- Theorem `thm:SIR` (II)(a). If `λ_n ≫ 1/n`, `sup_{0 ≤ t ≤ 2} |I_{⌊nt⌋}/n - min(t, 2-t)|` tends to
zero in probability: the probability that it is at least `eps` tends to zero, for every `eps > 0`. -/
theorem physical_sir_strong_uniform_fluid_limit_of_source_ratio (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n))
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => (physicalCountsPathLaw (mu n) n (X n) : Measure (ℕ → Counts)).real
      {H | ∃ t ∈ Set.Icc (0 : ℝ) 2, eps ≤
        |((H ⌊(n : ℝ) * t⌋₊).infectious : ℝ) / n - min t (2 - t)|}) atTop (𝓝 0) := by
  sorry
/-- Theorem `thm:SIR` (II)(b), height. If `λ_n ≫ 1/n`, the height of a uniform vertex of the full
infection tree divided by `ln n` converges in probability to `1`. -/
theorem physical_sir_strong_terminal_uniform_height_of_source_ratio (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n))
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => physicalUniformHeightLaw (mu n) n (X n) (2 * n + 1)
      {h | eps ≤ |(h : ℝ) / Real.log (n : ℝ) - 1|}) atTop (𝓝 0) := by
  sorry
/-- Theorem `thm:SIR` (II)(b), distance. If `λ_n ≫ 1/n`, the distance between two independent uniform
vertices of the full infection tree (possibly equal) divided by `ln n` converges in probability to `2`. -/
theorem physical_sir_strong_terminal_uniform_distance_of_source_ratio (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n))
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => physicalPairDataLaw (mu n) n (X n) (2 * n + 1)
      {z | eps ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - 2|}) atTop (𝓝 0) := by
  sorry
/-- Theorem `thm:SIR` (II)(b), maximum. If `λ_n ≫ 1/n`, the height of the full infection tree (maximal
address length of its vertices at step `2 n + 1`) divided by `ln n` converges in probability to `e`. -/
theorem physical_sir_strong_terminal_maximum_of_source_ratio (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n))
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => (physicalTreePathLaw (mu n) n (X n) : Measure (ℕ → TreeState))
      {H | eps ≤ |(((H (2 * n + 1)).tree.vertices.sup List.length : ℕ) : ℝ) /
        Real.log (n : ℝ) - Real.exp 1|}) atTop (𝓝 0) := by
  sorry
end Freezing1.SIR

/-! ## Sanity statements on the meaning of `PoissonSIRData` -/

namespace Freezing1.SIR
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]
variable {mu : Measure Ω} [IsProbabilityMeasure mu] {n : ℕ} {rate : ℝ≥0}
  {X : (c : ClockSlot n) → Ω → ClockDatum c}
/-- Under `PoissonSIRData` and a positive rate, the physical history of the infection tree is the
uniform attachment with freezing of the paper, with the infection probabilities of its Markov chain. -/
theorem PoissonSIRData.treePathLaw_eq (h : PoissonSIRData mu n rate X) (hr : 0 < rate) :
    (physicalTreePathLaw mu n X : Measure (ℕ → TreeState)) = treeFullLaw rate n := by
  sorry
end Freezing1.SIR

/-! ## Non-vacuity of `PoissonSIRData` -/

namespace Freezing1.SIR
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology
set_option backward.isDefEq.respectTransparency false
/-- For every population size and every positive contact rate there are a probability space and
independent clock data (exponential periods, Poisson contact paths) satisfying `PoissonSIRData`. -/
theorem PoissonSIRData.exists_data (n : ℕ) (rate : ℝ≥0) (hrate : 0 < rate) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (mu : Measure Ω) (_ : IsProbabilityMeasure mu)
      (X : (c : ClockSlot n) → Ω → ClockDatum c), PoissonSIRData mu n rate X := by
  sorry
/-- The sequence-level hypothesis `hdata` of the physical theorems is satisfiable along every
eventually positive rate sequence. -/
theorem PoissonSIRData.exists_family (rate : ℕ → ℝ≥0) (hpos : ∀ᶠ n in atTop, 0 < rate n) :
    ∃ (Ω : ℕ → Type) (_ : ∀ n, MeasurableSpace (Ω n)) (mu : (n : ℕ) → Measure (Ω n))
      (_ : ∀ n, IsProbabilityMeasure (mu n)) (X : (n : ℕ) → (c : ClockSlot n) → Ω n → ClockDatum c),
      ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n) := by
  sorry
end Freezing1.SIR

-- restore the name of this module (see the `setMainModule` remark in the header)
run_cmd Lean.modifyEnv (·.setMainModule `Challenge.Sir)
