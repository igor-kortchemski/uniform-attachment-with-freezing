module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic
public import Mathlib.Tactic.DeriveCountable
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Finset.Sort
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Challenge: local limits of uniform attachment trees with freezing (Theorems `thm:cvlocale`, `thm:BGW`)

Source: *Uniform attachment with freezing*, `attachement-uniforme-1-final.tex`. This interface covers
the two local-limit results of the Introduction.

* Theorem `thm:cvlocale` (Lean: `local_convergence_equivalences`, `local_convergence_common_limit`).
  For schedules `x n` converging coordinatewise to a schedule `y` with `τ(y) = ∞`, the following are
  equivalent: (I) the laws of the local trees `T_n(x n)` converge weakly in the local space,
  (II) the trees `T_n(y)` converge locally almost surely, (III) `∑ 1_{y_i = -1} / S_i(y)` diverges.
  In that case the limit is the law of the pathwise local limit `T_∞(y)` of `T_n(y)`.
* Theorem `thm:BGW` (Lean: `iid_signs_geometric_local_limit`, `planeLimitLaw_isBienayme`,
  `planeLimitLaw_eq_geometricBienaymeLaw`, `planeLimitLaw_offspring_mass`). For i.i.d. signs with
  `P(+1) = p ∈ [0, 1)`, the local limit `T_∞`, read as a plane tree by ordering the children of every
  vertex by increasing birth time and forgetting labels, is a Bienaymé tree with geometric offspring law
  `μ(k) = (1 - p) p^k`.

Every definition used by these statements is reproduced below, verbatim from the development, with its
ordinary mathematical meaning in the docstring; the theorem bodies of the statements are deliberately
left as holes. A few additional small theorems fixing the meaning of the model (probability laws, local
balls and topology, plane trees, Bienaymé laws, i.i.d. sign transitions) are included as extra targets;
three of them (`Forward.transitionLaw_probability`, `Forward.ValidAt.localBalls_valid`,
`LocalTree.canonical_planeOffspring`) are used inside definition bodies and are stated as targets because
their proofs would create module-private auxiliary lemmas, whose names contain the module name and so
cannot be reproduced in a separate Challenge module. It does not cover the height, same-law or SIR
statements, and it is not a statement about the whole manuscript.
-/

@[expose] public section

/-! ## Schedules, the walk and the extinction time -/

namespace Freezing1

/-- An attachment/freezing schedule `X = (X_i)_{i ≥ 1}`; index zero is unused. The value `true` at
index `i` is the sign `X_i = +1` (attachment at step `i`), `false` is `X_i = -1` (freezing). -/
abbrev SignSequence := ℕ → Bool

/-- The integer walk `S_n = 1 + ∑_{i=1}^n X_i` of the Introduction: the number of active vertices of
the tree after `n` steps. It is not stopped at its first zero. -/
def activeCount (x : SignSequence) (n : ℕ) : ℤ :=
  1 + ∑ i ∈ Finset.range n, if x (i + 1) then 1 else -1

/-- First zero `τ` of the walk `S`, or infinity if there is none (equation `eq:defintro`). -/
noncomputable def extinctionTime (x : SignSequence) : ℕ∞ :=
  open Classical in
  if h : ∃ k, activeCount x k = 0 then (Nat.find h : ℕ∞) else ⊤

/-- The walk starts at `1`, so `τ ≤ n` exactly when the walk vanishes at some time `k ≤ n`. -/
theorem extinctionTime_le_iff (x : SignSequence) (n : ℕ) :
    extinctionTime x ≤ n ↔ ∃ k ≤ n, activeCount x k = 0 := by
  sorry

end Freezing1

/-! ## Algorithm 1: the deterministic transition and the structural invariants -/

namespace Freezing1.Forward

/-- The state of Algorithm 1: vertices (labelled by their attachment times, the root being `0`), the
active vertices, the graph of the tree, the parent map, the heights, and the freezing time of each
frozen vertex. -/
structure State where
  vertices : Finset ℕ
  active : Finset ℕ
  graph : SimpleGraph ℕ
  parent : ℕ → ℕ
  height : ℕ → ℕ
  frozenAt : ℕ → Option ℕ

/-- The initial tree: the single active root `0` at height `0`. -/
def initial : State where
  vertices := {0}
  active := {0}
  graph := ⊥
  parent := fun _ => 0
  height := fun _ => 0
  frozenAt := fun _ => none

/-- Attach the fresh vertex `t` to the chosen active vertex `v`. -/
def attach (s : State) (t v : ℕ) : State where
  vertices := insert t s.vertices
  active := insert t s.active
  graph := s.graph ⊔ SimpleGraph.edge v t
  parent := Function.update s.parent t v
  height := Function.update s.height t (s.height v + 1)
  frozenAt := Function.update s.frozenAt t none

/-- Freeze the chosen vertex and record its displayed label (its freezing time `t`). -/
def freeze (s : State) (t v : ℕ) : State where
  vertices := s.vertices
  active := s.active.erase v
  graph := s.graph
  parent := s.parent
  height := s.height
  frozenAt := Function.update s.frozenAt v (some t)

/-- Algorithm 1's transition. Invalid choices leave the state unchanged;
all theorems about the process require a legal active choice when one exists. -/
def step (s : State) (t : ℕ) (sign : Bool) (v : ℕ) : State :=
  if v ∈ s.active then if sign then attach s t v else freeze s t v else s

/-- Structural invariants of a state reached at time `n`: a rooted tree on vertices bounded by `n`,
with a parent map pointing to older vertices, heights increasing by one along parent edges, and the
active vertices exactly those that are not frozen. -/
structure ValidAt (n : ℕ) (s : State) : Prop where
  root_mem : 0 ∈ s.vertices
  active_subset : s.active ⊆ s.vertices
  vertices_le : ∀ v ∈ s.vertices, v ≤ n
  adj_mem : ∀ {u v}, s.graph.Adj u v → u ∈ s.vertices ∧ v ∈ s.vertices
  acyclic : s.graph.IsAcyclic
  reachable : ∀ v ∈ s.vertices, s.graph.Reachable 0 v
  parent_mem : ∀ v ∈ s.vertices, s.parent v ∈ s.vertices
  parent_lt : ∀ v ∈ s.vertices, v ≠ 0 → s.parent v < v
  parent_adj : ∀ v ∈ s.vertices, v ≠ 0 → s.graph.Adj (s.parent v) v
  height_root : s.height 0 = 0
  height_parent : ∀ v ∈ s.vertices, v ≠ 0 → s.height v = s.height (s.parent v) + 1
  active_iff : ∀ v ∈ s.vertices, v ∈ s.active ↔ s.frozenAt v = none
  adj_height : ∀ {u v}, s.graph.Adj u v →
    s.height u + 1 = s.height v ∨ s.height v + 1 = s.height u

/-- The initial tree satisfies the invariants at time `0`. -/
theorem initial_valid : ValidAt 0 initial := by
  constructor <;> simp [initial, SimpleGraph.reachable_bot]

end Freezing1.Forward

/-! ## The random forward tree -/

namespace Freezing1.Forward

open MeasureTheory
open scoped ENNReal Classical

/-- The discrete (power-set) σ-algebra on states. -/
instance : MeasurableSpace State := ⊤
instance : DiscreteMeasurableSpace State := ⟨fun _ => trivial⟩

/-- One uniform choice of an active vertex, followed by the deterministic Algorithm 1 transition
(an empty active set is absorbing). -/
noncomputable def transitionLaw (s : State) (t : ℕ) (sign : Bool) : Measure State :=
  if s.active.Nonempty then
    (Measure.uniformOfFinset s.active).map (fun v => step s t sign v)
  else Measure.dirac s

/-- Each transition law is a probability measure. -/
instance transitionLaw_probability (s : State) (t : ℕ) (sign : Bool) :
    IsProbabilityMeasure (transitionLaw s t sign) := by
  sorry

/-- The law of the forward random tree `T_n(x)` at time `n`, for the deterministic schedule `x`. -/
noncomputable def treeLaw (x : SignSequence) : ℕ → Measure State
  | 0 => Measure.dirac initial
  | n + 1 => (treeLaw x n).bind (fun s => transitionLaw s (n + 1) (x (n + 1)))

instance treeLaw_probability (x : SignSequence) (n : ℕ) : IsProbabilityMeasure (treeLaw x n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac initial); infer_instance
  | succ n ih =>
    exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
      (Filter.Eventually.of_forall (fun s => transitionLaw_probability s _ _))

/-- Every state sampled from the forward law is a rooted finite tree with its verified heights. -/
theorem treeLaw_valid (x : SignSequence) (n : ℕ) :
    ∀ᵐ s ∂treeLaw x n, ValidAt n s := by
  sorry

end Freezing1.Forward

/-! ## The local space of time-labelled trees -/

namespace Freezing1.LocalTree

open Filter Set TopologicalSpace
open scoped Topology Classical

/-- The record of one vertex in a ball: its birth time (the label of its incoming edge; `0` for the
root), the birth time of its parent, its height (distance to the root), and its vertex label
(`none` for the letter `a` of an active vertex, `some t` for a vertex frozen at time `t`). -/
structure VertexRecord where
  birth : ℕ
  parent : ℕ
  height : ℕ
  frozenAt : Option ℕ
  deriving DecidableEq, Countable

/-- A finite ball: a finite set of vertex records. -/
abbrev Ball := Finset VertexRecord

/-- The discrete topology on balls. -/
instance : TopologicalSpace Ball := ⊥

/-- Restriction of a ball to the vertices at height at most `h` (graph distance `≤ h` from the root). -/
def restrict (h : ℕ) (B : Ball) : Ball := B.filter (fun v => v.height ≤ h)

/-- `B` is the ball of radius `h` of a rooted locally finite tree whose vertices are identified by
the birth time of their incoming edge: it contains the root (birth `0`), has heights at most `h`,
distinct vertices have distinct births, the root has parent and height `0`, and every non-root vertex
has its parent in the ball, one level lower and older. -/
structure ValidBall (h : ℕ) (B : Ball) : Prop where
  root : ∃ v ∈ B, v.birth = 0
  bounded : ∀ v ∈ B, v.height ≤ h
  unique : ∀ v ∈ B, ∀ w ∈ B, v.birth = w.birth → v = w
  root_data : ∀ v ∈ B, v.birth = 0 → v.parent = 0 ∧ v.height = 0
  parent_data : ∀ v ∈ B, v.birth ≠ 0 →
    ∃ w ∈ B, w.birth = v.parent ∧ w.height + 1 = v.height ∧ w.birth < v.birth

/-- A coherent family of balls: `B h` is a valid ball of radius `h` and is the restriction of
`B (h + 1)`. -/
def ValidSequence (B : ℕ → Ball) : Prop :=
  ∀ h, ValidBall h (B h) ∧ restrict h (B (h + 1)) = B h

/-- The chronological local space: rooted, vertex-labelled and edge-labelled, locally finite trees
whose vertices are identified by the birth time of their incoming edge (so every non-root vertex has
an older parent), as coherent sequences of balls. This is the closed subspace of the paper's local
space that contains every tree `T_n(x)` of the model; it is not the whole space of rooted
locally finite labelled trees. Its topology is the product of the discrete topologies of the balls,
so that `t_n → t` locally if and only if every ball of `t_n` equals that of `t` for large `n`. -/
abbrev Tree := {B : ℕ → Ball // ValidSequence B}

/-- Local convergence is exactly eventual equality of every complete finite
ball, including the root and the labels on its boundary. -/
theorem tendsto_iff_balls {ι : Type*} {l : Filter ι} (T : ι → Tree) (t : Tree) :
    Tendsto T l (𝓝 t) ↔ ∀ h, ∀ᶠ i in l, (T i).val h = t.val h := by
  sorry

end Freezing1.LocalTree

/-! ## Forward trees as elements of the local space -/

namespace Freezing1

open MeasureTheory
open scoped Classical

namespace LocalTree

/-- The Borel σ-algebra of the local space. -/
instance : MeasurableSpace Tree := borel Tree
instance : BorelSpace Tree := ⟨rfl⟩

end LocalTree

namespace Forward

/-- The record of vertex `v` in the state `s`. -/
def localRecord (s : State) (v : ℕ) : LocalTree.VertexRecord where
  birth := v
  parent := if v = 0 then 0 else s.parent v
  height := s.height v
  frozenAt := s.frozenAt v

/-- The ball of radius `h` (height at most `h`) of the state `s`. -/
def localBall (s : State) (h : ℕ) : LocalTree.Ball :=
  LocalTree.restrict h (s.vertices.image (localRecord s))

/-- Membership is the exact graph-distance ball, restricted to actual vertices. -/
theorem ValidAt.localBall_graph_distance {n : ℕ} {s : State} (hs : ValidAt n s)
    (h v : ℕ) :
    localRecord s v ∈ localBall s h ↔ v ∈ s.vertices ∧ s.graph.dist 0 v ≤ h := by
  sorry

/-- The balls of a valid state form a coherent family of valid balls, that is, an element of the
local space. -/
theorem ValidAt.localBalls_valid {n : ℕ} {s : State} (hs : ValidAt n s) :
    LocalTree.ValidSequence (localBall s) := by
  sorry

/-- The element of the local space given by a state (a fixed default outside valid states, which
has no effect under any forward law). -/
noncomputable def localTreeOfState (s : State) : LocalTree.Tree :=
  if hs : ∃ n, ValidAt n s then ⟨localBall s, hs.choose_spec.localBalls_valid⟩
  else ⟨localBall initial, initial_valid.localBalls_valid⟩

/-- On valid states, the local tree has the balls of the state. -/
theorem ValidAt.localTreeOfState_balls {n : ℕ} {s : State} (hs : ValidAt n s) :
    (localTreeOfState s).val = localBall s := by
  sorry

/-- The law of the local tree `T_n(x)` at time `n`. -/
noncomputable def localTreeLaw (x : SignSequence) (n : ℕ) : Measure LocalTree.Tree :=
  (treeLaw x n).map localTreeOfState

instance localTreeLaw_probability (x : SignSequence) (n : ℕ) :
    IsProbabilityMeasure (localTreeLaw x n) := by
  unfold localTreeLaw
  infer_instance

end Forward
end Freezing1

/-! ## The whole forward history on one probability space -/

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

namespace ForwardInfiniteHistory

open Forward

/-- A complete (infinite) history of states `(H n)_{n ≥ 0}`. -/
abbrev History := ℕ → State

/-- The next uniform choice is conditioned on the complete preceding path. -/
noncomputable def historyKernel (x : SignSequence) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → State) State where
  toFun H := transitionLaw (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (n + 1) (x (n + 1))
  measurable' := (measurable_from_top : Measurable
    (fun s : State => transitionLaw s (n + 1) (x (n + 1)))).comp (measurable_pi_apply _)

instance historyKernel_markov (x : SignSequence) (n : ℕ) :
    IsMarkovKernel (historyKernel x n) := by
  constructor
  intro H
  change IsProbabilityMeasure (transitionLaw (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (n + 1) (x (n + 1)))
  infer_instance

/-- The law of the complete actual forward history for the schedule `x` (Ionescu-Tulcea), including
held steps after extinction. -/
noncomputable def fullLaw (x : SignSequence) : Measure History :=
  Kernel.trajMeasure (X := fun _ => State) (Measure.dirac initial) (historyKernel x)

instance fullLaw_probability (x : SignSequence) : IsProbabilityMeasure (fullLaw x) := by
  unfold fullLaw
  infer_instance

/-- The infinite construction projects to the previously defined tree law,
for every schedule and time, including after absorption. -/
theorem map_eval (x : SignSequence) (n : ℕ) :
    (fullLaw x).map (fun H => H n) = treeLaw x n := by
  sorry

end ForwardInfiniteHistory
end Freezing1

/-! ## The pathwise local limit and the laws of the local trees -/

namespace Freezing1

open Filter MeasureTheory
open scoped Topology Classical

namespace ForwardInfiniteHistory

open Forward

/-- The pathwise local limit `T_∞` of the local trees `localTreeOfState (H n)` of a history `H`, when it
exists (a fixed default tree otherwise). -/
noncomputable def localLimit (H : History) : LocalTree.Tree :=
  if h : ∃ t : LocalTree.Tree,
      Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 t)
  then h.choose else localTreeOfState initial

/-- If the local trees of a history converge, `localLimit H` is the limit. -/
theorem tendsto_localLimit_of_exists {H : History}
    (h : ∃ t : LocalTree.Tree, Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 t)) :
    Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 (localLimit H)) := by
  sorry

/-- The law of the pathwise local limit under the law of the full history of the schedule `x`. -/
noncomputable def localLimitLaw (x : SignSequence) : ProbabilityMeasure LocalTree.Tree :=
  ProbabilityMeasure.map (⟨fullLaw x, inferInstance⟩ : ProbabilityMeasure History) localLimit

/-- The law of the local tree `T_n(x)` as a probability measure on the local space. -/
noncomputable def localProbabilityLaw (x : SignSequence) (n : ℕ) :
    ProbabilityMeasure LocalTree.Tree := ⟨localTreeLaw x n, inferInstance⟩

/-- The marginal at time `n` of the full history, seen in the local space, is the law of `T_n(x)`. -/
theorem map_eval_localTree (x : SignSequence) (n : ℕ) :
    (fullLaw x).map (fun H : History => localTreeOfState (H n)) = localTreeLaw x n := by
  sorry

end ForwardInfiniteHistory
end Freezing1

/-! ## Theorem `thm:cvlocale` -/

namespace Freezing1

open Forward ForwardInfiniteHistory Filter MeasureTheory
open scoped Topology BigOperators Classical

/-- The partial sums `∑_{i=1}^n 1_{x_i = -1} / S_i(x)` of the series in assertion (III). -/
noncomputable def freezingReciprocalSum (x : SignSequence) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, if x i then 0 else 1 / (activeCount x i : ℝ)

/-- Assertion (I) for the diagonal array `x n`: the laws of the local trees `T_n(x n)` converge
weakly (in the space of probability measures on the local space) to some probability measure. -/
def DiagonalLocalConvergence (x : ℕ → SignSequence) : Prop :=
  ∃ ν : ProbabilityMeasure LocalTree.Tree,
    Tendsto (fun n => localProbabilityLaw (x n) n) atTop (𝓝 ν)

/-- Assertion (II) for the schedule `x`: almost surely (on the probability space of the full
history of Algorithm 1) the local trees `T_n(x)` converge locally to some tree. -/
def AlmostSureLocalConvergence (x : SignSequence) : Prop :=
  ∀ᵐ H ∂fullLaw x, ∃ t : LocalTree.Tree,
    Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 t)

/-- Theorem `thm:cvlocale`: for schedules `x n` agreeing eventually with `y` coordinatewise at each
positive index, with `τ(y) = ∞`, the three assertions (I) laws of `T_n(x n)` converge locally in
distribution, (II) `T_n(y)` converges locally almost surely, (III) the sum
`∑ 1_{y_i = -1} / S_i(y)` diverges, are equivalent. The approximating trees may become extinct before
time `n` (they are then held constant). -/
theorem local_convergence_equivalences
    (x : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i)
    (hτ : extinctionTime y = ⊤) :
    (DiagonalLocalConvergence x ↔ AlmostSureLocalConvergence y) ∧
    (AlmostSureLocalConvergence y ↔ Tendsto (freezingReciprocalSum y) atTop atTop) := by
  sorry

/-- Theorem `thm:cvlocale`, last sentence: under the equivalent conditions, the pathwise limit
`T_∞(y)` is measurable (almost everywhere), is the almost sure local limit of `T_n(y)`, and its law is
the weak limit of the laws of `T_n(y)` and of the diagonal laws of `T_n(x n)`. -/
theorem local_convergence_common_limit
    (x : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i)
    (hτ : extinctionTime y = ⊤)
    (hdiv : Tendsto (freezingReciprocalSum y) atTop atTop) :
    AEMeasurable localLimit (fullLaw y) ∧
    (∀ᵐ H ∂fullLaw y,
      Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 (localLimit H))) ∧
    Tendsto (localProbabilityLaw y) atTop (𝓝 (localLimitLaw y)) ∧
    Tendsto (fun n => localProbabilityLaw (x n) n) atTop (𝓝 (localLimitLaw y)) := by
  sorry

end Freezing1

/-! ## Plane trees in canonical offspring coordinates -/

namespace Freezing1.PlaneTree

open Filter MeasureTheory Set
open scoped Topology Classical

set_option backward.isDefEq.respectTransparency false

/-- An Ulam-Harris address: a finite list of child indices. -/
abbrev Address := List ℕ
instance : MeasurableSpace Address := ⊤
instance : DiscreteMeasurableSpace Address := ⟨fun _ => trivial⟩

/-- An offspring field: a number of children at every address. -/
abbrev Offspring := Address → ℕ

/-- An offspring field is canonical when absent addresses have no children: if `j` is not a child
index of `u` (that is, not `1 ≤ j ≤ f u`), then the address `u ++ [j]` has offspring zero. -/
def Canonical (f : Offspring) : Prop :=
  ∀ (u : Address) (j : ℕ), ¬(1 ≤ j ∧ j ≤ f u) → f (u ++ [j]) = 0

/-- Locally finite plane trees (Ulam-Harris trees), encoded by canonical offspring fields. -/
abbrev Tree := {f : Offspring // Canonical f}

/-- The Borel σ-algebra of the product topology on plane trees. -/
instance : MeasurableSpace Tree := borel Tree
instance : BorelSpace Tree := ⟨rfl⟩

/-- The number of children of the root. -/
def degree (T : Tree) : ℕ := T.val []

/-- The subtree rooted at the `j`-th child of the root (`j ≥ 1`). -/
def child (T : Tree) (j : ℕ) : Tree :=
  ⟨fun u => T.val (j :: u), by
    intro u k hk
    exact T.property (j :: u) k hk⟩

end Freezing1.PlaneTree

/-! ## Pruning an offspring field -/

namespace Freezing1.PlaneTree

open MeasureTheory
open scoped Classical

/-- Keep only the offspring counts at existing addresses. -/
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

/-- The plane tree obtained from a field of potential offspring counts. -/
def prune (f : Offspring) : Tree := ⟨pruneRaw f, canonical_pruneRaw f⟩

end Freezing1.PlaneTree

/-! ## Bienaymé laws -/

namespace Freezing1.PlaneTree

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

/-- The law of independent offspring counts with law `μ` at all addresses. -/
noncomputable def offspringFieldLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Measure Offspring := Measure.infinitePi (fun _ : Address => μ)

/-- The law of the Bienaymé tree with offspring distribution `μ`: pruning of an i.i.d. offspring
field. -/
noncomputable def bienaymeLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] : Measure Tree :=
  (offspringFieldLaw μ).map prune

/-- The root of the Bienaymé tree has offspring law `μ`. -/
theorem bienaymeLaw_map_degree (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    (bienaymeLaw μ).map degree = μ := by
  sorry

/-- The Bienaymé tree law with geometric offspring distribution `μ(k) = (1 - p) p^k`. -/
noncomputable def geometricBienaymeLaw (p : unitInterval) : Measure Tree :=
  bienaymeLaw (geometricMeasure (unitInterval.symm p))

/-- The geometric Bienaymé tree law is a probability measure. -/
instance geometricBienaymeLaw_probability (p : unitInterval) :
    IsProbabilityMeasure (geometricBienaymeLaw p) := by
  sorry

/-- The standard branching characterization of a Bienaymé tree law `μ` with offspring law
`offspringLaw`: the root has the given offspring law, and conditional on its count `k` all its child
trees are independent copies of the original tree (the finite family of children has the product
law `μ ⊗ ... ⊗ μ`). -/
def IsBienayme (μ : Measure Tree) (offspringLaw : Measure ℕ) : Prop :=
  μ.map degree = offspringLaw ∧
    ∀ k : ℕ, μ {T | degree T = k} ≠ 0 →
      (ProbabilityTheory.cond μ {T | degree T = k}).map
        (fun T (i : Fin k) => child T (i.val + 1)) = Measure.pi (fun _ : Fin k => μ)

/-- The Bienaymé tree law with offspring law `ρ` exists and is the unique probability measure with
the branching characterization (so `IsBienayme` is not vacuous). -/
theorem exists_unique_bienaymeLaw (ρ : Measure ℕ) [IsProbabilityMeasure ρ] :
    IsBienayme (bienaymeLaw ρ) ρ ∧
      ∀ μ : Measure Tree, IsProbabilityMeasure μ → IsBienayme μ ρ → μ = bienaymeLaw ρ := by
  sorry

end Freezing1.PlaneTree

/-! ## Chronological plane order and forgetting labels -/

namespace Freezing1.LocalTree

open Filter
open scoped Topology Classical

/-- The record of the vertex of birth `v` in a ball, if there is one. -/
noncomputable def findRecord (B : Ball) (v : ℕ) : Option VertexRecord :=
  if h : ∃ r ∈ B, r.birth = v then some h.choose else none

/-- The record of the vertex of birth `v` in the tree `T` (it lies in the ball of radius `v`). -/
noncomputable def recordAt (T : Tree) (v : ℕ) : Option VertexRecord :=
  findRecord (T.val v) v

/-- The birth times of the children of the vertex of birth `v` (the actual parent edges). -/
noncomputable def childIDs (T : Tree) (v : ℕ) : Finset ℕ :=
  match recordAt T v with
  | none => ∅
  | some r => ((T.val (r.height + 1)).filter
      (fun q => q.birth ≠ 0 ∧ q.parent = v)).image VertexRecord.birth

/-- The children of the vertex of birth `v`, listed by increasing birth time. -/
noncomputable def childList (T : Tree) (v : ℕ) : List ℕ :=
  (childIDs T v).sort (· ≤ ·)

-- Lean shares the auxiliary `match_1` of identical `match` expressions inside one module; the source
-- keeps this definition in a separate module (with its own `follow.match_1`), so sharing is disabled.
set_option bootstrap.genMatcherCode false in
/-- Follow the Ulam-Harris address `u` from the vertex of birth `v`, taking the `j`-th child in
chronological order at each step; `none` if the address is absent. -/
noncomputable def follow (T : Tree) (v : ℕ) : PlaneTree.Address → Option ℕ
  | [] => some v
  | j :: u => if j = 0 then none else
      ((childList T v)[j - 1]?).bind (fun w => follow T w u)

/-- The number of children of the vertex reached by the address `u` from the root (zero if the
address is absent). -/
noncomputable def planeOffspring (T : Tree) (u : PlaneTree.Address) : ℕ :=
  match follow T 0 u with
  | none => 0
  | some v => (childIDs T v).card

/-- The chronological offspring coordinates are canonical (absent addresses have no children). -/
theorem canonical_planeOffspring (T : Tree) : PlaneTree.Canonical (planeOffspring T) := by
  sorry

/-- The plane tree obtained from a local tree by ordering the children of every vertex by increasing
birth time and forgetting all labels. -/
noncomputable def toPlaneTree (T : Tree) : PlaneTree.Tree :=
  ⟨planeOffspring T, canonical_planeOffspring T⟩

/-- The root degree of the plane tree is the number of children of the root. -/
theorem degree_toPlaneTree (T : Tree) :
    PlaneTree.degree (toPlaneTree T) = (childIDs T 0).card := by
  sorry

/-- Forgetting labels (chronological order) is continuous from the local space to plane trees. -/
theorem continuous_toPlaneTree : Continuous toPlaneTree := by
  sorry

end Freezing1.LocalTree

/-! ## Finite prefixes of histories -/

namespace Freezing1.CountableMarkovChain

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [MeasurableSpace E]

/-- A finite history `(H i)_{i ≤ n}` with values in `E`. -/
abbrev Prefix (n : ℕ) := Finset.Iic n → E

end Freezing1.CountableMarkovChain

/-! ## The forward process with i.i.d. random signs -/

namespace Freezing1.ForwardAnnealed

open Forward MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

/-- The law of one sign: `+1` (`true`) with probability `p` and `-1` (`false`) with probability `1 - p`. -/
noncomputable def signLaw (p : unitInterval) : Measure Bool :=
  bernoulliMeasure true false p

instance signLaw_probability (p : unitInterval) : IsProbabilityMeasure (signLaw p) := by
  unfold signLaw
  infer_instance

/-- One step with a fresh independent sign of parameter `p`: the sign is averaged out in the uniform
transition of Algorithm 1. -/
noncomputable def transitionLaw (p : unitInterval) (s : State) (t : ℕ) : Measure State :=
  (signLaw p).bind (fun sign => Forward.transitionLaw s t sign)

instance transitionLaw_probability (p : unitInterval) (s : State) (t : ℕ) :
    IsProbabilityMeasure (transitionLaw p s t) :=
  isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
    (Filter.Eventually.of_forall fun sign => Forward.transitionLaw_probability s t sign)

/-- The transition law as a Markov kernel on states. -/
noncomputable def transitionKernel (p : unitInterval) (t : ℕ) : Kernel State State :=
  ⟨fun s => transitionLaw p s t, measurable_from_top⟩

-- Same matcher-sharing remark as for `LocalTree.follow`.
set_option bootstrap.genMatcherCode false in
/-- The law of the tree at time `n` when the signs are i.i.d. with parameter `p` (a fresh sign at each
transition). -/
noncomputable def treeLaw (p : unitInterval) : ℕ → Measure State
  | 0 => Measure.dirac initial
  | n + 1 => (treeLaw p n).bind (fun s => transitionLaw p s (n + 1))

/-- For `p = 0` (all signs `-1`) the averaged tree law is the fixed-schedule law. -/
theorem treeLaw_zero_parameter (n : ℕ) : treeLaw 0 n = Forward.treeLaw (fun _ => false) n := by
  sorry

/-- For `p = 1` (all signs `+1`) the averaged tree law is the fixed-schedule law. -/
theorem treeLaw_one_parameter (n : ℕ) : treeLaw 1 n = Forward.treeLaw (fun _ => true) n := by
  sorry

end Freezing1.ForwardAnnealed

/-! ## The whole annealed history on one probability space -/

namespace Freezing1.ForwardAnnealed

open Forward MeasureTheory ProbabilityTheory CountableMarkovChain
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false
set_option linter.auxLemma false

/-- Auxiliary proof `n ∈ Finset.Iic n`. In the source this is the automatically abstracted nested proof
of `historyKernel` (and `historyKernel._proof_2` below its measurability proof); they are stated
explicitly here because, within one module, Lean would otherwise reuse the identical auxiliary proof of
`ForwardInfiniteHistory.historyKernel` (which lives in another source module). -/
theorem historyKernel._proof_1 (n : ℕ) :
    @Membership.mem ℕ (Finset ℕ) SetLike.instMembership (Finset.Iic n) n :=
  Finset.mem_Iic.mpr le_rfl

/-- Measurability of the next-state map of `historyKernel` (see `historyKernel._proof_1`). -/
theorem historyKernel._proof_2 (p : unitInterval) (n : ℕ) :
    Measurable (⇑(transitionKernel p (n + 1)) ∘
      fun H : Prefix (E := State) n => H ⟨n, Freezing1.ForwardAnnealed.historyKernel._proof_1 n⟩) :=
  ((transitionKernel p (n + 1)).measurable.comp (measurable_pi_apply _) :
    Measurable (fun H : Prefix (E := State) n =>
      transitionLaw p (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (n + 1)))

/-- The next state given the complete preceding path, with a fresh independent sign. -/
noncomputable def historyKernel (p : unitInterval) (n : ℕ) :
    Kernel (Prefix (E := State) n) State where
  toFun H := transitionLaw p (H ⟨n, Freezing1.ForwardAnnealed.historyKernel._proof_1 n⟩) (n + 1)
  measurable' := Freezing1.ForwardAnnealed.historyKernel._proof_2 p n

instance historyKernel_markov (p : unitInterval) (n : ℕ) :
    IsMarkovKernel (historyKernel p n) := ⟨fun H =>
      transitionLaw_probability p (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (n + 1)⟩

/-- The law of the complete history of states when the signs are i.i.d. with parameter `p`
(Ionescu-Tulcea). -/
noncomputable def fullLaw (p : unitInterval) : Measure ForwardInfiniteHistory.History :=
  Kernel.traj (X := fun _ => State) (historyKernel p) 0 (fun _ => initial)

instance fullLaw_probability (p : unitInterval) : IsProbabilityMeasure (fullLaw p) := by
  unfold fullLaw
  infer_instance

/-- The infinite averaged history has the original averaged tree marginals. -/
theorem map_eval (p : unitInterval) (n : ℕ) :
    (fullLaw p).map (fun H => H n) = treeLaw p n := by
  sorry

end Freezing1.ForwardAnnealed

/-! ## The annealed local limit and its plane tree -/

namespace Freezing1.ForwardAnnealed

open Forward ForwardInfiniteHistory Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology BigOperators Classical

set_option backward.isDefEq.respectTransparency false

/-- The law of the pathwise local limit under the law of the annealed history. -/
noncomputable def localLimitLaw (p : unitInterval) : ProbabilityMeasure LocalTree.Tree :=
  ProbabilityMeasure.map (⟨fullLaw p, inferInstance⟩ : ProbabilityMeasure History) localLimit

/-- Almost surely under the annealed history law, the sequence of local trees converges locally to
the pathwise local limit `localLimit` (the labelled version of the almost-sure convergence in
Theorem BGW). -/
theorem fullLaw_tendsto_localLimit (p : unitInterval) (hp : (p : ℝ) < 1) :
    ∀ᵐ H ∂fullLaw p,
      Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 (localLimit H)) := by
  sorry

/-- The pathwise local limit is almost-everywhere measurable under the annealed history law, so its
push-forward `localLimitLaw` is the genuine image measure and not a junk value. -/
theorem aemeasurable_localLimit (p : unitInterval) (hp : (p : ℝ) < 1) :
    AEMeasurable localLimit (fullLaw p) := by
  sorry

/-- The averaged transition is the mixture of the fixed-sign transitions with the sign law
`+1` with probability `p` and `-1` with probability `1 - p`. -/
theorem transitionLaw_apply_split (p : unitInterval) (s : State) (t : ℕ) (A : Set State) :
    transitionLaw p s t A =
      (unitInterval.toNNReal p : ℝ≥0∞) * Forward.transitionLaw s t true A +
      (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) *
        Forward.transitionLaw s t false A := by
  sorry

end Freezing1.ForwardAnnealed

namespace Freezing1.ForwardAnnealed

open Forward ForwardInfiniteHistory Filter MeasureTheory
open scoped Topology Classical

/-- The plane tree of the pathwise local limit: chronological order, labels forgotten. -/
noncomputable def planeLimit (H : History) : PlaneTree.Tree :=
  LocalTree.toPlaneTree (ForwardInfiniteHistory.localLimit H)

/-- The law of the plane tree of the local limit. -/
noncomputable def planeLimitLaw (p : unitInterval) : ProbabilityMeasure PlaneTree.Tree :=
  (localLimitLaw p).map LocalTree.toPlaneTree

end Freezing1.ForwardAnnealed

/-! ## Theorem `thm:BGW` -/

namespace Freezing1.ForwardAnnealed

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

/-- Theorem `thm:BGW`: the law of the plane tree of the local limit of the i.i.d.-sign tree, for
`p ∈ [0, 1)`, satisfies the branching characterization of a Bienaymé tree with the geometric offspring
law `μ(k) = (1 - p) p^k`. -/
theorem planeLimitLaw_isBienayme (p : unitInterval) (hp : (p : ℝ) < 1) :
    PlaneTree.IsBienayme (planeLimitLaw p) (geometricMeasure (unitInterval.symm p)) := by
  sorry

/-- Theorem `thm:BGW`: the law of the plane tree of the local limit is the geometric Bienaymé tree
law. -/
theorem planeLimitLaw_eq_geometricBienaymeLaw (p : unitInterval) (hp : (p : ℝ) < 1) :
    (planeLimitLaw p : Measure PlaneTree.Tree) = PlaneTree.geometricBienaymeLaw p := by
  sorry

/-- Theorem `thm:BGW`: the root of the limit tree has `k` children with probability
`(1 - p) p^k`. -/
theorem planeLimitLaw_offspring_mass (p : unitInterval) (hp : (p : ℝ) < 1) (k : ℕ) :
    (planeLimitLaw p : Measure PlaneTree.Tree) {T | PlaneTree.degree T = k} =
      ENNReal.ofReal ((1 - (p : ℝ)) * (p : ℝ) ^ k) := by
  sorry

/-- Theorem `thm:BGW` for the actual iid-sign process, with the source's chronological
ordering and the measurable pathwise limit on its genuine probability space: almost surely the plane
trees of the finite trees converge to `planeLimit H`, and the law of `planeLimit` under the full
history law is the geometric Bienaymé tree law. -/
theorem iid_signs_geometric_local_limit (p : unitInterval) (hp : (p : ℝ) < 1) :
    (∀ᵐ H ∂fullLaw p,
      Tendsto (fun n => LocalTree.toPlaneTree (Forward.localTreeOfState (H n))) atTop
        (𝓝 (planeLimit H))) ∧
      (fullLaw p).map planeLimit = PlaneTree.geometricBienaymeLaw p := by
  sorry

end Freezing1.ForwardAnnealed
