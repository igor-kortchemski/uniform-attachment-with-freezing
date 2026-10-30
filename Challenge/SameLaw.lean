module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Tactic

/-!
# Challenge: the forward and reverse constructions have the same law (Theorem `thm:samelaw`)

Source: *Uniform attachment with freezing*, `attachement-uniforme-1-final.tex`. This interface covers
Theorem `thm:samelaw`: the tree `T_n` built by the attachment/freezing Algorithm 1 and the tree `T^n`
built by the time-reversed growth/coalescent Algorithm 2 have the same distribution once the active
labels `a_1, ..., a_{S_n}` of `T^n` are erased (relabelled `a`), for every fixed schedule and every
`0 ≤ n ≤ τ`.

Encoding. Both random trees are encoded by the same finite `Observable`: vertices carry canonical integer
identifiers (the root has identifier `0`; every other vertex is named by the label of its parent edge,
i.e. by the time at which that edge appears), and the observable records the vertex identifiers, the
simple graph on them, the set of active identifiers and the set of pairs (identifier, freezing time) of
frozen vertices. The edge label of an edge is the larger of its two endpoint identifiers. The forward
tree is `Forward.treeLaw` pushed through `CanonicalTree.forward`; the reverse tree is the timestamped
reverse forest law `ReverseStamped.treeLaw` pushed through `CanonicalTree.reverse`, which forgets exactly
the distinctions between the active labels. Every definition used by the statements is reproduced below
with its ordinary mathematical meaning; the bodies of the target theorems are deliberately left as holes.
The main target is `CanonicalTree.construction_laws_eq`; the other targets pin down the meaning of the
objects (probability-measure facts, characterizations of the observable, support of both laws, the
deterministic root-merging operations). This file does not cover any other manuscript result.
-/

@[expose] public section

namespace Freezing1

/-! ## Schedules, the walk and the extinction time -/

/-- An attachment/freezing schedule `X = (X_i)_{i ≥ 1}`; index zero is unused. The value `true` at index
`i + 1` is the sign `X_{i+1} = +1` (attachment), `false` is `-1` (freezing). -/
abbrev SignSequence := ℕ → Bool

/-- The number of attachment steps (signs `+1`) among the first `n` signs. -/
def plusCount (x : SignSequence) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, if x (i + 1) then 1 else 0

/-- The integer walk `S_n = 1 + ∑_{i=1}^n X_i` of the Introduction (not stopped at its first zero). -/
def activeCount (x : SignSequence) (n : ℕ) : ℤ :=
  1 + ∑ i ∈ Finset.range n, if x (i + 1) then 1 else -1

/-- The first zero `τ = inf {n ≥ 1 : S_n = 0}` of the walk, or `∞` if there is none (equation `eq:defintro`). -/
noncomputable def extinctionTime (x : SignSequence) : ℕ∞ :=
  open Classical in
  if h : ∃ k, activeCount x k = 0 then (Nat.find h : ℕ∞) else ⊤

/-- The walk starts at `1`, so `τ ≤ n` exactly when the walk vanishes at some time `k ≤ n`. -/
theorem extinctionTime_le_iff (x : SignSequence) (n : ℕ) :
    extinctionTime x ≤ n ↔ ∃ k ≤ n, activeCount x k = 0 := by
  sorry

end Freezing1

/-! ## The forward construction (Algorithm 1) -/

namespace Freezing1.Forward

/-- A state of Algorithm 1: the finite vertex set (persistent identifiers; `0` is the root and a vertex
created at step `t` has identifier `t`), the active vertices, the graph on `ℕ`, the parent map, the height
map, and the freezing label of each vertex (`some t` if it froze at step `t`, `none` while active). -/
structure State where
  vertices : Finset ℕ
  active : Finset ℕ
  graph : SimpleGraph ℕ
  parent : ℕ → ℕ
  height : ℕ → ℕ
  frozenAt : ℕ → Option ℕ

/-- The tree `T_0`: a single root vertex (identifier `0`), active, with no edge. -/
def initial : State where
  vertices := {0}
  active := {0}
  graph := ⊥
  parent := fun _ => 0
  height := fun _ => 0
  frozenAt := fun _ => none

/-- Attach the fresh vertex `t` to the active vertex `v` (an edge labelled `t`, new vertex active). -/
def attach (s : State) (t v : ℕ) : State where
  vertices := insert t s.vertices
  active := insert t s.active
  graph := s.graph ⊔ SimpleGraph.edge v t
  parent := Function.update s.parent t v
  height := Function.update s.height t (s.height v + 1)
  frozenAt := Function.update s.frozenAt t none

/-- Freeze the vertex `v` at step `t` (its active label `a` is replaced by the label `t`). -/
def freeze (s : State) (t v : ℕ) : State where
  vertices := s.vertices
  active := s.active.erase v
  graph := s.graph
  parent := s.parent
  height := s.height
  frozenAt := Function.update s.frozenAt v (some t)

/-- One deterministic step of Algorithm 1 at time `t` for the sign `sign` and the chosen vertex `v`: attach if `sign = +1`, freeze if `sign = -1` (an inactive choice leaves the state unchanged). -/
def step (s : State) (t : ℕ) (sign : Bool) (v : ℕ) : State :=
  if v ∈ s.active then if sign then attach s t v else freeze s t v else s

/-- The structural invariants of a forward state at time `n`: it is a finite rooted tree on identifiers `≤ n` rooted at `0`, parents have smaller identifiers, heights are depths, and a vertex is active iff it has no freezing label. -/
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

/-- The actual finite tree: the state graph restricted to its vertex set. -/
def State.tree (s : State) : SimpleGraph {v // v ∈ s.vertices} :=
  s.graph.induce (s.vertices : Set ℕ)

end Freezing1.Forward

namespace Freezing1.Forward

open MeasureTheory
open scoped ENNReal Classical

/-- Every set of states is measurable (discrete measurable space). -/
instance : MeasurableSpace State := ⊤

/-- One step of Algorithm 1: choose a uniform active vertex (if there is none, stay put), then apply the deterministic transition with the sign `sign` at time `t`. -/
noncomputable def transitionLaw (s : State) (t : ℕ) (sign : Bool) : Measure State :=
  if s.active.Nonempty then
    (Measure.uniformOfFinset s.active).map (fun v => step s t sign v)
  else Measure.dirac s

/-- The law of the random tree `T_n` of Algorithm 1 for the schedule `x`: `T_0` is the root, and `T_{n+1}` is obtained from `T_n` by one step with the sign `x (n+1)` and a fresh uniform choice. -/
noncomputable def treeLaw (x : SignSequence) : ℕ → Measure State
  | 0 => Measure.dirac initial
  | n + 1 => (treeLaw x n).bind (fun s => transitionLaw s (n + 1) (x (n + 1)))

/-- Exact finite transition probabilities: if there is an active vertex, the probability of a set `A` of states is the proportion of active choices `v` whose step lands in `A`. -/
theorem transitionLaw_apply (s : State) (t : ℕ) (sign : Bool)
    (h : s.active.Nonempty) (A : Set State) :
    transitionLaw s t sign A =
      ((s.active.filter (fun v => step s t sign v ∈ A)).card : ℝ≥0∞) / s.active.card := by
  sorry

/-- Every state sampled from the forward law at time `n` satisfies the structural invariants `ValidAt n`. -/
theorem treeLaw_valid (x : SignSequence) (n : ℕ) :
    ∀ᵐ s ∂treeLaw x n, ValidAt n s := by
  sorry

/-- Every state sampled from the forward law is a finite tree in the sense of Mathlib. -/
theorem treeLaw_isTree (x : SignSequence) (n : ℕ) :
    ∀ᵐ s ∂treeLaw x n, s.tree.IsTree := by
  sorry

/-- For `n ≤ τ`, almost surely the forward tree has `S_n` active vertices and `(number of +1 among the first n signs) + 1` vertices in total. -/
theorem treeLaw_counts (x : SignSequence) (n : ℕ) (hτ : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ s ∂treeLaw x n, (s.active.card : ℤ) = activeCount x n ∧
      s.vertices.card = plusCount x n + 1 := by
  sorry

end Freezing1.Forward

/-! ## Rooted forests and the deterministic reverse operations -/

/-
Comparator note. The proofs of the fields of `RootedForest.join` and of the lemma `RootedForest.depth_eq_zero_iff`
below call `omega`, which stores an auxiliary lemma under a *private* name. In Lean's module system a private name
is `_private.<module>.0.<name>`, and in the development these declarations live in the module
`Freezing1.RootedForest`. To reproduce the same constants (hence the same names) in this file, the module name used
to build private names is set to `Freezing1.RootedForest` for the next block only and restored right after it.
This has no other effect: no declaration, definition, instance or statement is changed.
-/
open Lean in
run_cmd modifyEnv (·.setMainModule `Freezing1.RootedForest)

namespace Freezing1

/-- A finite forest of rooted trees on a vertex set in `V`, given by the parent map, the root of the component and the depth, together with the invariants of a parent forest: roots are their own parents and have depth `0`, and a non-root vertex has depth one more than its parent. -/
structure RootedForest (V : Type*) [DecidableEq V] where
  vertices : Finset V
  parent : V → V
  root : V → V
  depth : V → ℕ
  parent_mem : ∀ v ∈ vertices, parent v ∈ vertices
  root_mem : ∀ v ∈ vertices, root v ∈ vertices
  root_fixed : ∀ v ∈ vertices, root (root v) = root v
  parent_root : ∀ v ∈ vertices, parent (root v) = root v
  root_parent : ∀ v ∈ vertices, root (parent v) = root v
  depth_root : ∀ v ∈ vertices, depth (root v) = 0
  depth_parent : ∀ v ∈ vertices, v ≠ root v → depth (parent v) + 1 = depth v

namespace RootedForest

variable {V : Type*} [DecidableEq V]

/-- The forest whose components are the given isolated vertices. -/
def isolated (s : Finset V) : RootedForest V where
  vertices := s
  parent := id
  root := id
  depth := fun _ => 0
  parent_mem := by simp
  root_mem := by simp
  root_fixed := by simp
  parent_root := by simp
  root_parent := by simp
  depth_root := by simp
  depth_parent := by simp

/-- The set of roots (one for each component) of the forest. -/
def roots (F : RootedForest V) : Finset V :=
  F.vertices.filter fun v => F.root v = v

@[simp] theorem mem_roots {F : RootedForest V} {v : V} :
    v ∈ F.roots ↔ v ∈ F.vertices ∧ F.root v = v := Finset.mem_filter

theorem depth_eq_zero_iff (F : RootedForest V) {v : V} (hv : v ∈ F.vertices) :
    F.depth v = 0 ↔ F.root v = v := by
  constructor
  · intro hz
    by_contra h
    have := F.depth_parent v hv (Ne.symm h)
    omega
  · intro h
    simpa only [h] using F.depth_root v hv

theorem parent_of_root (F : RootedForest V) {v : V} (hv : v ∈ F.roots) :
    F.parent v = v := by
  obtain ⟨hv, hr⟩ := mem_roots.mp hv
  simpa only [hr] using F.parent_root v hv

/-- The merge of Algorithm 2 for `X_i = +1`: the component rooted at `b` is attached below the root `a` of another component by a new parent edge from `b` to `a` (the tree obtained is rooted at `a`); both roots must exist and differ. -/
def join (F : RootedForest V) (a b : V) (ha : a ∈ F.roots) (hb : b ∈ F.roots)
    (hab : a ≠ b) : RootedForest V where
  vertices := F.vertices
  parent v := if v = b then a else F.parent v
  root v := if F.root v = b then a else F.root v
  depth v := F.depth v + if F.root v = b then 1 else 0
  parent_mem := by
    intro v hv
    split_ifs
    · exact (mem_roots.mp ha).1
    · exact F.parent_mem v hv
  root_mem := by
    intro v hv
    split_ifs
    · exact (mem_roots.mp ha).1
    · exact F.root_mem v hv
  root_fixed := by
    intro v hv
    have hra := (mem_roots.mp ha).2
    have hrr := F.root_fixed v hv
    by_cases h : F.root v = b <;> simp [h, hra, hab, hrr]
  parent_root := by
    intro v hv
    have hra := (mem_roots.mp ha).2
    have hpa := F.parent_of_root ha
    have hpr := F.parent_root v hv
    by_cases h : F.root v = b <;> simp [h, hpa, hab, hpr]
  root_parent := by
    intro v hv
    have hra := (mem_roots.mp ha).2
    have hrb := (mem_roots.mp hb).2
    have hrp := F.root_parent v hv
    by_cases h : v = b <;> simp [h, hra, hrb, hab, hrp]
  depth_root := by
    intro v hv
    have hra := (mem_roots.mp ha).2
    have hda : F.depth a = 0 := (F.depth_eq_zero_iff (mem_roots.mp ha).1).mpr hra
    have hdr := F.depth_root v hv
    have hrr := F.root_fixed v hv
    by_cases h : F.root v = b <;> simp [h, hra, hab, hda, hdr, hrr]
  depth_parent := by
    intro v hv hne
    have hra := (mem_roots.mp ha).2
    have hrb := (mem_roots.mp hb).2
    have hda : F.depth a = 0 := (F.depth_eq_zero_iff (mem_roots.mp ha).1).mpr hra
    have hdb : F.depth b = 0 := (F.depth_eq_zero_iff (mem_roots.mp hb).1).mpr hrb
    have hrp := F.root_parent v hv
    by_cases hvb : v = b
    · subst v
      simp [hra, hrb, hda, hdb, hab]
    · have hvr : v ≠ F.root v := by
        intro heq
        have hnot : F.root v ≠ b := by simpa only [← heq] using hvb
        simp only [hnot, ↓reduceIte] at hne
        exact hne heq
      have hd := F.depth_parent v hv hvr
      simp only [hvb, ↓reduceIte, hrp]
      omega

/-- A merge removes exactly its second root from the set of roots. -/
theorem join_roots (F : RootedForest V) {a b : V}
    (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b) :
    (F.join a b ha hb hab).roots = F.roots.erase b := by
  sorry

/-- The undirected graph of the forest: two distinct vertices are adjacent iff one is the parent of the other. -/
def graph (F : RootedForest V) : SimpleGraph V where
  Adj u v := u ∈ F.vertices ∧ v ∈ F.vertices ∧ u ≠ v ∧
    (F.parent u = v ∨ F.parent v = u)
  symm := by
    constructor
    intro u v h
    exact ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.symm⟩
  loopless := ⟨by simp⟩

/-- Merging two roots adds exactly the edge between them to the graph. -/
theorem join_graph (F : RootedForest V) {a b : V}
    (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b) :
    (F.join a b ha hb hab).graph = F.graph ⊔ SimpleGraph.edge a b := by
  sorry

/-- The operation of Algorithm 2 for `X_i = -1`: insert a fresh isolated one-vertex tree. -/
def adjoin (F : RootedForest V) (v : V) (hv : v ∉ F.vertices) : RootedForest V where
  vertices := insert v F.vertices
  parent w := if w = v then v else F.parent w
  root w := if w = v then v else F.root w
  depth w := if w = v then 0 else F.depth w
  parent_mem := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp
    · have hwv : w ≠ v := fun h => hv (h ▸ hw)
      simp only [hwv, ↓reduceIte]
      exact Finset.mem_insert_of_mem (F.parent_mem w hw)
  root_mem := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp
    · have hwv : w ≠ v := fun h => hv (h ▸ hw)
      simp only [hwv, ↓reduceIte]
      exact Finset.mem_insert_of_mem (F.root_mem w hw)
  root_fixed := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp
    · have hwv : w ≠ v := fun h => hv (h ▸ hw)
      have hrv : F.root w ≠ v := fun h => hv (h ▸ F.root_mem w hw)
      simp [hwv, hrv, F.root_fixed w hw]
  parent_root := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp
    · have hwv : w ≠ v := fun h => hv (h ▸ hw)
      have hrv : F.root w ≠ v := fun h => hv (h ▸ F.root_mem w hw)
      simp [hwv, hrv, F.parent_root w hw]
  root_parent := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp
    · have hwv : w ≠ v := fun h => hv (h ▸ hw)
      have hpv : F.parent w ≠ v := fun h => hv (h ▸ F.parent_mem w hw)
      simp [hwv, hpv, F.root_parent w hw]
  depth_root := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp
    · have hwv : w ≠ v := fun h => hv (h ▸ hw)
      have hrv : F.root w ≠ v := fun h => hv (h ▸ F.root_mem w hw)
      simp [hwv, hrv, F.depth_root w hw]
  depth_parent := by
    intro w hw hn
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp at hn
    · have hwv : w ≠ v := fun h => hv (h ▸ hw)
      have hpv : F.parent w ≠ v := fun h => hv (h ▸ F.parent_mem w hw)
      simp only [hwv, ↓reduceIte] at hn
      simp [hwv, hpv, F.depth_parent w hw hn]

/-- Adjoining a fresh vertex makes it a new root. -/
theorem adjoin_roots (F : RootedForest V) {v : V} (hv : v ∉ F.vertices) :
    (F.adjoin v hv).roots = insert v F.roots := by
  sorry

/-- Adjoining a fresh vertex does not change the graph. -/
theorem adjoin_graph (F : RootedForest V) {v : V} (hv : v ∉ F.vertices) :
    (F.adjoin v hv).graph = F.graph := by
  sorry

/-- The graph of the forest as a simple graph on its actual vertex set. -/
def toGraph (F : RootedForest V) : SimpleGraph {v // v ∈ F.vertices} :=
  F.graph.induce (F.vertices : Set V)

end RootedForest

end Freezing1

open Lean in
run_cmd modifyEnv (·.setMainModule `Challenge.SameLaw)

/-! ## Uniform ordered pairs of distinct roots -/

namespace Freezing1

open MeasureTheory

section UniformRootPair

variable {V : Type*} [DecidableEq V]

variable [MeasurableSpace V] [MeasurableSingletonClass V]

/-- The uniform probability measure on the ordered pairs `(r, r')` of distinct elements of the finite set `s` (sampling without replacement, the order is retained). -/
noncomputable def uniformRootPair (s : Finset V) : Measure (V × V) :=
  Measure.uniformOfFinset s.offDiag

omit [DecidableEq V] in
/-- For a finite set with at least two elements, the law of the uniform ordered pair of distinct elements is a probability measure. -/
theorem uniformRootPair_isProbabilityMeasure (s : Finset V) (hs : 2 ≤ s.card) :
    IsProbabilityMeasure (uniformRootPair s) := by
  sorry

end UniformRootPair

end Freezing1

/-! ## The reverse growth/coalescent construction (Algorithm 2) -/

namespace Freezing1.Reverse

open MeasureTheory
open scoped ENNReal Classical

/-- Forests whose vertices are the active labels `a_j` (`Sum.inl j`) and the freezing labels (`Sum.inr j`, displayed as `j + 1`). -/
abbrev Forest := RootedForest (ℕ ⊕ ℕ)

/-- The forest `F^n_n` at the start of Algorithm 2: `S_n` isolated one-vertex trees labelled `a_1, ..., a_{S_n}` (`S_n = 0` gives the empty forest). -/
def initial (x : SignSequence) (n : ℕ) : Forest :=
  RootedForest.isolated ((Finset.range (activeCount x n).toNat).disjSum ∅)

end Freezing1.Reverse

namespace Freezing1.ReverseStamped

open MeasureTheory
open scoped ENNReal Classical

/-- A reverse forest together with the edge times: `edgeTime v` is the label (the reverse step index) of the parent edge of `v`, and `0` for a root. -/
structure Forest where
  forest : Reverse.Forest
  edgeTime : (ℕ ⊕ ℕ) → ℕ

/-- Every set of timestamped forests is measurable (discrete measurable space). -/
instance : MeasurableSpace Forest := ⊤

/-- The initial timestamped forest `F^n_n`: `S_n` isolated active vertices with no parent edge. -/
def initial (x : SignSequence) (n : ℕ) : Forest :=
  ⟨Reverse.initial x n, fun _ => 0⟩

/-- Merge the chosen ordered pair `(r(T_1), r(T_2))` of distinct roots at time `t`: the tree of `r(T_2)` is attached below `r(T_1)` by an edge labelled `t`, stored at `r(T_2)`. An invalid pair leaves the forest unchanged. -/
def joinChoice (F : Forest) (t : ℕ) (p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)) : Forest :=
  if h : p ∈ F.forest.roots.offDiag then
    ⟨F.forest.join p.1 p.2 (Finset.mem_offDiag.mp h).1
      (Finset.mem_offDiag.mp h).2.1 (Finset.mem_offDiag.mp h).2.2,
      Function.update F.edgeTime p.2 t⟩
  else F

/-- A valid merge stores the time `t` at the second chosen root and leaves the other edge times unchanged. -/
theorem joinChoice_edgeTime (F : Forest) (t : ℕ) {p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)}
    (hp : p ∈ F.forest.roots.offDiag) :
    (joinChoice F t p).edgeTime = Function.update F.edgeTime p.2 t := by
  sorry

/-- Insert the freezing label `inr i` (displayed as the label `i + 1`) as a new one-vertex tree with no parent edge (the case `X_{i+1} = -1`). -/
def insertLabel (F : Forest) (i : ℕ) : Forest :=
  if h : Sum.inr i ∈ F.forest.vertices then F
  else ⟨F.forest.adjoin (.inr i) h, Function.update F.edgeTime (.inr i) 0⟩

/-- One merge step at time `t`: with at least two trees, choose a uniform ordered pair of distinct roots and merge, otherwise do nothing. -/
noncomputable def joinLaw (F : Forest) (t : ℕ) : Measure Forest :=
  if 2 ≤ F.forest.roots.card then
    (uniformRootPair F.forest.roots).map (joinChoice F t)
  else Measure.dirac F

/-- One step of Algorithm 2 from `F^n_{i+1}` to `F^n_i`: read the sign `x (i+1)`; for `+1` merge two uniformly chosen roots (edge label `i+1`), for `-1` insert the one-vertex tree labelled `i + 1`. -/
noncomputable def transitionLaw (x : SignSequence) (i : ℕ) (F : Forest) : Measure Forest :=
  if x (i + 1) then joinLaw F (i + 1) else Measure.dirac (insertLabel F i)

/- Comparator note. The matcher of this recursion is identical to the one of `Forward.treeLaw`; in the development the two live in
different modules and therefore have distinct names (`Forward.treeLaw.match_1`, `ReverseStamped.lawAfter.match_1`). Lean
reuses a matcher with identical value inside one file, so we use `bootstrap.genMatcherCode` (only a code-generation
flag, the kernel constants are unchanged) to obtain a separate matcher with the name used by the development. -/
set_option bootstrap.genMatcherCode false in
/-- The law of the timestamped forest after `k` reverse steps of Algorithm 2 (started at `F^n_n`, then reading `x n, x (n-1), ...`). -/
noncomputable def lawAfter (x : SignSequence) (n : ℕ) : ℕ → Measure Forest
  | 0 => Measure.dirac (initial x n)
  | k + 1 => if k < n then
      (lawAfter x n k).bind (transitionLaw x (n - (k + 1)))
    else lawAfter x n k

/-- The law of the timestamped output `T^n = F^n_0` of Algorithm 2 (after all `n` reverse steps). -/
noncomputable def treeLaw (x : SignSequence) (n : ℕ) : Measure Forest := lawAfter x n n

/-- The attachment times: the indices `t` with `i < t ≤ n` and `x t = +1` (the labels of the edges created in steps `n, ..., i + 1`). -/
def attachmentTimes (x : SignSequence) (n i : ℕ) : Finset ℕ :=
  (Finset.Ioc i n).filter fun t => x t = true

/-- For `n ≤ τ`, almost surely the edge times are injective on the vertices of the reverse output and their set of values is `{0}` together with the attachment times: they are canonical vertex identifiers. -/
theorem treeLaw_canonical_ids (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ F ∂treeLaw x n,
      (∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
        F.edgeTime u = F.edgeTime v → u = v) ∧
      F.forest.vertices.image F.edgeTime = insert 0 (attachmentTimes x n 0) := by
  sorry

/-- For `n ≤ τ`, the underlying forest of the reverse output is almost surely a finite tree in the sense of Mathlib. -/
theorem treeLaw_forest_isTree (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ F ∂treeLaw x n, F.forest.toGraph.IsTree := by
  sorry

end Freezing1.ReverseStamped

/-! ## The common observable and the target -/

namespace Freezing1.CanonicalTree

open MeasureTheory
open scoped Classical

/-- The common observable of both constructions: the vertex identifiers, the graph on `ℕ`, the active identifiers, and the pairs (identifier, freezing time) of frozen vertices. -/
structure Observable where
  vertices : Finset ℕ
  graph : SimpleGraph ℕ
  active : Finset ℕ
  frozen : Finset (ℕ × ℕ)

/-- Every set of observables is measurable (discrete measurable space). -/
instance : MeasurableSpace Observable := ⊤

/-- The label of the edge between two canonical identifiers: the larger endpoint identifier. -/
def edgeTime (u v : ℕ) : ℕ := max u v

/-- All pairs (coordinate of a vertex, freezing time) over the vertices of `s` that are frozen. -/
def frozenPairs {V : Type*} [DecidableEq V] (s : Finset V)
    (coordinate : V → ℕ) (label : V → Option ℕ) : Finset (ℕ × ℕ) :=
  s.biUnion fun v => (label v).toFinset.image fun t => (coordinate v, t)

/-- Transport a graph on `V` to the canonical coordinates in `ℕ`: two distinct coordinates are adjacent iff some adjacent vertices carry them. -/
def transportGraph {V : Type*} [DecidableEq V] (s : Finset V)
    (coordinate : V → ℕ) (G : SimpleGraph V) : SimpleGraph ℕ where
  Adj a b := a ≠ b ∧ ∃ u ∈ s, ∃ v ∈ s,
    coordinate u = a ∧ coordinate v = b ∧ G.Adj u v
  symm := by
    constructor
    rintro a b ⟨hne, u, hu, v, hv, hcu, hcv, hadj⟩
    exact ⟨hne.symm, v, hv, u, hu, hcv, hcu, hadj.symm⟩
  loopless := ⟨by simp⟩

/-- Injective coordinates preserve and reflect every adjacency. -/
theorem transportGraph_adj_iff {V : Type*} [DecidableEq V] {s : Finset V}
    {coordinate : V → ℕ} {G : SimpleGraph V}
    (hinj : ∀ u ∈ s, ∀ v ∈ s, coordinate u = coordinate v → u = v)
    {u v : V} (hu : u ∈ s) (hv : v ∈ s) :
    (transportGraph s coordinate G).Adj (coordinate u) (coordinate v) ↔ G.Adj u v := by
  sorry

/-- The observable of a forward state: its vertices, graph and active vertices, and its frozen vertices with their freezing times (the identifiers are the birth times). -/
def forward (s : Forward.State) : Observable where
  vertices := s.vertices
  graph := s.graph
  active := s.active
  frozen := frozenPairs s.vertices id s.frozenAt

/-- The displayed label of a reverse vertex: the active labels `inl j` all display the same unlabeled active status `none`, and the frozen label `inr j` displays the freezing time `j + 1`. -/
def reverseLabel : (ℕ ⊕ ℕ) → Option ℕ
  | .inl _ => none
  | .inr j => some (j + 1)

/-- The observable of a timestamped reverse forest: the canonical identifier of a vertex is its parent-edge time (`0` for the root); the active labels `a_j` are forgotten, the frozen labels are kept. -/
def reverse (F : ReverseStamped.Forest) : Observable where
  vertices := F.forest.vertices.image F.edgeTime
  graph := transportGraph F.forest.vertices F.edgeTime F.forest.graph
  active := (F.forest.vertices.filter fun v => reverseLabel v = none).image F.edgeTime
  frozen := frozenPairs F.forest.vertices F.edgeTime reverseLabel

/-- The frozen pairs of the forward observable are exactly the freezing labels of the vertices of the state. -/
theorem forward_frozen_iff {s : Forward.State} {v t : ℕ} :
    (v, t) ∈ (forward s).frozen ↔ v ∈ s.vertices ∧ s.frozenAt v = some t := by
  sorry

/-- With injective edge times, the frozen pair at the identifier of `v` has the label displayed by `v`. -/
theorem reverse_frozen_iff {F : ReverseStamped.Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v)
    {v : ℕ ⊕ ℕ} (hv : v ∈ F.forest.vertices) {t : ℕ} :
    (F.edgeTime v, t) ∈ (reverse F).frozen ↔ reverseLabel v = some t := by
  sorry

/-- With injective edge times, the observable graph is the forest graph in the canonical coordinates. -/
theorem reverse_adj_iff {F : ReverseStamped.Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v)
    {u v : ℕ ⊕ ℕ} (hu : u ∈ F.forest.vertices) (hv : v ∈ F.forest.vertices) :
    (reverse F).graph.Adj (F.edgeTime u) (F.edgeTime v) ↔ F.forest.graph.Adj u v := by
  sorry

/-- Forward parent edges keep exactly their attachment timestamp: the label of the edge between a vertex and its parent is the larger endpoint identifier. -/
theorem forward_edge_time {n : ℕ} {s : Forward.State} (hs : Forward.ValidAt n s)
    {v : ℕ} (hv : v ∈ s.vertices) (hn : v ≠ 0) :
    edgeTime (s.parent v) v = v := by
  sorry

/-- The law of the forward tree `T_n` as an observable. -/
noncomputable def forwardLaw (x : SignSequence) (n : ℕ) : Measure Observable :=
  (Forward.treeLaw x n).map forward

/-- The law of the reverse tree `T^n` (active labels erased) as an observable. -/
noncomputable def reverseLaw (x : SignSequence) (n : ℕ) : Measure Observable :=
  (ReverseStamped.treeLaw x n).map reverse

/-- The law of the forward observable is a probability measure. -/
theorem forwardLaw_probability (x : SignSequence) (n : ℕ) :
    IsProbabilityMeasure (forwardLaw x n) := by
  sorry

/-- The law of the reverse observable is a probability measure. -/
theorem reverseLaw_probability (x : SignSequence) (n : ℕ) :
    IsProbabilityMeasure (reverseLaw x n) := by
  sorry

/-- For `n ≤ τ`, almost surely the forward tree has exactly the canonical identifier set `{0}` together with the attachment times. -/
theorem forwardLaw_vertices (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ T ∂forwardLaw x n,
      T.vertices = insert 0 (ReverseStamped.attachmentTimes x n 0) := by
  sorry

/-- For `n ≤ τ`, almost surely the reverse tree has exactly the canonical identifier set `{0}` together with the attachment times. -/
theorem reverseLaw_vertices (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ T ∂reverseLaw x n,
      T.vertices = insert 0 (ReverseStamped.attachmentTimes x n 0) := by
  sorry

/-- For `n ≤ τ`, the observable graph of the reverse tree is almost surely isomorphic to the forest graph itself. -/
theorem treeLaw_reverse_graph_isomorphic (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ F ∂ReverseStamped.treeLaw x n,
      Nonempty (F.forest.toGraph ≃g (reverse F).graph.induce ((reverse F).vertices : Set ℕ)) := by
  sorry

end Freezing1.CanonicalTree

namespace Freezing1.CanonicalTree

open MeasureTheory
open scoped ENNReal

/-- **Theorem `thm:samelaw`.** For every schedule `x` and every `n ≤ τ(x)`, the tree `T_n` of Algorithm 1 and the tree `T^n` of Algorithm 2 with its active labels erased have the same distribution (as observables: canonical identifiers, graph, active identifiers, and frozen labels with their freezing times). -/
theorem construction_laws_eq (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) : forwardLaw x n = reverseLaw x n := by
  sorry

end Freezing1.CanonicalTree
