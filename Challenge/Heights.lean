module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Challenge: heights of uniform attachment trees with freezing (Theorems `thm:height`, `thm:lineaire`)

Source: *Uniform attachment with freezing*, `attachement-uniforme-1-final.tex`. This interface covers
the height results of the Introduction: Theorem `thm:height` (I), (II), (III) and Theorem
`thm:lineaire` (I), (II) (height and distance) and (III). Every definition used by these statements is
given below with its ordinary mathematical meaning; the theorem bodies are deliberately left as holes.
It does not cover the local-limit, same-law or SIR statements, and it is not a statement about the
whole manuscript. The hypothesis `hτ : ∀ n, n < extinctionTime (x n)` is the manuscript's standing
assumption `τ(𝐱ⁿ) > n` (it forces `S_i ≥ 1` for `i ≤ n`, so the set of active vertices is never empty);
the real-valued `limsup`/`liminf` of the linear-regime hypotheses are taken of bounded sequences.
-/

@[expose] public section

namespace Freezing1

/-! ## Schedules, the walk and the extinction time -/

/-- An attachment/freezing schedule; index zero is unused. The value `true` at index `i + 1` is the
sign `+1` (attachment at step `i + 1`), `false` is `-1` (freezing). -/
abbrev SignSequence := ℕ → Bool

/-- The integer walk `S_n = 1 + ∑_{i=1}^n X_i` of the Introduction: the number of active vertices
of the tree after `n` steps. It is not stopped at its first zero. -/
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

/-- The deterministic height scale `h_n^+ = ∑_{i=1}^n 1_{X_i = +1} / S_i` from the Introduction. -/
noncomputable def heightScale (x : SignSequence) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, if x (i + 1) then 1 / (activeCount x (i + 1) : ℝ) else 0

end Freezing1

/-! ## Algorithm 1: the random tree with freezing -/

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

/-- Freeze the chosen vertex and record its displayed label. -/
def freeze (s : State) (t v : ℕ) : State where
  vertices := s.vertices
  active := s.active.erase v
  graph := s.graph
  parent := s.parent
  height := s.height
  frozenAt := Function.update s.frozenAt v (some t)

/-- Algorithm 1's transition. An invalid choice (a vertex that is not active) leaves the state
unchanged; this branch is never reached under `transitionLaw`, which only chooses active vertices. -/
def step (s : State) (t : ℕ) (sign : Bool) (v : ℕ) : State :=
  if v ∈ s.active then if sign then attach s t v else freeze s t v else s

open MeasureTheory
open scoped ENNReal Classical

instance : MeasurableSpace State := ⊤

/-- One uniform choice, followed by the deterministic Algorithm 1 transition. -/
noncomputable def transitionLaw (s : State) (t : ℕ) (sign : Bool) : Measure State :=
  if s.active.Nonempty then
    (Measure.uniformOfFinset s.active).map (fun v => step s t sign v)
  else Measure.dirac s

/-- The law of the forward random tree at time `n`. -/
noncomputable def treeLaw (x : SignSequence) : ℕ → Measure State
  | 0 => Measure.dirac initial
  | n + 1 => (treeLaw x n).bind (fun s => transitionLaw s (n + 1) (x (n + 1)))

end Freezing1.Forward

namespace Freezing1.Forward

open MeasureTheory
open scoped BigOperators ENNReal ProbabilityTheory

/-- Conditional law of the height of a uniformly chosen active vertex of a state; the value zero is
only used for states without active vertex. -/
noncomputable def activeHeightKernel : ProbabilityTheory.Kernel State ℕ where
  toFun s := if s.active.Nonempty then (Measure.uniformOfFinset s.active).map s.height
    else Measure.dirac 0
  measurable' := measurable_from_top

/-- The height law for a vertex sampled uniformly among the active vertices of the random tree
`T_n`. -/
noncomputable def uniformActiveHeightLaw (x : SignSequence) (n : ℕ) : Measure ℕ :=
  (treeLaw x n).bind activeHeightKernel

open ProbabilityTheory

/-- The height of a tree: the largest height of one of its vertices. -/
def treeHeight (s : State) : ℕ := s.vertices.sup s.height

/-- A vertex sampled conditionally uniformly from all vertices (active and frozen) of a tree. The
empty fallback is never used under the tree law, which always contains the root. -/
noncomputable def vertexHeightKernel : Kernel State ℕ where
  toFun s := if s.vertices.Nonempty then (Measure.uniformOfFinset s.vertices).map s.height
    else Measure.dirac 0
  measurable' := measurable_from_top

/-- The law of the height of a conditionally uniform vertex of the random tree `T_n`. -/
noncomputable def uniformHeightLaw (x : SignSequence) (n : ℕ) : Measure ℕ :=
  (treeLaw x n).bind vertexHeightKernel

end Freezing1.Forward

namespace Freezing1

open Filter
open scoped Topology NNReal

set_option backward.isDefEq.respectTransparency false

/-- The indices `A_n ≤ i ≤ ε n` of the first uniform linear-regime condition. -/
noncomputable def nearOriginIndices (A : ℕ → ℝ) (ε : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun i => A n ≤ (i : ℝ) ∧ (i : ℝ) ≤ ε * n

/-- `max_{A_n ≤ i ≤ ε n} |S_i^n / i - c|` (a nonnegative supremum; zero on an empty index set). -/
noncomputable def nearOriginMaximum (x : ℕ → SignSequence) (A : ℕ → ℝ)
    (c ε : ℝ) (n : ℕ) : ℝ :=
  (((nearOriginIndices A ε n).sup
    (fun i => (⟨|(activeCount (x n) i : ℝ) / i - c|, abs_nonneg _⟩ : ℝ≥0)) : ℝ≥0) : ℝ)

/-- The first condition of the linear regime (`eq:assumptions`):
`lim_{ε → 0} limsup_n max_{A_n ≤ i ≤ ε n} |S_i^n / i - c| = 0`.
The real sequences involved are bounded (each term lies in `[0, 2 + |c|]` because `A n > 0` keeps
`i = 0` out of the maximum and `|S_i| ≤ i + 1`), so `limsup` is the genuine limit superior. -/
def NearOriginLimsup (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ) : Prop :=
  Tendsto (fun ε : ℝ => limsup (nearOriginMaximum x A c ε) atTop)
    (𝓝[>] 0) (𝓝 0)

/-- The indices `ε n ≤ i ≤ n` of the second uniform linear-regime condition, always including `n`. -/
noncomputable def bulkIndices (ε : ℝ) (n : ℕ) : Finset ℕ :=
  insert n ((Finset.range (n + 1)).filter fun i => ε * n ≤ (i : ℝ))

/-- `min_{ε n ≤ i ≤ n} S_i^n / n`. -/
noncomputable def bulkMinimum (x : ℕ → SignSequence) (ε : ℝ) (n : ℕ) : ℝ :=
  (bulkIndices ε n).inf' (Finset.insert_nonempty _ _)
    (fun i => (activeCount (x n) i : ℝ) / n)

/-- The second condition of the linear regime (`eq:assumptions`): for every `ε ∈ (0,1)`,
`liminf_n min_{ε n ≤ i ≤ n} S_i^n / n > 0`. The sequences are bounded in `[-2, 2]`, so `liminf`
is the genuine limit inferior. -/
def BulkLiminf (x : ℕ → SignSequence) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → 0 < liminf (bulkMinimum x ε) atTop

end Freezing1

namespace Freezing1.CanonicalTree

open MeasureTheory
open scoped Classical ENNReal

/-- Two conditionally independent uniform vertices `(u, v)` of a tree (the diagonal `u = v` is not
excluded), observed through their heights and graph distance `(h(u), h(v), d(u,v))`. The vertex
set always contains the root `0`, so the uniform law is a probability measure. -/
noncomputable def forwardPairKernel (s : Forward.State) : Measure (ℕ × ℕ × ℕ) :=
  (Measure.uniformOfFinset s.vertices).bind fun u =>
    (Measure.uniformOfFinset s.vertices).map fun v => (s.height u, s.height v, s.graph.dist u v)

/-- The law of the heights and distance of two conditionally independent uniform vertices of
the random tree `T_n`. -/
noncomputable def forwardPairDataLaw (x : SignSequence) (n : ℕ) : Measure (ℕ × ℕ × ℕ) :=
  (Forward.treeLaw x n).bind forwardPairKernel

end Freezing1.CanonicalTree

namespace Freezing1

open Set

/-- The function defining the height factor, strictly increasing on `[1, ∞)`. -/
noncomputable def heightRate (x : ℝ) : ℝ := x * Real.log x - x

theorem heightRate_eq (x : ℝ) : heightRate x = x * (Real.log x - 1) := by
  unfold heightRate
  ring

theorem continuous_heightRate : Continuous heightRate :=
  Real.continuous_mul_log.sub continuous_id

theorem hasDerivAt_heightRate {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt heightRate (Real.log x) x := by
  convert (Real.hasDerivAt_mul_log hx).fun_sub (hasDerivAt_id' x) using 1
  · rfl
  · ring

theorem strictMonoOn_heightRate : StrictMonoOn heightRate (Ici 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici _) continuous_heightRate.continuousOn ?_
  intro x hx
  have hx1 : 1 < x := by simpa using hx
  rw [(hasDerivAt_heightRate (by linarith)).deriv]
  exact Real.log_pos hx1

@[simp] theorem heightRate_one : heightRate 1 = -1 := by simp [heightRate]

@[simp] theorem heightRate_exp_one : heightRate (Real.exp 1) = 0 := by
  simp [heightRate]

/-- Existence and uniqueness of the number specified in Theorem `thm:lineaire` (III).
The quantifier ranges over all real numbers strictly larger than one. -/
theorem linearHeightFactor_existsUnique {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∃! x : ℝ, 1 < x ∧ x * (Real.log x - 1) = (c - 1) / (c + 1) := by
  have hc : 0 < c + 1 := by linarith
  have htarget : (c - 1) / (c + 1) ∈ Icc (heightRate 1) (heightRate (Real.exp 1)) := by
    simp only [heightRate_one, heightRate_exp_one, mem_Icc]
    constructor
    · rw [le_div_iff₀ hc]
      linarith
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith) hc.le
  have he : (1 : ℝ) ≤ Real.exp 1 := (Real.one_lt_exp_iff.mpr zero_lt_one).le
  obtain ⟨x, hx, hxeq⟩ := intermediate_value_Icc he
    continuous_heightRate.continuousOn htarget
  have hx1 : 1 < x := by
    refine lt_of_le_of_ne hx.1 ?_
    intro h
    have ht : -1 < (c - 1) / (c + 1) := by
      rw [lt_div_iff₀ hc]
      linarith
    have : heightRate x = -1 := by rw [← h, heightRate_one]
    linarith
  refine ⟨x, ⟨hx1, by simpa [heightRate_eq] using hxeq⟩, ?_⟩
  intro y hy
  apply strictMonoOn_heightRate.injOn hy.1.le hx1.le
  rw [heightRate_eq, heightRate_eq, hy.2]
  simpa only [heightRate_eq] using hxeq.symm

/-- The admissible linear growth constants of Theorem `thm:lineaire`: `0 < c ≤ 1`. -/
abbrev LinearRegimeParameter := Ioc (0 : ℝ) 1

/-- The height factor `f(c)` of Theorem `thm:lineaire` (III). Its domain records exactly `0 < c ≤ 1`.
The choice is justified by `linearHeightFactor_existsUnique`, and uniqueness
ensures that all later statements are independent of that choice. -/
noncomputable def linearHeightFactor (c : LinearRegimeParameter) : ℝ :=
  Classical.choose (linearHeightFactor_existsUnique c.property.1 c.property.2).exists

/-- `f(c)` is the root larger than one of `f (log f - 1) = (c - 1) / (c + 1)`. -/
theorem linearHeightFactor_spec (c : LinearRegimeParameter) :
    1 < linearHeightFactor c ∧
      linearHeightFactor c * (Real.log (linearHeightFactor c) - 1) =
        ((c : ℝ) - 1) / ((c : ℝ) + 1) :=
  Classical.choose_spec (linearHeightFactor_existsUnique c.property.1 c.property.2).exists

/-! ## The height theorems -/

open MeasureTheory Filter
open scoped ENNReal Topology

/-- Theorem `thm:height` (I): the height of a uniformly chosen active vertex, divided by `h_n^+`,
converges to one in every real `Lᵖ`, `p ≥ 1`. The rows `x n` of the triangular array satisfy
`τ > n`. -/
theorem uniform_active_height_tendsto_Lp (x : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n)) {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm (fun k : ℕ => (k : ℝ) / heightScale (x n) n - 1)
      (ENNReal.ofReal p) (Forward.uniformActiveHeightLaw (x n) n)) atTop (𝓝 0) := by
  sorry

/-- Theorem `thm:height` (II): with probability tending to one, the maximum height divided by
`h_n^+` lies in `[1 - ε, e + ε]`, for every `0 < ε < 1`. -/
theorem maximum_height_window_tendsto_one (x : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n)) {ε : ℝ}
    (hε : 0 < ε) (_hε1 : ε < 1) :
    Tendsto (fun n => (Forward.treeLaw (x n) n).real
      {s | 1 - ε ≤ (Forward.treeHeight s : ℝ) / heightScale (x n) n ∧
        (Forward.treeHeight s : ℝ) / heightScale (x n) n ≤ Real.exp 1 + ε}) atTop (𝓝 1) := by
  sorry

/-- Theorem `thm:height` (III): if `log n = o(h_n^+)`, the maximum height divided by `h_n^+` tends to
one in every real `Lᵖ`, `p ≥ 1`. -/
theorem maximum_height_tendsto_Lp (x : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (x n) n) atTop (𝓝 0))
    {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm
      (fun s => (Forward.treeHeight s : ℝ) / heightScale (x n) n - 1)
      (ENNReal.ofReal p) (Forward.treeLaw (x n) n)) atTop (𝓝 0) := by
  sorry

/-- Theorem `thm:lineaire` (I): under the two linear-regime conditions, `h_n^+ / log n` converges to
`(c + 1) / (2 c)`. -/
theorem linear_heightScale_tendsto
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x) :
    Tendsto (fun n : ℕ => heightScale (x n) n / Real.log (n : ℝ))
      atTop (𝓝 ((c + 1) / (2 * c))) := by
  sorry

/-- Theorem `thm:lineaire` (II), height: a conditionally uniform vertex of the forward tree has height
divided by `log n` converging in every real `Lᵖ`, `p ≥ 1`, to `(c + 1) / (2 c)`. -/
theorem linear_uniform_height_tendsto_Lp
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x)
    {r : ℝ} (hr : 1 ≤ r) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun k : ℕ => (k : ℝ) / Real.log (n : ℝ) - (c + 1) / (2 * c))
      (ENNReal.ofReal r) (Forward.uniformHeightLaw (x n) n)) atTop (𝓝 0) := by
  sorry

/-- Theorem `thm:lineaire` (II), distance: two conditionally independent uniform vertices of the
forward tree (equality allowed) have distance divided by `log n` converging in every real `Lᵖ`,
`p ≥ 1`, to `(c + 1) / c`. -/
theorem linear_uniform_distance_tendsto_Lp
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x)
    {r : ℝ} (hr : 1 ≤ r) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun z : ℕ × ℕ × ℕ => (z.2.2 : ℝ) / Real.log (n : ℝ) - (c + 1) / c)
      (ENNReal.ofReal r) (CanonicalTree.forwardPairDataLaw (x n) n)) atTop (𝓝 0) := by
  sorry

/-- Theorem `thm:lineaire` (III): the maximum height divided by `log n` converges in probability to
`((c + 1) / (2 c)) f(c)`, where `f(c) > 1` is the root of `f (log f - 1) = (c - 1) / (c + 1)`. -/
theorem linear_maximum_deviation_tendsto_zero (c : LinearRegimeParameter)
    (x : ℕ → SignSequence) (A : ℕ → ℝ)
    (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A (c : ℝ)) (hbulk : BulkLiminf x)
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => (Forward.treeLaw (x n) n)
      {s | η ≤ |(Forward.treeHeight s : ℝ) / Real.log (n : ℝ) -
        (((c : ℝ) + 1) / (2 * (c : ℝ))) * linearHeightFactor c|})
      atTop (𝓝 0) := by
  sorry

end Freezing1
