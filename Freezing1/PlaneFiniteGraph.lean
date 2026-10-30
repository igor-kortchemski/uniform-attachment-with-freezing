module

public import Freezing1.PlaneStateValidity
public import Freezing1.FiniteUniformPairs
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The actual graph of a finite plane tree

Edges join a present address to a present one-child extension. Conditional
pair sampling uses two independent uniform vertices of that finite graph,
including the diagonal.
-/

@[expose] public section

namespace Freezing1.PlaneForward

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

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
