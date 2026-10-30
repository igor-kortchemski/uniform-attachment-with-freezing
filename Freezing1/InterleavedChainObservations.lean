module

public import Freezing1.InterleavedChainCylinders
public import Freezing1.CountableMarkovObservations

/-!
# Cylinder completion along the actual interleaved history

The two observed lists are extracted from the genuine triple-valued path.
Their last entries recover its two current states. The product-completion
identity consequently gives the exact product expectation at every global
time, despite the scheduler depending on both current states.
-/

@[expose] public section

namespace Freezing1.InterleavedChain

open MeasureTheory ProbabilityTheory CountableMarkovChain
open scoped ENNReal Classical

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

def updateObservation (o : List E × List E) (s : State E) : List E × List E :=
  if s.2.2 then (o.1 ++ [s.1], o.2) else (o.1, o.2 ++ [s.2.1])

def observations (H : ℕ → State E) (n : ℕ) : List E × List E :=
  accumulate ([], []) updateObservation H n

def MovesOnlySelected (s t : State E) : Prop :=
  if t.2.2 then t.2.1 = s.2.1 else t.1 = s.1

theorem transition_movesOnlySelected (α : Kernel E E) (κ : E × E → unitInterval)
    (s : State E) : ∀ᵐ t ∂transition α κ s, MovesOnlySelected s t := by
  rw [ae_iff]
  change transition α κ s {t | ¬MovesOnlySelected s t} = 0
  rw [transition_apply]
  simp [MovesOnlySelected]

theorem fullLaw_movesOnlySelected (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (s : State E) :
    ∀ᵐ H ∂InterleavedChain.fullLaw α κ s,
      ∀ n, MovesOnlySelected (H n) (H (n + 1)) :=
  CountableMarkovChain.fullLaw_steps (transition α κ) s MovesOnlySelected
    (transition_movesOnlySelected α κ)

omit [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E] in
/-- No coordinate changes between its own selected updates. -/
theorem observations_last (H : ℕ → State E)
    (h : ∀ n, MovesOnlySelected (H n) (H (n + 1))) (n : ℕ) :
    (observations H n).1.getLastD (H 0).1 = (H n).1 ∧
      (observations H n).2.getLastD (H 0).2.1 = (H n).2.1 := by
  induction n with
  | zero => simp only [observations, accumulate_zero, List.getLastD_nil, and_self]
  | succ n ih =>
    have hs := h n
    change (updateObservation (observations H n) (H (n + 1))).1.getLastD _ = _ ∧
      (updateObservation (observations H n) (H (n + 1))).2.getLastD _ = _
    cases he : (H (n + 1)).2.2 with
    | false =>
      have hs' : (H (n + 1)).1 = (H n).1 := by simpa only [MovesOnlySelected, he, Bool.false_eq_true, ite_false] using hs
      simpa only [updateObservation, he, Bool.false_eq_true, ite_false, List.getLastD_concat] using
        And.intro (ih.1.trans hs'.symm) (rfl : (H (n + 1)).2.1 = (H (n + 1)).2.1)
    | true =>
      have hs' : (H (n + 1)).2.1 = (H n).2.1 := by simpa only [MovesOnlySelected, he, ite_true] using hs
      simpa only [updateObservation, he, ite_true, List.getLastD_concat] using
        And.intro (rfl : (H (n + 1)).1 = (H (n + 1)).1) (ih.2.trans hs'.symm)

theorem map_transition_observations (α : Kernel E E) (κ : E × E → unitInterval)
    (x y : E) (o : List E × List E) (s : State E)
    (hx : o.1.getLastD x = s.1) (hy : o.2.getLastD y = s.2.1) :
    (transition α κ s).map (updateObservation o) = observationTransition α κ x y o := by
  simp only [transition, Kernel.coe_mk, Measure.map_add _ _ (measurable_of_countable _),
    Measure.map_smul _ (measurable_of_countable _).aemeasurable, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  simp only [Function.comp_def, updateObservation, ite_true, Bool.false_eq_true, ite_false,
    observationTransition, Kernel.coe_mk, hx, hy]

/-- The product of the two requested cylinder probabilities is the exact
expectation of their completion product along the actual interleaved path. -/
theorem lintegral_pairCompletion_observations (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (x y : E) (i : Bool) (u v : List E) (n : ℕ) :
    ∫⁻ H, pairCompletion α x y u v (observations H n)
      ∂InterleavedChain.fullLaw α κ (x, y, i) =
      wordProbability α x u * wordProbability α y v := by
  have hh : ∀ k, ∀ᵐ H ∂CountableMarkovChain.fullLaw (transition α κ) (x, y, i),
      ∫⁻ z, pairCompletion α x y u v (updateObservation (observations H k) z)
          ∂transition α κ (H k) = pairCompletion α x y u v (observations H k) := by
    intro k
    filter_upwards [CountableMarkovChain.fullLaw_initial (transition α κ) (x, y, i),
      fullLaw_movesOnlySelected α κ (x, y, i)] with H hzero hsteps
    have hlast := observations_last H hsteps k
    simp only [hzero] at hlast
    rw [← lintegral_map (measurable_of_countable _) (measurable_of_countable _),
      map_transition_observations α κ x y (observations H k) (H k) hlast.1 hlast.2]
    exact lintegral_pairCompletion_transition α κ x y u v _
  simpa only [observations, fullLaw, pairCompletion, completion_nil_observed] using
    CountableMarkovChain.lintegral_accumulate_of_harmonic (transition α κ) (x, y, i)
      ([], []) updateObservation (fun o _ => pairCompletion α x y u v o) hh n

end Freezing1.InterleavedChain
