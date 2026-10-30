module

public import Freezing1.InterleavedChainKernel
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Completion probabilities of finite Markov cylinders

A partially observed word is assigned its exact remaining cylinder
probability. Appending one genuine Markov step preserves the expectation.
For two words the product is harmonic under the actual adaptive interleaving
kernel: only one word advances, so no independence is presumed.
-/

@[expose] public section

namespace Freezing1.InterleavedChain

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

/-- Finite words over a countable state space carry the discrete sigma-algebra. -/
instance wordMeasurableSpace (E : Type*) [Countable E] : MeasurableSpace (List E) := ⊤

instance wordMeasurableSingletonClass (E : Type*) [Countable E] :
    MeasurableSingletonClass (List E) := ⟨fun _ => trivial⟩

/-- Exact probability of a prescribed finite future word. -/
noncomputable def wordProbability (α : Kernel E E) : E → List E → ℝ≥0∞
  | _, [] => 1
  | x, y :: ys => α x {y} * wordProbability α y ys

/-- The word already observed is checked against the requested cylinder;
the still unobserved suffix contributes its actual Markov probability. -/
noncomputable def completion (α : Kernel E E) : E → List E → List E → ℝ≥0∞
  | _, _, [] => 1
  | x, [], y :: ys => wordProbability α x (y :: ys)
  | _, z :: zs, y :: ys => if z = y then completion α z zs ys else 0

omit [MeasurableSingletonClass E] [Countable E] in
@[simp] theorem completion_nil_target (α : Kernel E E) (x : E) (zs : List E) :
    completion α x zs [] = 1 := by cases zs <;> rfl

omit [MeasurableSingletonClass E] [Countable E] in
@[simp] theorem completion_nil_observed (α : Kernel E E) (x : E) (ys : List E) :
    completion α x [] ys = wordProbability α x ys := by cases ys <;> rfl

omit [MeasurableSingletonClass E] [Countable E] in
theorem wordProbability_le_one (α : Kernel E E) [IsMarkovKernel α]
    (x : E) (ys : List E) : wordProbability α x ys ≤ 1 := by
  induction ys generalizing x with
  | nil => rfl
  | cons y ys ih =>
    simpa only [wordProbability, one_mul] using mul_le_mul' (prob_le_one : α x {y} ≤ 1) (ih y)

omit [MeasurableSingletonClass E] [Countable E] in
theorem completion_le_one (α : Kernel E E) [IsMarkovKernel α]
    (x : E) (zs ys : List E) : completion α x zs ys ≤ 1 := by
  induction zs generalizing x ys with
  | nil => simpa only [completion_nil_observed] using wordProbability_le_one α x ys
  | cons z zs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      simp only [completion]
      split_ifs
      · exact ih z ys
      · exact bot_le

omit [Countable E] in
/-- The elementary one-coordinate harmonic identity, including an already
completed target word and a previously failed match. -/
theorem lintegral_completion_append (α : Kernel E E) [IsMarkovKernel α]
    (x : E) (zs ys : List E) :
    ∫⁻ z, completion α x (zs ++ [z]) ys ∂α (zs.getLastD x) =
      completion α x zs ys := by
  induction zs generalizing x ys with
  | nil =>
    cases ys with
    | nil => simp
    | cons y ys =>
      have he : (fun z => completion α x [z] (y :: ys)) =
          ({y} : Set E).indicator (fun _ => wordProbability α y ys) := by
        funext z
        by_cases hz : z = y
        · subst z
          simp [completion]
        · simp [completion, hz]
      simpa only [List.nil_append, List.getLastD_nil, he, completion_nil_observed,
        wordProbability, mul_comm] using
        (lintegral_indicator_const (measurableSet_singleton y)
          (wordProbability α y ys) (μ := α x))
  | cons z zs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      by_cases hzy : z = y
      · subst z
        simpa only [List.cons_append, List.getLastD_cons, completion, ite_true] using ih y ys
      · simp [List.cons_append, completion, hzy]

/-- Product completion evaluated at the pair of observed words. -/
noncomputable def pairCompletion (α : Kernel E E) (x y : E)
    (targetLeft targetRight : List E) (observed : List E × List E) : ℝ≥0∞ :=
  completion α x observed.1 targetLeft * completion α y observed.2 targetRight

/-- The true kernel of the two growing lists of observations. It uses the
current last states to choose a side, then appends one genuine Markov step. -/
noncomputable def observationTransition (α : Kernel E E) (κ : E × E → unitInterval)
    (x y : E) : Kernel (List E × List E) (List E × List E) where
  toFun o :=
    unitInterval.toNNReal (κ (o.1.getLastD x, o.2.getLastD y)) •
      (α (o.1.getLastD x)).map (fun z => (o.1 ++ [z], o.2)) +
    unitInterval.toNNReal (unitInterval.symm (κ (o.1.getLastD x, o.2.getLastD y))) •
      (α (o.2.getLastD y)).map (fun z => (o.1, o.2 ++ [z]))
  measurable' := measurable_of_countable _

instance observationTransition_markov (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (x y : E) :
    IsMarkovKernel (observationTransition α κ x y) := by
  constructor
  intro o
  constructor
  change (unitInterval.toNNReal (κ (o.1.getLastD x, o.2.getLastD y)) •
      (α (o.1.getLastD x)).map (fun z => (o.1 ++ [z], o.2)) +
    unitInterval.toNNReal (unitInterval.symm (κ (o.1.getLastD x, o.2.getLastD y))) •
      (α (o.2.getLastD y)).map (fun z => (o.1, o.2 ++ [z]))) Set.univ = 1
  simp

/-- A product of cylinder-completion probabilities is harmonic for every
adaptive scheduler κ. This replaces the paper's asynchronous conditioning
step with an identity for the actual transition measure. -/
theorem lintegral_pairCompletion_transition (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (x y : E) (u v : List E) (o : List E × List E) :
    ∫⁻ q, pairCompletion α x y u v q ∂observationTransition α κ x y o =
      pairCompletion α x y u v o := by
  simp only [observationTransition, Kernel.coe_mk, lintegral_add_measure,
    lintegral_smul_measure]
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  simp only [pairCompletion]
  rw [lintegral_mul_const _ (measurable_of_countable _),
    lintegral_const_mul _ (measurable_of_countable _),
    lintegral_completion_append, lintegral_completion_append]
  rw [← add_smul]
  simp

end Freezing1.InterleavedChain
