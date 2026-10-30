module

public import Freezing1.InterleavedChainLaw
public import Freezing1.CountableMarkovCylinders
public import Freezing1.CountablePathLaw
public import Mathlib.Probability.HasLaw

/-!
# L06: the two extracted chains have the independent Markov product law

The source's non-starvation assumptions are the only scheduling assumptions.
The result concerns the complete measurable extracted paths, with the exact
fallback convention at an absorbing coordinate.
-/

@[expose] public section

namespace Freezing1.InterleavedChain

open MeasureTheory ProbabilityTheory CountableMarkovChain CountablePathLaw
open scoped ENNReal Classical

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

def pathPairTail (p : (ℕ → E) × (ℕ → E)) : (ℕ → E) × (ℕ → E) :=
  (fun n => p.1 (n + 1), fun n => p.2 (n + 1))

def pathPairPrepend (x y : E) (p : (ℕ → E) × (ℕ → E)) : (ℕ → E) × (ℕ → E) :=
  (fun n => n.casesOn x p.1, fun n => n.casesOn y p.2)

omit [MeasurableSingletonClass E] [Countable E] in
theorem measurable_pathPairTail : Measurable (pathPairTail (E := E)) := by
  unfold pathPairTail
  fun_prop

omit [MeasurableSingletonClass E] [Countable E] in
theorem measurable_pathPairPrepend (x y : E) : Measurable (pathPairPrepend x y) := by
  unfold pathPairPrepend
  apply Measurable.prodMk <;> apply Measurable.of_eval <;> intro n <;>
    cases n <;> dsimp <;> fun_prop

omit [MeasurableSingletonClass E] [Countable E] in
theorem map_tail_prepend (μ : Measure ((ℕ → E) × (ℕ → E))) (x y : E)
    (h : ∀ᵐ p ∂μ, p.1 0 = x ∧ p.2 0 = y) :
    (μ.map pathPairTail).map (pathPairPrepend x y) = μ := by
  rw [Measure.map_map (measurable_pathPairPrepend x y) measurable_pathPairTail]
  have he : pathPairPrepend x y ∘ pathPairTail =ᵐ[μ] id := by
    filter_upwards [h] with p hp
    apply Prod.ext
    · funext n
      cases n with
      | zero => exact hp.1.symm
      | succ n => rfl
    · funext n
      cases n with
      | zero => exact hp.2.symm
      | succ n => rfl
  rw [Measure.map_congr he, Measure.map_id]

/-- The exact whole-path assertion of L06. In fact the unused initial mark
can be either value, so the source initial mark `1` is included. -/
theorem extracted_pair_map_eq_prod (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (hf : Fair α κ) (x y : E) (i : Bool) :
    (InterleavedChain.fullLaw α κ (x, y, i)).map
      (fun H => (extracted H true, extracted H false)) =
      (CountableMarkovChain.fullLaw α x).prod (CountableMarkovChain.fullLaw α y) := by
  let μ := (InterleavedChain.fullLaw α κ (x, y, i)).map
    (fun H => (extracted H true, extracted H false))
  let ν := (CountableMarkovChain.fullLaw α x).prod (CountableMarkovChain.fullLaw α y)
  have hm : Measurable (fun H : ℕ → State E => (extracted H true, extracted H false)) :=
    (measurable_extracted true).prodMk (measurable_extracted false)
  have htails : μ.map pathPairTail = ν.map pathPairTail := by
    apply pair_eq_of_word_probabilities
    intro u v
    have hB : MeasurableSet {p : (ℕ → E) × (ℕ → E) |
        initialWord p.1 u.length = u ∧ initialWord p.2 v.length = v} :=
      (((measurable_initialWord u.length).comp measurable_fst).eq measurable_const).and
        (((measurable_initialWord v.length).comp measurable_snd).eq measurable_const) |>.setOf
    rw [Measure.map_apply measurable_pathPairTail hB,
      Measure.map_apply measurable_pathPairTail hB]
    change μ {p | futureWord p.1 u.length = u ∧ futureWord p.2 v.length = v} =
      ν {p | futureWord p.1 u.length = u ∧ futureWord p.2 v.length = v}
    have hfuture : MeasurableSet {p : (ℕ → E) × (ℕ → E) |
        futureWord p.1 u.length = u ∧ futureWord p.2 v.length = v} :=
      (((measurable_futureWord u.length).comp measurable_fst).eq measurable_const).and
        (((measurable_futureWord v.length).comp measurable_snd).eq measurable_const) |>.setOf
    rw [show μ = _ from rfl, Measure.map_apply hm hfuture]
    change (InterleavedChain.fullLaw α κ (x, y, i))
        {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v} = _
    rw [extractedWord_pair_probability α κ hf]
    change _ = (CountableMarkovChain.fullLaw α x).prod (CountableMarkovChain.fullLaw α y)
      ({H | futureWord H u.length = u} ×ˢ {H | futureWord H v.length = v})
    rw [Measure.prod_prod, futureWord_probability, futureWord_probability]
  have hμinitial : ∀ᵐ p ∂μ, p.1 0 = x ∧ p.2 0 = y := by
    apply (ae_map_iff hm.aemeasurable
      ((((measurable_pi_apply 0).comp measurable_fst).eq measurable_const).and
        (((measurable_pi_apply 0).comp measurable_snd).eq measurable_const) |>.setOf)).mpr
    filter_upwards [CountableMarkovChain.fullLaw_initial (transition α κ) (x, y, i)] with H hH
    simp [extracted_zero, hH]
  have hνfirst : ∀ᵐ p ∂ν, p.1 0 = x := by
    apply ae_of_ae_map (μ := ν) (f := Prod.fst) (p := fun H => H 0 = x)
      measurable_fst.aemeasurable
    simp only [ν, Measure.map_fst_prod, measure_univ, one_smul]
    exact CountableMarkovChain.fullLaw_initial α x
  have hνsecond : ∀ᵐ p ∂ν, p.2 0 = y := by
    apply ae_of_ae_map (μ := ν) (f := Prod.snd) (p := fun H => H 0 = y)
      measurable_snd.aemeasurable
    simp only [ν, Measure.map_snd_prod, measure_univ, one_smul]
    exact CountableMarkovChain.fullLaw_initial α y
  have hνinitial : ∀ᵐ p ∂ν, p.1 0 = x ∧ p.2 0 = y := hνfirst.and hνsecond
  have hh := congrArg (fun ρ => ρ.map (pathPairPrepend x y)) htails
  rwa [map_tail_prepend μ x y hμinitial, map_tail_prepend ν x y hνinitial] at hh

/-- The complete extracted pair has the law of two independently sampled
copies of the original Markov chain. -/
theorem extracted_pair_hasLaw (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (hf : Fair α κ) (x y : E) (i : Bool) :
    HasLaw (fun H => (extracted H true, extracted H false))
      ((CountableMarkovChain.fullLaw α x).prod (CountableMarkovChain.fullLaw α y))
      (InterleavedChain.fullLaw α κ (x, y, i)) :=
  ⟨((measurable_extracted true).prodMk (measurable_extracted false)).aemeasurable,
    extracted_pair_map_eq_prod α κ hf x y i⟩

end Freezing1.InterleavedChain
