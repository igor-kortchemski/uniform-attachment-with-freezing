module

public import Freezing1.InterleavedWordExtraction
public import Freezing1.CountableMarkovShift

/-!
# The extracted cylinder law under the source fairness assumptions

Fairness is transported to every deterministic time by the actual Markov
shift law. Bounded convergence of the two completion probabilities then
identifies the joint extracted cylinders with the product Markov cylinders.
-/

@[expose] public section

namespace Freezing1.InterleavedChain

open MeasureTheory ProbabilityTheory CountableMarkovChain Filter
open scoped ENNReal Topology Classical

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

theorem fullLaw_pathFair (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (hf : Fair α κ) (s : State E) :
    ∀ᵐ H ∂InterleavedChain.fullLaw α κ s, PathFair α H := by
  apply ae_all_iff.mpr
  intro side
  apply ae_all_iff.mpr
  intro n
  let P : State E → (ℕ → State E) → Prop := fun z H =>
    ¬Absorbing α (coordinate z side) → ∃ k, 0 < k ∧ (H k).2.2 = side
  have hP : MeasurableSet {q : State E × (ℕ → State E) | P q.1 q.2} := by
    apply Measurable.setOf
    apply Measurable.imp
    · exact ((measurable_of_countable (fun z : State E => Absorbing α (coordinate z side))).comp measurable_fst).not
    · apply Measurable.exists
      intro k
      exact measurable_const.and (((measurable_pi_apply k).comp measurable_snd).snd.snd.eq measurable_const)
  have hstart : ∀ z, ∀ᵐ H ∂CountableMarkovChain.fullLaw (transition α κ) z, P z H := by
    rintro ⟨x, y, i⟩
    cases side with
    | false =>
      by_cases h : Absorbing α y
      · exact Filter.Eventually.of_forall fun _ hn => (hn h).elim
      · exact (hf.2 x y i h).mono fun _ hh _ => hh
    | true =>
      by_cases h : Absorbing α x
      · exact Filter.Eventually.of_forall fun _ hn => (hn h).elim
      · exact (hf.1 x y i h).mono fun _ hh _ => hh
  filter_upwards [fullLaw_ae_shift (transition α κ) s n P hP hstart] with H hh
  intro hn
  obtain ⟨k, hk, hmark⟩ := hh hn
  exact ⟨n + k, by omega, hmark⟩

theorem measurable_extractedWord (side : Bool) (r : ℕ) :
    Measurable (fun H : ℕ → State E => extractedWord H side r) := by
  have hm : Measurable (fun H : ℕ → State E => fun i : Fin r => extracted H side (i.val + 1)) :=
    Measurable.of_eval fun i => (measurable_pi_apply (i.val + 1)).comp (measurable_extracted side)
  exact (measurable_of_countable (List.ofFn : (Fin r → E) → List E)).comp hm

theorem measurable_observations (n : ℕ) :
    Measurable (fun H : ℕ → State E => observations H n) :=
  (measurable_of_countable (accumulatePrefix ([], []) updateObservation n)).comp (by fun_prop)

/-- The exact joint law of any two finite future words in the extracted
chains. The initial coordinates are handled separately by `extracted_zero`.
The scheduler can depend arbitrarily on both states and either coordinate
may be absorbed after finitely many selections. -/
theorem extractedWord_pair_probability (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (hf : Fair α κ) (x y : E) (i : Bool) (u v : List E) :
    (InterleavedChain.fullLaw α κ (x, y, i))
      {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v} =
      wordProbability α x u * wordProbability α y v := by
  let μ := InterleavedChain.fullLaw α κ (x, y, i)
  let F : ℕ → (ℕ → State E) → ℝ≥0∞ :=
    fun n H => pairCompletion α x y u v (observations H n)
  let B : Set (ℕ → State E) :=
    {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v}
  have hB : MeasurableSet B :=
    ((measurable_extractedWord true u.length).eq measurable_const).and
      ((measurable_extractedWord false v.length).eq measurable_const) |>.setOf
  have hlim : ∀ᵐ H ∂μ, Tendsto (fun n => F n H) atTop (𝓝 (B.indicator 1 H)) := by
    filter_upwards [CountableMarkovChain.fullLaw_initial (transition α κ) (x, y, i),
      fullLaw_movesOnlySelected α κ (x, y, i), fullLaw_pathFair α κ hf (x, y, i)]
      with H hzero hm hfair
    have hleft := completion_observed_eventually α H hm hfair true u
    have hright := completion_observed_eventually α H hm hfair false v
    have he : (fun n => F n H) =ᶠ[atTop] (fun _ => B.indicator 1 H) := by
      filter_upwards [hleft, hright] with n hl hr
      simp only [coordinate, observedCoordinate, hzero, ite_true, Bool.false_eq_true, ite_false] at hl hr
      dsimp [F, pairCompletion]
      rw [hl, hr]
      by_cases hu : extractedWord H true u.length = u <;>
        by_cases hv : extractedWord H false v.length = v <;> simp [B, hu, hv]
    exact tendsto_const_nhds.congr' he.symm
  have hint := tendsto_lintegral_of_dominated_convergence (μ := μ) (fun _ => 1)
    (fun n => (measurable_of_countable (pairCompletion α x y u v)).comp (measurable_observations n))
    (fun n => Filter.Eventually.of_forall fun H => by
      exact (mul_le_mul' (completion_le_one α x (observations H n).1 u)
        (completion_le_one α y (observations H n).2 v)).trans_eq (one_mul 1))
    (by simp) hlim
  have hconst : (fun n => ∫⁻ H, F n H ∂μ) =
      fun _ : ℕ => wordProbability α x u * wordProbability α y v := by
    funext n
    exact lintegral_pairCompletion_observations α κ x y i u v n
  change Tendsto (fun n => ∫⁻ H, F n H ∂μ) atTop (𝓝 _) at hint
  rw [hconst] at hint
  have he := tendsto_nhds_unique hint tendsto_const_nhds
  simpa only [lintegral_indicator_one hB] using he

end Freezing1.InterleavedChain
