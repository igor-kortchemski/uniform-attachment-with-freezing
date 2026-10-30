module

public import Freezing1.SIRCaptureCoefficientObserved
public import Freezing1.MainSIREmbedded

/-! The literal two uniform reverse-birth marginals, sampled independently conditional on one tree. -/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory
open scoped Classical NNReal Topology

set_option backward.isDefEq.respectTransparency false

noncomputable def wordObservedBirthPairKernel (n : ℕ) (w : Fin (2 * n + 1) → Bool) :
    Measure (ℕ × ℕ) :=
  (Forward.treeLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1)).bind fun s =>
    let μ := (Measure.uniformOfFinset s.vertices).map
      (Forward.reverseBirthClock (captureWordExtinction n w) s)
    μ.prod μ

instance wordObservedBirthPairKernel_probability (n : ℕ) (w : Fin (2 * n + 1) → Bool) :
    IsProbabilityMeasure (wordObservedBirthPairKernel n w) := by
  apply isProbabilityMeasure_bind measurable_from_top.aemeasurable
  filter_upwards [Forward.treeLaw_valid (ForwardAnnealed.wordSchedule w) (2 * n + 1)] with s hs
  have := Forward.uniform_vertices_probability s ⟨0, hs.root_mem⟩
  have : IsProbabilityMeasure ((Measure.uniformOfFinset s.vertices).map
      (Forward.reverseBirthClock (captureWordExtinction n w) s)) :=
    Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr inferInstance
  infer_instance

theorem wordObservedBirthPairKernel_map_fst (n : ℕ) (w : Fin (2 * n + 1) → Bool) :
    (wordObservedBirthPairKernel n w).map Prod.fst = wordObservedBirthKernel n w := by
  rw [wordObservedBirthPairKernel, wordObservedBirthKernel,
    Measure.map_bind measurable_from_top.aemeasurable measurable_fst.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [Forward.treeLaw_valid (ForwardAnnealed.wordSchedule w) (2 * n + 1)] with s hs
  have := Forward.uniform_vertices_probability s ⟨0, hs.root_mem⟩
  have : IsProbabilityMeasure ((Measure.uniformOfFinset s.vertices).map
      (Forward.reverseBirthClock (captureWordExtinction n w) s)) :=
    Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr inferInstance
  rw [Measure.map_fst_prod, measure_univ, one_smul]

theorem wordObservedBirthPairKernel_map_snd (n : ℕ) (w : Fin (2 * n + 1) → Bool) :
    (wordObservedBirthPairKernel n w).map Prod.snd = wordObservedBirthKernel n w := by
  rw [wordObservedBirthPairKernel, wordObservedBirthKernel,
    Measure.map_bind measurable_from_top.aemeasurable measurable_snd.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [Forward.treeLaw_valid (ForwardAnnealed.wordSchedule w) (2 * n + 1)] with s hs
  have := Forward.uniform_vertices_probability s ⟨0, hs.root_mem⟩
  have : IsProbabilityMeasure ((Measure.uniformOfFinset s.vertices).map
      (Forward.reverseBirthClock (captureWordExtinction n w) s)) :=
    Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr inferInstance
  rw [Measure.map_snd_prod, measure_univ, one_smul]

noncomputable def actualTerminalReverseBirthPairLaw (r : ℝ≥0) (n : ℕ) : Measure (ℕ × ℕ) :=
  (signWordLaw r n (2 * n + 1)).bind (wordObservedBirthPairKernel n)

instance actualTerminalReverseBirthPairLaw_probability (r : ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (actualTerminalReverseBirthPairLaw r n) :=
  isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
    (Eventually.of_forall fun _ => inferInstance)

theorem actualTerminalReverseBirthPairLaw_map_fst (r : ℝ≥0) (n : ℕ) :
    (actualTerminalReverseBirthPairLaw r n).map Prod.fst = actualTerminalReverseBirthLaw r n := by
  rw [actualTerminalReverseBirthPairLaw, actualTerminalReverseBirthLaw,
    Measure.map_bind (measurable_of_countable _).aemeasurable measurable_fst.aemeasurable]
  congr 1
  funext w
  exact wordObservedBirthPairKernel_map_fst n w

theorem actualTerminalReverseBirthPairLaw_map_snd (r : ℝ≥0) (n : ℕ) :
    (actualTerminalReverseBirthPairLaw r n).map Prod.snd = actualTerminalReverseBirthLaw r n := by
  rw [actualTerminalReverseBirthPairLaw, actualTerminalReverseBirthLaw,
    Measure.map_bind (measurable_of_countable _).aemeasurable measurable_snd.aemeasurable]
  congr 1
  funext w
  exact wordObservedBirthPairKernel_map_snd n w

/-- The source's two probabilities are equal because both samples are
conditionally uniform on the same whole terminal tree. -/
theorem actualTerminalReverseBirthPairLaw_same_epsilon (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    {eps : ℝ} (heps : 0 < eps) (hepsT : eps < fluidExtinctionTime lam) :
    ∀ᶠ n : ℕ in atTop,
      1 - eps ≤ (actualTerminalReverseBirthPairLaw (rate n) n).real
          {z | (z.1 : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)} ∧
        (actualTerminalReverseBirthPairLaw (rate n) n).real
            {z | (z.1 : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)} =
          (actualTerminalReverseBirthPairLaw (rate n) n).real
            {z | (z.2 : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)} := by
  filter_upwards [actualTerminalReverseBirthLaw_same_epsilon rate lam hlam hscaled heps hepsT]
    with n hn
  have hf := actualTerminalReverseBirthPairLaw_map_fst (rate n) n
  have hs := actualTerminalReverseBirthPairLaw_map_snd (rate n) n
  have hfst : (actualTerminalReverseBirthPairLaw (rate n) n).real
        {z | (z.1 : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)} =
      (actualTerminalReverseBirthLaw (rate n) n).real
        {j | (j : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)} := by
    rw [← hf, map_measureReal_apply measurable_fst ((Set.to_countable _).measurableSet)]
    rfl
  have hsnd : (actualTerminalReverseBirthPairLaw (rate n) n).real
        {z | (z.2 : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)} =
      (actualTerminalReverseBirthLaw (rate n) n).real
        {j | (j : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)} := by
    rw [← hs, map_measureReal_apply measurable_snd ((Set.to_countable _).measurableSet)]
    rfl
  exact ⟨by rwa [hfst], hfst.trans hsnd.symm⟩

theorem source_same_epsilon_two_reverse_births (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1))
    {eps : ℝ} (heps : 0 < eps) (hepsT : eps < fluidExtinctionTime lam) :
    ∀ᶠ n : ℕ in atTop,
      1 - eps ≤ (actualTerminalReverseBirthPairLaw (rate n) n).real
          {z | (z.1 : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)} ∧
        (actualTerminalReverseBirthPairLaw (rate n) n).real
            {z | (z.1 : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)} =
          (actualTerminalReverseBirthPairLaw (rate n) n).real
            {z | (z.2 : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)} :=
  actualTerminalReverseBirthPairLaw_same_epsilon rate lam hlam
    (scaled_rate_of_source_ratio rate lam
      (by exact_mod_cast (lt_trans zero_lt_one hlam)) hratio) heps hepsT

end Freezing1.SIR
