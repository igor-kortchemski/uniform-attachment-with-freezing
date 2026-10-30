module

public import Freezing1.SIRClockPrefixLaw
public import Freezing1.CountableMarkovObservations
public import Freezing1.CountablePathLaw

/-!
# The complete event-word law of one preassigned clock array

The reference word kernel is derived from the exponential product already
proved for relevant clocks. Equality with the original, single static array
is then proved from its actual prefix probabilities and the deterministic
coherence of word histories.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def clockChoiceLaw {n : ℕ} (r : ℝ) (z : PopulationState n) :
    Measure (ClockChoice n) :=
  (relevantClockLaw r z).map (relevantFirstLive z)

theorem clockChoiceLaw_probability {n : ℕ} {r : ℝ} (hr : 0 < r) (z : PopulationState n) :
    IsProbabilityMeasure (clockChoiceLaw r z) := by
  have := relevantClockLaw_probability hr z
  exact Measure.isProbabilityMeasure_map_iff (measurable_relevantFirstLive z).aemeasurable
    |>.mpr inferInstance

theorem clockChoiceLaw_singleton {n : ℕ} {r : ℝ} (hr : 0 < r)
    {z : PopulationState n} (hz : z.Valid) (c : ClockChoice n) :
    clockChoiceLaw r z {c} = clockChoiceWeight r z c := by
  have := relevantClockLaw_probability hr (optionPopulationStep z c)
  have hh := congrArg
    (fun mu : Measure (RelevantCoordinate (optionPopulationStep z c) → ℝ) => mu univ)
    (relevant_clock_choice_transition hz hr c)
  rw [Measure.map_apply (measurable_nextResidualForChoice hz c) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] at hh
  rw [clockChoiceLaw, Measure.map_apply (measurable_relevantFirstLive z)
    (measurableSet_singleton c)]
  exact hh

noncomputable def clockWordKernel (r : ℝ) (_hr : 0 < r) (n : ℕ) :
    Kernel (ClockWord n) (ClockWord n) where
  toFun w := (clockChoiceLaw r (replayPopulation n w)).map (fun c => c :: w)
  measurable' := measurable_of_countable _

instance clockWordKernel_markov (r : ℝ) (hr : 0 < r) (n : ℕ) :
    IsMarkovKernel (clockWordKernel r hr n) := by
  constructor
  intro w
  have := clockChoiceLaw_probability hr (replayPopulation n w)
  exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable
    |>.mpr inferInstance

theorem clockWordKernel_nil (r : ℝ) (hr : 0 < r) (n : ℕ) (w : ClockWord n) :
    clockWordKernel r hr n w {[]} = 0 := by
  change ((clockChoiceLaw r (replayPopulation n w)).map (fun c => c :: w)) {[]} = 0
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton [])]
  have he : (fun c : ClockChoice n => c :: w) ⁻¹' {[]} = ∅ := by ext c; simp
  rw [he, measure_empty]

theorem clockWordKernel_cons (r : ℝ) (hr : 0 < r) (n : ℕ)
    (w u : ClockWord n) (c : ClockChoice n) :
    clockWordKernel r hr n w {c :: u} =
      if u = w then clockChoiceWeight r (replayPopulation n w) c else 0 := by
  change ((clockChoiceLaw r (replayPopulation n w)).map (fun c => c :: w)) {c :: u} = _
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  by_cases hu : u = w
  · subst u
    have he : (fun d : ClockChoice n => d :: w) ⁻¹' {c :: w} = {c} := by ext d; simp
    rw [he, clockChoiceLaw_singleton hr (replayPopulation_valid n w) c, ite_eq_left rfl]
  · have he : (fun d : ClockChoice n => d :: w) ⁻¹' {c :: u} = ∅ := by
      ext d
      simp only [mem_preimage, mem_singleton_iff, List.cons.injEq, mem_empty_iff_false,
        iff_false, not_and]
      intro _ hwu
      exact hu hwu.symm
    rw [he, measure_empty, ite_eq_right hu]

noncomputable def clockWordFullLaw (r : ℝ) (hr : 0 < r) (n : ℕ) :
    Measure (ℕ → ClockWord n) :=
  CountableMarkovChain.fullLaw (clockWordKernel r hr n) []

instance clockWordFullLaw_probability (r : ℝ) (hr : 0 < r) (n : ℕ) :
    IsProbabilityMeasure (clockWordFullLaw r hr n) := by unfold clockWordFullLaw; infer_instance

theorem clockWordFullLaw_marginal (r : ℝ) (hr : 0 < r) (n k : ℕ) (w : ClockWord n) :
    ((clockWordFullLaw r hr n).map (fun H => H k)) {w} =
      if w.length = k then clockWordWeight r n w else 0 := by
  induction k generalizing w with
  | zero =>
    rw [clockWordFullLaw, CountableMarkovChain.map_eval_zero]
    cases w with
    | nil => simp [clockWordWeight]
    | cons c w => simp
  | succ k ih =>
    rw [clockWordFullLaw, CountableMarkovChain.map_eval_succ,
      Measure.bind_apply (measurableSet_singleton _) (clockWordKernel r hr n).aemeasurable]
    change (∫⁻ u, clockWordKernel r hr n u {w}
      ∂(clockWordFullLaw r hr n).map (fun H => H k)) = _
    cases w with
    | nil => simp_rw [clockWordKernel_nil]; simp
    | cons c w =>
      simp_rw [clockWordKernel_cons]
      have hf : (fun u : ClockWord n =>
          if w = u then clockChoiceWeight r (replayPopulation n u) c else 0) =
          ({w} : Set (ClockWord n)).indicator
            (fun _ => clockChoiceWeight r (replayPopulation n w) c) := by
        funext u
        by_cases hu : w = u
        · subst u; simp
        · simp [hu, Ne.symm hu]
      rw [hf, lintegral_indicator_const (measurableSet_singleton w), ih]
      simp only [List.length_cons, Nat.add_right_cancel_iff, clockWordWeight]
      split_ifs <;> simp [mul_comm]

theorem preassigned_word_marginal {r : ℝ} (hr : 0 < r) (n k : ℕ) (w : ClockWord n) :
    ((preassignedClockLaw r n).map (fun omega => preassignedWord n omega k)) {w} =
      if w.length = k then clockWordWeight r n w else 0 := by
  rw [Measure.map_apply (measurable_preassignedWord n k) (measurableSet_singleton w)]
  by_cases hw : w.length = k
  · rw [ite_eq_left hw, ← hw]
    exact preassigned_clock_word_probability hr n w
  · rw [ite_eq_right hw]
    have he : (fun omega => preassignedWord n omega k) ⁻¹' {w} = ∅ := by
      ext omega
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      intro he
      exact hw (he ▸ preassignedWord_length n omega k)
    rw [he, measure_empty]

theorem preassigned_word_marginal_eq {r : ℝ} (hr : 0 < r) (n k : ℕ) :
    (preassignedClockLaw r n).map (fun omega => preassignedWord n omega k) =
      (clockWordFullLaw r hr n).map (fun H => H k) := by
  apply Measure.ext_of_singleton
  intro w
  rw [preassigned_word_marginal hr, clockWordFullLaw_marginal]

/-- Growing newest-first words determine their entire earlier history. -/
theorem coherent_word_drop {n : ℕ} (H : ℕ → ClockWord n)
    (hH : ∀ k, ∃ c, H (k + 1) = c :: H k) {a b : ℕ} (hab : a ≤ b) :
    (H b).drop (b - a) = H a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    obtain ⟨c, hc⟩ := hH b
    rw [hc, show b + 1 - a = (b - a) + 1 by omega, List.drop_succ_cons, ih]

noncomputable def wordPrefixFromLast {n : ℕ} (k : ℕ) (w : ClockWord n) :
    (i : Finset.Iic k) → ClockWord n := fun i => w.drop (k - i.val)

theorem coherent_word_prefix {n : ℕ} (H : ℕ → ClockWord n)
    (hH : ∀ k, ∃ c, H (k + 1) = c :: H k) (k : ℕ) :
    Preorder.frestrictLe k H = wordPrefixFromLast k (H k) := by
  funext i
  exact (coherent_word_drop H hH (Finset.mem_Iic.mp i.property)).symm

theorem clockWordFullLaw_coherent (r : ℝ) (hr : 0 < r) (n : ℕ) :
    ∀ᵐ H ∂clockWordFullLaw r hr n, ∀ k, ∃ c, H (k + 1) = c :: H k := by
  unfold clockWordFullLaw
  apply CountableMarkovChain.fullLaw_steps (clockWordKernel r hr n) []
    (fun w u => ∃ c, u = c :: w)
  intro w
  change ∀ᵐ u ∂(clockChoiceLaw r (replayPopulation n w)).map (fun c => c :: w),
    ∃ c, u = c :: w
  apply (ae_map_iff (measurable_of_countable _).aemeasurable (by trivial)).mpr
  exact Filter.Eventually.of_forall fun c => ⟨c, rfl⟩

/-- The original array, used unchanged at every event, has the reference
complete word law. This is an equality of measures on all infinite histories. -/
theorem preassigned_clock_word_fullLaw {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (preassignedClockLaw r n).map (preassignedWord n) = clockWordFullLaw r hr n := by
  have := preassignedClockLaw_probability hr n
  have hm : Measurable (preassignedWord n) :=
    Measurable.of_eval (fun k => measurable_preassignedWord n k)
  apply CountablePathLaw.eq_of_prefix_map_eq
  intro k
  rw [Measure.map_map (by fun_prop) hm]
  calc
    _ = (preassignedClockLaw r n).map
        (wordPrefixFromLast k ∘ fun omega => preassignedWord n omega k) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun omega => coherent_word_prefix _
        (fun j => ⟨preassignedEvent n omega j, rfl⟩) k
    _ = ((preassignedClockLaw r n).map (fun omega => preassignedWord n omega k)).map
        (wordPrefixFromLast k) := by rw [Measure.map_map (measurable_of_countable _)
          (measurable_preassignedWord n k)]
    _ = ((clockWordFullLaw r hr n).map (fun H => H k)).map (wordPrefixFromLast k) := by
      rw [preassigned_word_marginal_eq hr n k]
    _ = (clockWordFullLaw r hr n).map (Preorder.frestrictLe k) := by
      rw [Measure.map_map (measurable_of_countable (wordPrefixFromLast k)) (by fun_prop)]
      apply Measure.map_congr
      filter_upwards [clockWordFullLaw_coherent r hr n] with H hH
      exact (coherent_word_prefix H hH k).symm

end Freezing1.SIR
