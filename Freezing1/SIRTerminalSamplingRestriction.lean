module

public import Freezing1.SIRFiniteRateEnvironmentTransfer
public import Freezing1.SIRFiniteRateSamplingCapture

/-!
# Terminal uniform-sampling restriction with arbitrary prefix gates

Exact adaptive-word projectivity retains earlier count gates. Along each
original fixed-word history, the fraction of later vertices is the actual
remaining susceptible loss divided by the actual terminal vertex count.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory RandomEnvironment
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

theorem wordCountsAt_takeSigns (n : ℕ) {K m i : ℕ} (w : Fin K → Bool)
    (hm : m ≤ K) (hi : i ≤ m) :
    wordCountsAt n (takeSigns w hm) i = wordCountsAt n w i := by
  have he : takeSigns (takeSigns w hm) hi = takeSigns w (hi.trans hm) := by
    funext j
    rfl
  calc
    _ = countsRunWord n (takeSigns (takeSigns w hm) hi) :=
      (countsRunWord_takeSigns n (takeSigns w hm) hi).symm
    _ = _ := by rw [he, countsRunWord_takeSigns]

theorem longer_word_gated_height_projectivity (rate : ℝ≥0) (n K m a : ℕ)
    (hm : m ≤ K) (ha : a ≤ m) (A : Set ℕ) :
    (∫⁻ w, if 0 < (wordCountsAt n w a).infectious then
      Forward.uniformHeightLaw (ForwardAnnealed.wordSchedule w) m A else 0
      ∂signWordLaw rate n K) =
    ∫⁻ w, if 0 < (wordCountsAt n w a).infectious then
      Forward.uniformHeightLaw (ForwardAnnealed.wordSchedule w) m A else 0
      ∂signWordLaw rate n m := by
  let f : (Fin m → Bool) → ℝ≥0∞ := fun w => if 0 < (wordCountsAt n w a).infectious then
    Forward.uniformHeightLaw (ForwardAnnealed.wordSchedule w) m A else 0
  calc
    _ = ∫⁻ w, f (takeSigns w hm) ∂signWordLaw rate n K := by
      apply lintegral_congr
      intro w
      have he : Forward.uniformHeightLaw (ForwardAnnealed.wordSchedule w) m =
          Forward.uniformHeightLaw (ForwardAnnealed.wordSchedule (takeSigns w hm)) m := by
        unfold Forward.uniformHeightLaw
        rw [Forward.treeLaw_eq_of_schedule_prefix (takeSigns_schedule_agree w hm)]
      simp only [f, wordCountsAt_takeSigns n w hm ha, he]
    _ = ∫⁻ w, f w ∂(signWordLaw rate n K).map (fun w => takeSigns w hm) :=
      (lintegral_map (measurable_of_countable _) (measurable_of_countable _)).symm
    _ = _ := by rw [signWordLaw_map_takeSigns]

theorem longer_word_gated_pair_projectivity (rate : ℝ≥0) (n K m a : ℕ)
    (hm : m ≤ K) (ha : a ≤ m) (A : Set (ℕ × ℕ × ℕ)) :
    (∫⁻ w, if 0 < (wordCountsAt n w a).infectious then
      CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule w) m A else 0
      ∂signWordLaw rate n K) =
    ∫⁻ w, if 0 < (wordCountsAt n w a).infectious then
      CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule w) m A else 0
      ∂signWordLaw rate n m := by
  let f : (Fin m → Bool) → ℝ≥0∞ := fun w => if 0 < (wordCountsAt n w a).infectious then
    CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule w) m A else 0
  calc
    _ = ∫⁻ w, f (takeSigns w hm) ∂signWordLaw rate n K := by
      apply lintegral_congr
      intro w
      have he : CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule w) m =
          CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule (takeSigns w hm)) m := by
        unfold CanonicalTree.forwardPairDataLaw
        rw [Forward.treeLaw_eq_of_schedule_prefix (takeSigns_schedule_agree w hm)]
      simp only [f, wordCountsAt_takeSigns n w hm ha, he]
    _ = ∫⁻ w, f w ∂(signWordLaw rate n K).map (fun w => takeSigns w hm) :=
      (lintegral_map (measurable_of_countable _) (measurable_of_countable _)).symm
    _ = _ := by rw [signWordLaw_map_takeSigns]

theorem word_relative_later_vertex_fraction (n : ℕ) {K m : ℕ} (w : Fin K → Bool)
    (hw : SignWordFeasible n w) (hm : m ≤ K) {eta : ℝ}
    (hrelative : ((wordCountsAt n w m).susceptible : ℝ) - (wordCountsAt n w K).susceptible ≤
      eta * ((n + 1 - (wordCountsAt n w K).susceptible : ℕ) : ℝ)) :
    ∀ᵐ H ∂ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w),
      (((H K).vertices.card : ℝ) - (H m).vertices.card) / (H K).vertices.card ≤ eta := by
  filter_upwards [original_word_history_vertex_count n w hw hm,
    original_word_history_vertex_count n w hw le_rfl,
    ForwardInfiniteHistory.fullLaw_valid (ForwardAnnealed.wordSchedule w)] with H hprefix hterminal hv
  have hp : ((wordCountsAt n w m).susceptible : ℝ) + (H m).vertices.card = (n : ℝ) + 1 := by
    exact_mod_cast hprefix
  have ht : ((wordCountsAt n w K).susceptible : ℝ) + (H K).vertices.card = (n : ℝ) + 1 := by
    exact_mod_cast hterminal
  have hcard : n + 1 - (wordCountsAt n w K).susceptible = (H K).vertices.card := by omega
  rw [hcard] at hrelative
  have hBpos : (0 : ℝ) < (H K).vertices.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, (hv K).root_mem⟩
  apply (div_le_iff₀ hBpos).mpr
  linarith

theorem word_uniform_samples_relative_bound (n : ℕ) {K m : ℕ} (w : Fin K → Bool)
    (hw : SignWordFeasible n w) (hm : m ≤ K) {eta : ℝ} (heta : 0 ≤ eta)
    (hrelative : ((wordCountsAt n w m).susceptible : ℝ) - (wordCountsAt n w K).susceptible ≤
      eta * ((n + 1 - (wordCountsAt n w K).susceptible : ℕ) : ℝ))
    (A : Set ℕ) (B : Set (ℕ × ℕ × ℕ)) :
    Forward.uniformHeightLaw (ForwardAnnealed.wordSchedule w) K A ≤
      Forward.uniformHeightLaw (ForwardAnnealed.wordSchedule w) m A + ENNReal.ofReal (2 * eta) ∧
    CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule w) K B ≤
      CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule w) m B + ENNReal.ofReal (2 * eta) := by
  have hevent : ∀ᵐ H ∂ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w),
      Forward.vertexHeightKernel (H K) A ≤ Forward.vertexHeightKernel (H m) A + ENNReal.ofReal (2 * eta) ∧
      CanonicalTree.forwardPairKernel (H K) B ≤ CanonicalTree.forwardPairKernel (H m) B +
        ENNReal.ofReal (2 * eta) := by
    filter_upwards [word_relative_later_vertex_fraction n w hw hm hrelative,
      ForwardInfiniteHistory.fullLaw_uniform_samples_restriction_bound
        (ForwardAnnealed.wordSchedule w) m K hm A B,
      ForwardInfiniteHistory.fullLaw_valid (ForwardAnnealed.wordSchedule w)] with H hf hr hv
    have := forward_pair_kernel_probability_of_nonempty (H m) ⟨0, (hv m).root_mem⟩
    have := forward_pair_kernel_probability_of_nonempty (H K) ⟨0, (hv K).root_mem⟩
    constructor
    · apply measure_le_add_of_real_le _ _ A (by positivity)
      have hh := le_abs_self ((Forward.vertexHeightKernel (H K)).real A -
        (Forward.vertexHeightKernel (H m)).real A)
      nlinarith [hr.1]
    · apply measure_le_add_of_real_le _ _ B (by positivity)
      have hh := le_abs_self ((CanonicalTree.forwardPairKernel (H K)).real B -
        (CanonicalTree.forwardPairKernel (H m)).real B)
      nlinarith [hr.2]
  constructor
  · rw [Forward.uniformHeightLaw, forward_sampling_event_lintegral _ _ _ A (Set.to_countable _).measurableSet,
      Forward.uniformHeightLaw, forward_sampling_event_lintegral _ _ _ A (Set.to_countable _).measurableSet]
    calc
      _ ≤ ∫⁻ H, Forward.vertexHeightKernel (H m) A + ENNReal.ofReal (2 * eta)
          ∂ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w) :=
        lintegral_mono_ae (hevent.mono fun _ h => h.1)
      _ = _ := by rw [lintegral_add_right _ measurable_const]; simp
  · rw [CanonicalTree.forwardPairDataLaw,
      forward_sampling_event_lintegral _ _ _ B (Set.to_countable _).measurableSet,
      CanonicalTree.forwardPairDataLaw,
      forward_sampling_event_lintegral _ _ _ B (Set.to_countable _).measurableSet]
    calc
      _ ≤ ∫⁻ H, CanonicalTree.forwardPairKernel (H m) B + ENNReal.ofReal (2 * eta)
          ∂ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w) :=
        lintegral_mono_ae (hevent.mono fun _ h => h.2)
      _ = _ := by rw [lintegral_add_right _ measurable_const]; simp

theorem signWordLaw_relative_late_births_tendsto (rate : ℕ → ℝ≥0)
    {lam t eta : ℝ} (hlam : 1 < lam)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds lam))
    (heta : 0 < eta) (ht : fluidExtinctionTime lam / 2 < t)
    (htt : t < fluidExtinctionTime lam)
    (hgap : fluidExtinctionTime lam - t < eta * (fluidExtinctionTime lam / 8)) :
    Tendsto (fun n => signWordLaw (rate n) n (2 * n + 1) {w |
      eta * ((n + 1 - (wordCountsAt n w (2 * n + 1)).susceptible : ℕ) : ℝ) ≤
        (wordCountsAt n w ⌊t * (n : ℝ)⌋₊).susceptible -
          ((wordCountsAt n w (2 * n + 1)).susceptible : ℝ)}) atTop (nhds 0) := by
  have hh := countsFullLaw_relative_late_births_tendsto rate hlam hrate heta ht htt hgap
  convert hh using 1
  funext n
  have ht2 : t ≤ 2 := (htt.trans (fluidExtinctionTime_spec hlam).2.1).le
  have hm : ⌊t * (n : ℝ)⌋₊ ≤ 2 * n + 1 := by
    apply Nat.floor_le_of_le
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have he := signWordLaw_wordCountsAt_event_eq (rate n) n (2 * n + 1)
    {C | eta * ((n + 1 - (C (2 * n + 1)).susceptible : ℕ) : ℝ) ≤
      (C ⌊t * (n : ℝ)⌋₊).susceptible - ((C (2 * n + 1)).susceptible : ℝ)} (by
      intro C D hCD
      simp only [mem_ofPred_eq]
      rw [hCD _ hm, hCD _ le_rfl])
  simpa only [mem_ofPred_eq, mul_comm (n : ℝ) t] using he

end Freezing1.SIR
