module

public import Freezing1.SIRRandomEnvironmentTransferPrefix
public import Freezing1.MainSIRUniformDistanceStrong
public import Freezing1.SIRLateMaximumWord
public import Freezing1.ForwardUniformRestriction
public import Freezing1.SIRLateInfectionProbability

/-!
# Capturing terminal uniform samples by population time

Complete adaptive words are retained while prefix samples are compared
with terminal samples along the same original forward history. Exact
vertex-card identities identify the error as remaining susceptibles.
-/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

theorem ValidAt.toPlaneState_vertices_card {n : ℕ} {s : State} (hs : ValidAt n s) :
    s.toPlaneState.vertices.card = s.vertices.card :=
  Finset.card_image_iff.mpr hs.planeAddress_injective

end Freezing1.Forward

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory RandomEnvironment
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem feasible_takeSigns (n : ℕ) {K : ℕ} (w : Fin K → Bool) (hw : SignWordFeasible n w)
    {k : ℕ} (hk : k ≤ K) : SignWordFeasible n (takeSigns w hk) := by
  induction K generalizing k with
  | zero =>
    have he : k = 0 := by omega
    subst k
    trivial
  | succ K ih =>
    by_cases he : k = K + 1
    · subst k
      simpa only [takeSigns_self] using hw
    · have hk' : k ≤ K := by omega
      rw [← takeSigns_init w hk']
      exact ih (Fin.init w) hw.1 hk'

theorem countsRunWord_takeSigns (n : ℕ) {K : ℕ} (w : Fin K → Bool) {k : ℕ} (hk : k ≤ K) :
    countsRunWord n (takeSigns w hk) = wordCountsAt n w k := by
  induction K generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst k
    rw [takeSigns_self, wordCountsAt_last]
  | succ K ih =>
    by_cases he : k = K + 1
    · subst k
      rw [takeSigns_self, wordCountsAt_last]
    · have hk' : k ≤ K := by omega
      rw [← takeSigns_init w hk', wordCountsAt_init n w hk']
      exact ih (Fin.init w) hk'

theorem original_word_treeLaw_vertex_count (n : ℕ) {K : ℕ} (w : Fin K → Bool)
    (hw : SignWordFeasible n w) {i : ℕ} (hi : i ≤ K) :
    ∀ᵐ s ∂Forward.treeLaw (ForwardAnnealed.wordSchedule w) i,
      (wordCountsAt n w i).susceptible + s.vertices.card = n + 1 := by
  let v := takeSigns w hi
  have hv : SignWordFeasible n v := feasible_takeSigns n w hw hi
  have hp := planeWordLaw_phase_feasible n v hv
  rw [← map_fixedWord_treeLaw_to_planeWordLaw v] at hp
  have hp' := ae_of_ae_map Forward.measurable_toPlaneState.aemeasurable hp
  rw [Forward.treeLaw_eq_of_schedule_prefix (takeSigns_schedule_agree w hi)]
  filter_upwards [hp', Forward.treeLaw_valid (ForwardAnnealed.wordSchedule v) i] with s hs hvalid
  have hh := hs.2.2
  rw [hvalid.toPlaneState_vertices_card, countsRunWord_takeSigns n w hi] at hh
  exact hh

theorem original_word_history_vertex_count (n : ℕ) {K : ℕ} (w : Fin K → Bool)
    (hw : SignWordFeasible n w) {i : ℕ} (hi : i ≤ K) :
    ∀ᵐ H ∂ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w),
      (wordCountsAt n w i).susceptible + (H i).vertices.card = n + 1 := by
  have hp := original_word_treeLaw_vertex_count n w hw hi
  rw [← ForwardInfiniteHistory.map_eval] at hp
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hp

theorem terminal_word_later_vertex_fraction (n : ℕ) (hn : 0 < n)
    (w : Fin (2 * n + 1) → Bool) (hw : SignWordFeasible n w)
    {delta : ℝ} (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1 / 2)
    (hU : ((wordCountsAt n w n).susceptible : ℝ) ≤ delta * n) :
    ∀ᵐ H ∂ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w),
      (((H (2 * n + 1)).vertices.card : ℝ) - (H n).vertices.card) /
        (H (2 * n + 1)).vertices.card ≤ 2 * delta := by
  filter_upwards [original_word_history_vertex_count n w hw (show n ≤ 2 * n + 1 by omega),
    original_word_history_vertex_count n w hw le_rfl,
    ForwardInfiniteHistory.fullLaw_old_geometry (ForwardAnnealed.wordSchedule w) n (2 * n + 1)
      (by omega)] with H hprefix hterminal hgeometry
  have hp : ((wordCountsAt n w n).susceptible : ℝ) + (H n).vertices.card = (n : ℝ) + 1 := by
    exact_mod_cast hprefix
  have ht : ((wordCountsAt n w (2 * n + 1)).susceptible : ℝ) +
      (H (2 * n + 1)).vertices.card = (n : ℝ) + 1 := by exact_mod_cast hterminal
  have hcards : ((H n).vertices.card : ℝ) ≤ (H (2 * n + 1)).vertices.card := by
    exact_mod_cast Finset.card_le_card hgeometry.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hhalfn : delta * (n : ℝ) ≤ (n : ℝ) / 2 := by
    have hh := mul_le_mul_of_nonneg_right hd1 hnR.le
    linarith
  have hB : (n : ℝ) / 2 ≤ (H (2 * n + 1)).vertices.card := by linarith
  have hBpos : (0 : ℝ) < (H (2 * n + 1)).vertices.card := (half_pos hnR).trans_le hB
  have hscaled := mul_le_mul_of_nonneg_left hB (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd0)
  have hlast : (0 : ℝ) ≤ (wordCountsAt n w (2 * n + 1)).susceptible := by positivity
  apply (div_le_iff₀ hBpos).mpr
  nlinarith

theorem measure_le_add_of_real_le {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (A : Set α)
    {r : ℝ} (hr : 0 ≤ r) (h : μ.real A ≤ ν.real A + r) :
    μ A ≤ ν A + ENNReal.ofReal r := by
  calc
    _ = ENNReal.ofReal (μ.real A) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (ν.real A + r) := ENNReal.ofReal_le_ofReal h
    _ = _ := by
      rw [ENNReal.ofReal_add (show 0 ≤ ν.real A from measureReal_nonneg) hr, Measure.real,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem forward_pair_kernel_probability_of_nonempty (s : Forward.State)
    (hs : s.vertices.Nonempty) : IsProbabilityMeasure (CanonicalTree.forwardPairKernel s) := by
  have := Forward.uniform_vertices_probability s hs
  unfold CanonicalTree.forwardPairKernel
  exact isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
    (Eventually.of_forall fun _ => Measure.isProbabilityMeasure_map_iff
      (measurable_of_countable _).aemeasurable |>.mpr inferInstance)

theorem forward_sampling_event_lintegral {α : Type*} [MeasurableSpace α]
    (x : SignSequence) (k : ℕ) (K : Forward.State → Measure α) (A : Set α)
    (hA : MeasurableSet A) :
    ((Forward.treeLaw x k).bind K) A =
      ∫⁻ H, K (H k) A ∂ForwardInfiniteHistory.fullLaw x := by
  have hm : Measurable (fun H : ForwardInfiniteHistory.History => K (H k)) :=
    measurable_from_top.comp (measurable_pi_apply k)
  rw [← ForwardInfiniteHistory.map_eval,
    Measure.bind_map (measurable_pi_apply k).aemeasurable measurable_from_top.aemeasurable]
  exact Measure.bind_apply hA hm.aemeasurable

theorem terminal_word_uniform_samples_bound (n : ℕ) (hn : 0 < n)
    (w : Fin (2 * n + 1) → Bool) (hw : SignWordFeasible n w)
    {delta : ℝ} (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1 / 2)
    (hU : ((wordCountsAt n w n).susceptible : ℝ) ≤ delta * n)
    (A : Set ℕ) (B : Set (ℕ × ℕ × ℕ)) :
    Forward.uniformHeightLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1) A ≤
        Forward.uniformHeightLaw (ForwardAnnealed.wordSchedule w) n A + ENNReal.ofReal (4 * delta) ∧
    CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1) B ≤
        CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule w) n B +
          ENNReal.ofReal (4 * delta) := by
  have hevent : ∀ᵐ H ∂ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w),
      Forward.vertexHeightKernel (H (2 * n + 1)) A ≤
        Forward.vertexHeightKernel (H n) A + ENNReal.ofReal (4 * delta) ∧
      CanonicalTree.forwardPairKernel (H (2 * n + 1)) B ≤
        CanonicalTree.forwardPairKernel (H n) B + ENNReal.ofReal (4 * delta) := by
    filter_upwards [terminal_word_later_vertex_fraction n hn w hw hd0 hd1 hU,
      ForwardInfiniteHistory.fullLaw_uniform_samples_restriction_bound
        (ForwardAnnealed.wordSchedule w) n (2 * n + 1) (by omega) A B,
      ForwardInfiniteHistory.fullLaw_valid (ForwardAnnealed.wordSchedule w)] with H hf hr hv
    have := forward_pair_kernel_probability_of_nonempty (H n) ⟨0, (hv n).root_mem⟩
    have := forward_pair_kernel_probability_of_nonempty (H (2 * n + 1)) ⟨0, (hv _).root_mem⟩
    constructor
    · apply measure_le_add_of_real_le _ _ A (by positivity)
      have hh := le_abs_self ((Forward.vertexHeightKernel (H (2 * n + 1))).real A -
        (Forward.vertexHeightKernel (H n)).real A)
      nlinarith [hr.1]
    · apply measure_le_add_of_real_le _ _ B (by positivity)
      have hh := le_abs_self ((CanonicalTree.forwardPairKernel (H (2 * n + 1))).real B -
        (CanonicalTree.forwardPairKernel (H n)).real B)
      nlinarith [hr.2]
  constructor
  · rw [Forward.uniformHeightLaw, forward_sampling_event_lintegral _ _ _ A (Set.to_countable _).measurableSet,
      Forward.uniformHeightLaw, forward_sampling_event_lintegral _ _ _ A (Set.to_countable _).measurableSet]
    calc
      _ ≤ ∫⁻ H, Forward.vertexHeightKernel (H n) A + ENNReal.ofReal (4 * delta)
          ∂ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w) :=
        lintegral_mono_ae (hevent.mono fun _ h => h.1)
      _ = _ := by rw [lintegral_add_right _ measurable_const]; simp
  · rw [CanonicalTree.forwardPairDataLaw,
      forward_sampling_event_lintegral _ _ _ B (Set.to_countable _).measurableSet,
      CanonicalTree.forwardPairDataLaw,
      forward_sampling_event_lintegral _ _ _ B (Set.to_countable _).measurableSet]
    calc
      _ ≤ ∫⁻ H, CanonicalTree.forwardPairKernel (H n) B + ENNReal.ofReal (4 * delta)
          ∂ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w) :=
        lintegral_mono_ae (hevent.mono fun _ h => h.2)
      _ = _ := by rw [lintegral_add_right _ measurable_const]; simp

end Freezing1.SIR
