module

public import Freezing1.SIRFiniteRateEnvironmentTransfer
public import Freezing1.SIRGeometryRescale
public import Freezing1.SIRTreePrefixWordObservations
public import Freezing1.SIRSurvivalGateComparison

/-!
# Uniform samples in a surviving finite-rate SIR prefix

The deterministic linear theorem is averaged over the actual adaptive
environment. A fixed positive prefix before the fluid zero has the source
height and distance constants on its genuine survival event.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory RandomEnvironment CountableMarkovChain
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

theorem planeWordLaw_uniformHeightLaw {k : ℕ} (w : Fin k → Bool) :
    (planeWordLaw w).bind PlaneForward.vertexHeightKernel =
      Forward.uniformHeightLaw (ForwardAnnealed.wordSchedule w) k := by
  rw [← map_fixedWord_treeLaw_to_planeWordLaw,
    Measure.bind_map Forward.measurable_toPlaneState.aemeasurable
      PlaneForward.vertexHeightKernel.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [Forward.treeLaw_valid (ForwardAnnealed.wordSchedule w) k] with s hs
  exact hs.toPlaneState_vertexHeightKernel

theorem planeWordLaw_pairDataLaw {k : ℕ} (w : Fin k → Bool) :
    (planeWordLaw w).bind PlaneForward.pairDataKernel =
      CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule w) k := by
  rw [← map_fixedWord_treeLaw_to_planeWordLaw]
  exact Forward.planePairDataLaw_fixed _ _

theorem lintegral_treeFullLaw_gated_height_word (rate : ℝ≥0) (n k a : ℕ) (ha : a ≤ k)
    (A : Set ℕ) :
    (∫⁻ H, if 0 < (H a).counts.infectious then
      PlaneForward.vertexHeightKernel (H k).tree A else 0 ∂treeFullLaw rate n) =
      ∫⁻ w, if 0 < (wordCountsAt n w a).infectious then
        Forward.uniformHeightLaw (ForwardAnnealed.wordSchedule w) k A else 0
        ∂signWordLaw rate n k := by
  have hh := lintegral_treeFullLaw_countsPrefix_tree rate n k
    (fun z => if 0 < (z.1 ⟨a, Finset.mem_Iic.mpr ha⟩).infectious then
      PlaneForward.vertexHeightKernel z.2 A else 0)
  calc
    _ = ∫⁻ w, ∫⁻ s, if 0 < (countsPrefixWord n w ⟨a, Finset.mem_Iic.mpr ha⟩).infectious then
        PlaneForward.vertexHeightKernel s A else 0 ∂planeWordLaw w ∂signWordLaw rate n k := hh
    _ = _ := by
      apply lintegral_congr
      intro w
      simp only [wordCountsAt, dite_eq_left ha]
      split_ifs
      · rw [← planeWordLaw_uniformHeightLaw]
        exact (Measure.bind_apply (Set.to_countable A).measurableSet
          PlaneForward.vertexHeightKernel.aemeasurable).symm
      · simp only [lintegral_zero]

theorem lintegral_treeFullLaw_gated_pair_word (rate : ℝ≥0) (n k a : ℕ) (ha : a ≤ k)
    (A : Set (ℕ × ℕ × ℕ)) :
    (∫⁻ H, if 0 < (H a).counts.infectious then
      PlaneForward.pairDataKernel (H k).tree A else 0 ∂treeFullLaw rate n) =
      ∫⁻ w, if 0 < (wordCountsAt n w a).infectious then
        CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule w) k A else 0
        ∂signWordLaw rate n k := by
  have hh := lintegral_treeFullLaw_countsPrefix_tree rate n k
    (fun z => if 0 < (z.1 ⟨a, Finset.mem_Iic.mpr ha⟩).infectious then
      PlaneForward.pairDataKernel z.2 A else 0)
  calc
    _ = ∫⁻ w, ∫⁻ s, if 0 < (countsPrefixWord n w ⟨a, Finset.mem_Iic.mpr ha⟩).infectious then
        PlaneForward.pairDataKernel s A else 0 ∂planeWordLaw w ∂signWordLaw rate n k := hh
    _ = _ := by
      apply lintegral_congr
      intro w
      simp only [wordCountsAt, dite_eq_left ha]
      split_ifs
      · rw [← planeWordLaw_pairDataLaw]
        exact (Measure.bind_apply (Set.to_countable A).measurableSet
          PlaneForward.pairDataKernel.aemeasurable).symm
      · simp only [lintegral_zero]

theorem word_average_alive_tendsto_of_two_stage (rate : ℕ → ℝ≥0) {t : ℝ} (ht : 0 < t)
    (score : ℕ → SignSequence → ℝ≥0∞)
    (hstage : ∀ eta > 0, ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta ∈ Ioc (0 : ℝ) delta0,
      ∀ᶠ n in atTop, (∫⁻ w,
        if 0 < (wordCountsAt n w ⌊delta * (n : ℝ)⌋₊).infectious then
          score ⌊t * (n : ℝ)⌋₊ (ForwardAnnealed.wordSchedule w) else 0
        ∂signWordLaw (rate n) n ⌊t * (n : ℝ)⌋₊) < ENNReal.ofReal eta) :
    Tendsto (fun n => ∫⁻ w,
      if 0 < (countsRunWord n w).infectious then
        score ⌊t * (n : ℝ)⌋₊ (ForwardAnnealed.wordSchedule w) else 0
      ∂signWordLaw (rate n) n ⌊t * (n : ℝ)⌋₊) atTop (nhds 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro e he
  obtain ⟨eta, heta, hetae⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := (1 : ℝ≥0∞)) (b := e) (by norm_num) he.ne'
  have hetaR : (0 : ℝ) < eta := by exact_mod_cast heta
  obtain ⟨d0, hd0, hdelta⟩ := hstage (eta : ℝ) hetaR
  let d : ℝ := min d0 (t / 2)
  have hd : 0 < d := lt_min hd0 (half_pos ht)
  have hdt : d ≤ t := (min_le_right _ _).trans (by linarith)
  filter_upwards [hdelta d ⟨hd, min_le_left _ _⟩] with n hn
  have ham : ⌊d * (n : ℝ)⌋₊ ≤ ⌊t * (n : ℝ)⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_right hdt (Nat.cast_nonneg n))
  have hle : (∫⁻ w, if 0 < (countsRunWord n w).infectious then
      score ⌊t * (n : ℝ)⌋₊ (ForwardAnnealed.wordSchedule w) else 0
      ∂signWordLaw (rate n) n ⌊t * (n : ℝ)⌋₊) ≤
      ∫⁻ w, if 0 < (wordCountsAt n w ⌊d * (n : ℝ)⌋₊).infectious then
        score ⌊t * (n : ℝ)⌋₊ (ForwardAnnealed.wordSchedule w) else 0
        ∂signWordLaw (rate n) n ⌊t * (n : ℝ)⌋₊ := by
    apply lintegral_mono_ae
    filter_upwards [signWordLaw_feasible (rate n) n ⌊t * (n : ℝ)⌋₊] with w hw
    by_cases halive : 0 < (countsRunWord n w).infectious
    · have hp := feasible_alive_wordCountsAt n w hw le_rfl
        (by simpa only [wordCountsAt_last] using halive)
      have hprev : 0 < (wordCountsAt n w ⌊d * (n : ℝ)⌋₊).infectious := by
        have hh : (0 : ℤ) < ((wordCountsAt n w ⌊d * (n : ℝ)⌋₊).infectious : ℤ) := by
          rw [hp.2 _ ham]
          exact hp.1 _ ham
        exact_mod_cast hh
      simp only [ite_eq_left halive, ite_eq_left hprev, le_refl]
    · simp only [ite_eq_right halive]
      exact bot_le
  have heq : ENNReal.ofReal (eta : ℝ) = (eta : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
  exact (hle.trans_lt hn).le.trans (by simpa only [heq, mul_one] using hetae.le)

theorem finiteRate_height_constant {lam : ℝ} (hlam : 1 < lam) :
    ((((lam - 1) / (lam + 1)) + 1) / (2 * ((lam - 1) / (lam + 1)))) = lam / (lam - 1) := by
  have h1 : lam - 1 ≠ 0 := by linarith
  have h2 : lam + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem finiteRate_distance_constant {lam : ℝ} (hlam : 1 < lam) :
    ((((lam - 1) / (lam + 1)) + 1) / ((lam - 1) / (lam + 1))) = 2 * lam / (lam - 1) := by
  have h1 : lam - 1 ≠ 0 := by linarith
  have h2 : lam + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem sir_prefix_alive_uniform_height_horizon_log_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    {t eps : ℝ} (ht : 0 < t) (htt : t < fluidExtinctionTime lam) (heps : 0 < eps) :
    Tendsto (fun n => ∫⁻ H, if 0 < (H ⌊t * (n : ℝ)⌋₊).counts.infectious then
      PlaneForward.vertexHeightKernel (H ⌊t * (n : ℝ)⌋₊).tree
        {h | eps ≤ |(h : ℝ) / Real.log (⌊t * (n : ℝ)⌋₊ : ℝ) - (lam : ℝ) / ((lam : ℝ) - 1)|}
      else 0 ∂treeFullLaw (rate n) n) atTop (nhds 0) := by
  let c : ℝ := ((lam : ℝ) - 1) / ((lam : ℝ) + 1)
  have hc : 0 < c := div_pos (by linarith) (by linarith)
  have hc1 : c ≤ 1 := (div_le_one (by linarith : 0 < (lam : ℝ) + 1)).mpr (by linarith)
  have hh := word_average_alive_tendsto_of_two_stage rate ht
    (fun m x => Forward.uniformHeightLaw x m
      {h | eps ≤ |(h : ℝ) / Real.log (m : ℝ) - (lam : ℝ) / ((lam : ℝ) - 1)|})
    (fun eta heta => finiteRate_average_score_two_stage rate lam hlam hrate
      logLogStartupCutoff logLogStartupCutoff_tendsto ht htt
      (fun m x => Forward.uniformHeightLaw x m
        {h | eps ≤ |(h : ℝ) / Real.log (m : ℝ) - (lam : ℝ) / ((lam : ℝ) - 1)|})
      (fun _ _ => prob_le_one)
      (fun window floor hw hf eta' heta' => by
        simpa only [Measure.real, c, finiteRate_height_constant hlam] using
          uniform_nearBulk_height_bound logLogStartupCutoff logLogStartupCutoff_tendsto
            logLogStartupCutoff_sublog hc hc1 heps heta' window floor hw hf) heta)
  convert hh using 1
  funext n
  rw [lintegral_treeFullLaw_gated_height_word _ _ _ _ le_rfl]
  simp only [wordCountsAt_last]

theorem sir_prefix_alive_uniform_distance_horizon_log_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    {t eps : ℝ} (ht : 0 < t) (htt : t < fluidExtinctionTime lam) (heps : 0 < eps) :
    Tendsto (fun n => ∫⁻ H, if 0 < (H ⌊t * (n : ℝ)⌋₊).counts.infectious then
      PlaneForward.pairDataKernel (H ⌊t * (n : ℝ)⌋₊).tree
        {z | eps ≤ |(z.2.2 : ℝ) / Real.log (⌊t * (n : ℝ)⌋₊ : ℝ) - 2 * (lam : ℝ) / ((lam : ℝ) - 1)|}
      else 0 ∂treeFullLaw (rate n) n) atTop (nhds 0) := by
  let c : ℝ := ((lam : ℝ) - 1) / ((lam : ℝ) + 1)
  have hc : 0 < c := div_pos (by linarith) (by linarith)
  have hc1 : c ≤ 1 := (div_le_one (by linarith : 0 < (lam : ℝ) + 1)).mpr (by linarith)
  have hbound (m : ℕ) (x : SignSequence) : CanonicalTree.forwardPairDataLaw x m
      {z | eps ≤ |(z.2.2 : ℝ) / Real.log (m : ℝ) - 2 * (lam : ℝ) / ((lam : ℝ) - 1)|} ≤ 1 := by
    have := original_pair_probability x m
    exact prob_le_one
  have hh := word_average_alive_tendsto_of_two_stage rate ht
    (fun m x => CanonicalTree.forwardPairDataLaw x m
      {z | eps ≤ |(z.2.2 : ℝ) / Real.log (m : ℝ) - 2 * (lam : ℝ) / ((lam : ℝ) - 1)|})
    (fun eta heta => finiteRate_average_score_two_stage rate lam hlam hrate
      logLogStartupCutoff logLogStartupCutoff_tendsto ht htt
      (fun m x => CanonicalTree.forwardPairDataLaw x m
        {z | eps ≤ |(z.2.2 : ℝ) / Real.log (m : ℝ) - 2 * (lam : ℝ) / ((lam : ℝ) - 1)|}) hbound
      (fun window floor hw hf eta' heta' => by
        simpa only [Measure.real, c, finiteRate_distance_constant hlam] using
          uniform_nearBulk_distance_bound logLogStartupCutoff logLogStartupCutoff_tendsto
            logLogStartupCutoff_sublog hc hc1 heps heta' window floor hw hf) heta)
  convert hh using 1
  funext n
  rw [lintegral_treeFullLaw_gated_pair_word _ _ _ _ le_rfl]
  simp only [wordCountsAt_last]

theorem sir_prefix_alive_uniform_height_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    {t eps : ℝ} (ht : 0 < t) (htt : t < fluidExtinctionTime lam) (heps : 0 < eps) :
    Tendsto (fun n => ∫⁻ H, if 0 < (H ⌊t * (n : ℝ)⌋₊).counts.infectious then
      PlaneForward.vertexHeightKernel (H ⌊t * (n : ℝ)⌋₊).tree
        {h | eps ≤ |(h : ℝ) / Real.log (n : ℝ) - (lam : ℝ) / ((lam : ℝ) - 1)|}
      else 0 ∂treeFullLaw (rate n) n) atTop (nhds 0) := by
  have hh := sir_prefix_alive_uniform_height_horizon_log_tendsto rate lam hlam hrate ht htt
    (by positivity : 0 < eps / 4)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [eventually_log_prefix_rescale_subset (c := (lam : ℝ) / ((lam : ℝ) - 1)) ht heps]
    with n hn
  apply lintegral_mono
  intro H
  dsimp only
  split_ifs
  · apply measure_mono
    intro h hbad
    exact hn hbad
  · exact le_rfl

theorem sir_prefix_alive_uniform_distance_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    {t eps : ℝ} (ht : 0 < t) (htt : t < fluidExtinctionTime lam) (heps : 0 < eps) :
    Tendsto (fun n => ∫⁻ H, if 0 < (H ⌊t * (n : ℝ)⌋₊).counts.infectious then
      PlaneForward.pairDataKernel (H ⌊t * (n : ℝ)⌋₊).tree
        {z | eps ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - 2 * (lam : ℝ) / ((lam : ℝ) - 1)|}
      else 0 ∂treeFullLaw (rate n) n) atTop (nhds 0) := by
  have hh := sir_prefix_alive_uniform_distance_horizon_log_tendsto rate lam hlam hrate ht htt
    (by positivity : 0 < eps / 4)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [eventually_log_prefix_rescale_subset
    (c := 2 * (lam : ℝ) / ((lam : ℝ) - 1)) ht heps] with n hn
  apply lintegral_mono
  intro H
  dsimp only
  split_ifs
  · apply measure_mono
    intro z hbad
    exact hn hbad
  · exact le_rfl

theorem gated_lintegral_le_add_mismatch {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) (hf : ∀ a, f a ≤ 1)
    (G H : α → Prop) (hmeas : MeasurableSet {a | G a ∧ ¬H a}) :
    (∫⁻ a, if G a then f a else 0 ∂μ) ≤
      (∫⁻ a, if H a then f a else 0 ∂μ) + μ {a | G a ∧ ¬H a} := by
  have hh := lintegral_le_add_small_bad μ
    (fun a => if G a then f a else 0) (fun a => if H a then f a else 0)
    (fun a => by split_ifs; exact hf a; exact bot_le)
    {a | G a ∧ ¬H a} hmeas 0 (fun a ha => by
      by_cases hG : G a
      · have hH : H a := by by_contra h; exact ha ⟨hG, h⟩
        simp only [ite_eq_left hG, ite_eq_left hH, add_zero, le_refl]
      · simp only [ite_eq_right hG]
        exact bot_le)
  simpa only [add_zero] using hh

theorem treeFullLaw_sublinear_preFluid_gate_mismatch_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (nhds 0))
    {t : ℝ} (ht : 0 < t) (htt : t < fluidExtinctionTime lam) :
    Tendsto (fun n => treeFullLaw (rate n) n
      {H | 0 < (H (cutoff n)).counts.infectious ∧
        ¬0 < (H ⌊t * (n : ℝ)⌋₊).counts.infectious}) atTop (nhds 0) := by
  have hh := (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).mp
    (countsFullLaw_sublinear_preFluid_gate_mismatch rate lam hlam hrate cutoff hcutoff hsmall ht htt)
  convert hh using 1
  funext n
  rw [← map_treeFullLaw_counts, Measure.map_apply (by fun_prop) (by measurability)]
  congr 1
  ext H
  simp only [mem_ofPred_eq, mem_preimage, mul_comm (n : ℝ) t, not_lt, Nat.le_zero]

theorem sir_sublinear_gate_prefix_uniform_height_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (nhds 0))
    {t eps : ℝ} (ht : 0 < t) (htt : t < fluidExtinctionTime lam) (heps : 0 < eps) :
    Tendsto (fun n => ∫⁻ H, if 0 < (H (cutoff n)).counts.infectious then
      PlaneForward.vertexHeightKernel (H ⌊t * (n : ℝ)⌋₊).tree
        {h | eps ≤ |(h : ℝ) / Real.log (n : ℝ) - (lam : ℝ) / ((lam : ℝ) - 1)|}
      else 0 ∂treeFullLaw (rate n) n) atTop (nhds 0) := by
  have hh := (sir_prefix_alive_uniform_height_tendsto rate lam hlam hrate ht htt heps).add
    (treeFullLaw_sublinear_preFluid_gate_mismatch_tendsto rate lam hlam hrate cutoff hcutoff hsmall ht htt)
  simp only [add_zero] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh (fun _ => bot_le)
  intro n
  dsimp only
  convert gated_lintegral_le_add_mismatch (treeFullLaw (rate n) n)
    (fun H => PlaneForward.vertexHeightKernel (H ⌊t * (n : ℝ)⌋₊).tree
      {h | eps ≤ |(h : ℝ) / Real.log (n : ℝ) - (lam : ℝ) / ((lam : ℝ) - 1)|})
    (fun _ => prob_le_one)
    (fun H => 0 < (H (cutoff n)).counts.infectious)
    (fun H => 0 < (H ⌊t * (n : ℝ)⌋₊).counts.infectious) (by measurability) using 1
  · apply lintegral_congr
    intro H
    split_ifs <;> rfl
  · congr 1
    apply lintegral_congr
    intro H
    split_ifs <;> rfl

theorem sir_sublinear_gate_prefix_uniform_distance_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (nhds 0))
    {t eps : ℝ} (ht : 0 < t) (htt : t < fluidExtinctionTime lam) (heps : 0 < eps) :
    Tendsto (fun n => ∫⁻ H, if 0 < (H (cutoff n)).counts.infectious then
      PlaneForward.pairDataKernel (H ⌊t * (n : ℝ)⌋₊).tree
        {z | eps ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - 2 * (lam : ℝ) / ((lam : ℝ) - 1)|}
      else 0 ∂treeFullLaw (rate n) n) atTop (nhds 0) := by
  have hh := (sir_prefix_alive_uniform_distance_tendsto rate lam hlam hrate ht htt heps).add
    (treeFullLaw_sublinear_preFluid_gate_mismatch_tendsto rate lam hlam hrate cutoff hcutoff hsmall ht htt)
  simp only [add_zero] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh (fun _ => bot_le)
  intro n
  dsimp only
  convert gated_lintegral_le_add_mismatch (treeFullLaw (rate n) n)
    (fun H => PlaneForward.pairDataKernel (H ⌊t * (n : ℝ)⌋₊).tree
      {z | eps ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - 2 * (lam : ℝ) / ((lam : ℝ) - 1)|})
    (fun _ => prob_le_one)
    (fun H => 0 < (H (cutoff n)).counts.infectious)
    (fun H => 0 < (H ⌊t * (n : ℝ)⌋₊).counts.infectious) (by measurability) using 1
  · apply lintegral_congr
    intro H
    split_ifs <;> rfl
  · congr 1
    apply lintegral_congr
    intro H
    split_ifs <;> rfl

end Freezing1.SIR
