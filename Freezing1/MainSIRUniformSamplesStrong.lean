module

public import Freezing1.SIRRandomEnvironmentTransferSampling

/-!
# Strong-regime terminal SIR uniform height and pair distance

The proof averages original fixed-word restriction bounds with the actual
adaptive terminal-word measure. Only a vanishing fraction of vertices is
added after population time. Both complete terminal sampling laws retain
all vertices, and the pair law retains conditional independence and equality.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory RandomEnvironment
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem sirUniformHeightLaw_word_mixture (rate : ℝ≥0) (n k : ℕ) :
    sirUniformHeightLaw rate n k = (signWordLaw rate n k).bind
      (fun w => Forward.uniformHeightLaw (ForwardAnnealed.wordSchedule w) k) := by
  rw [sirUniformHeightLaw, treeFullLaw_plane_original_word_mixture,
    Measure.bind_bind (measurable_of_countable _).aemeasurable PlaneForward.vertexHeightKernel.aemeasurable]
  apply Measure.bind_congr_right
  apply Eventually.of_forall
  intro w
  change ((Forward.treeLaw (ForwardAnnealed.wordSchedule w) k).map Forward.State.toPlaneState).bind
    PlaneForward.vertexHeightKernel = Forward.uniformHeightLaw (ForwardAnnealed.wordSchedule w) k
  rw [Measure.bind_map Forward.measurable_toPlaneState.aemeasurable
    PlaneForward.vertexHeightKernel.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [Forward.treeLaw_valid (ForwardAnnealed.wordSchedule w) k] with s hs
  exact hs.toPlaneState_vertexHeightKernel

theorem sirPairDataLaw_word_mixture (rate : ℝ≥0) (n k : ℕ) :
    sirPairDataLaw rate n k = (signWordLaw rate n k).bind
      (fun w => CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule w) k) := by
  rw [sirPairDataLaw, treeFullLaw_plane_original_word_mixture,
    Measure.bind_bind (measurable_of_countable _).aemeasurable PlaneForward.pairDataKernel.aemeasurable]
  congr 1
  funext w
  exact Forward.planePairDataLaw_fixed _ _

theorem longer_word_height_mixture (rate : ℝ≥0) (n K k : ℕ) (hk : k ≤ K) :
    (signWordLaw rate n K).bind (fun w => Forward.uniformHeightLaw (ForwardAnnealed.wordSchedule w) k) =
      sirUniformHeightLaw rate n k := by
  calc
    _ = ((signWordLaw rate n K).bind
        (fun w => Forward.treeLaw (ForwardAnnealed.wordSchedule w) k)).bind Forward.vertexHeightKernel := by
      rw [Measure.bind_bind (measurable_of_countable _).aemeasurable Forward.vertexHeightKernel.aemeasurable]
      rfl
    _ = ((signWordLaw rate n k).bind
        (fun w => Forward.treeLaw (ForwardAnnealed.wordSchedule w) k)).bind Forward.vertexHeightKernel := by
      rw [original_tree_mixture_of_longer_word rate n K k hk]
    _ = _ := by
      rw [Measure.bind_bind (measurable_of_countable _).aemeasurable Forward.vertexHeightKernel.aemeasurable,
        sirUniformHeightLaw_word_mixture]
      rfl

theorem longer_word_pair_mixture (rate : ℝ≥0) (n K k : ℕ) (hk : k ≤ K) :
    (signWordLaw rate n K).bind (fun w => CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule w) k) =
      sirPairDataLaw rate n k := by
  calc
    _ = ((signWordLaw rate n K).bind
        (fun w => Forward.treeLaw (ForwardAnnealed.wordSchedule w) k)).bind CanonicalTree.forwardPairKernel := by
      rw [Measure.bind_bind (measurable_of_countable _).aemeasurable measurable_from_top.aemeasurable]
      rfl
    _ = ((signWordLaw rate n k).bind
        (fun w => Forward.treeLaw (ForwardAnnealed.wordSchedule w) k)).bind CanonicalTree.forwardPairKernel := by
      rw [original_tree_mixture_of_longer_word rate n K k hk]
    _ = _ := by
      rw [Measure.bind_bind (measurable_of_countable _).aemeasurable measurable_from_top.aemeasurable,
        sirPairDataLaw_word_mixture]
      rfl

theorem signWordLaw_wordCountsAt_susceptible_event_eq (rate : ℝ≥0) (n K i : ℕ)
    (hi : i ≤ K) (A : Set ℕ) :
    signWordLaw rate n K {w | (wordCountsAt n w i).susceptible ∈ A} =
      countsFullLaw rate n {H | (H i).susceptible ∈ A} := by
  have hh := signWordLaw_countsPrefix_event_eq rate n K
    {q | (q ⟨i, Finset.mem_Iic.mpr hi⟩).susceptible ∈ A}
  change signWordLaw rate n K {w | (countsPrefixWord n w ⟨i, Finset.mem_Iic.mpr hi⟩).susceptible ∈ A} =
    countsFullLaw rate n {H | (H i).susceptible ∈ A} at hh
  simpa only [wordCountsAt, dite_eq_left hi] using hh

theorem terminal_word_large_susceptible_tendsto_zero (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {delta : ℝ} (hd : 0 < delta) :
    Tendsto (fun n => signWordLaw (rate n) n (2 * n + 1)
      {w | delta * n < (wordCountsAt n w n).susceptible}) atTop (nhds 0) := by
  have hh := (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).mp
    (countsFullLaw_susceptible_at_population_tendsto_zero rate hstrong hd)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh (fun _ => bot_le)
  intro n
  change signWordLaw (rate n) n (2 * n + 1) {w | delta * n < (wordCountsAt n w n).susceptible} ≤
    countsFullLaw (rate n) n {H | delta * n ≤ (H n).susceptible}
  have heq := signWordLaw_wordCountsAt_susceptible_event_eq (rate n) n (2 * n + 1) n
    (by omega) {u | delta * n < (u : ℝ)}
  change signWordLaw (rate n) n (2 * n + 1) {w | delta * n < (wordCountsAt n w n).susceptible} =
    countsFullLaw (rate n) n {H | delta * n < (H n).susceptible} at heq
  rw [heq]
  apply measure_mono
  intro H h
  change delta * n < (H n).susceptible at h
  change delta * n ≤ (H n).susceptible
  exact h.le

theorem lintegral_le_add_small_bad {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f g : α → ℝ≥0∞)
    (hbound : ∀ a, f a ≤ 1) (B : Set α) (hB : MeasurableSet B) (e : ℝ≥0∞)
    (hgood : ∀ a ∉ B, f a ≤ g a + e) :
    ∫⁻ a, f a ∂μ ≤ (∫⁻ a, g a ∂μ) + e + μ B := by
  calc
    _ = (∫⁻ a in Bᶜ, f a ∂μ) + ∫⁻ a in B, f a ∂μ := by
      simpa only [compl_compl] using (lintegral_add_compl f hB.compl).symm
    _ ≤ (∫⁻ a in Bᶜ, g a + e ∂μ) + μ B := by
      exact add_le_add (setLIntegral_mono' hB.compl (fun a ha => hgood a ha))
        ((lintegral_mono hbound).trans_eq (setLIntegral_one _))
    _ = (∫⁻ a in Bᶜ, g a ∂μ) + e * μ Bᶜ + μ B := by
      rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ _ := add_le_add (add_le_add (setLIntegral_le_lintegral _ _)
      (mul_le_of_le_one_right' prob_le_one)) (le_refl _)

/-- Averaging a genuine fixed-word prefix-capture estimate pays only the
actual probability of remaining susceptible mass. -/
theorem strong_terminal_average_tendsto_zero (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    (F G : (n : ℕ) → (Fin (2 * n + 1) → Bool) → ℝ≥0∞)
    (hF : ∀ n w, F n w ≤ 1)
    (hprefix : Tendsto (fun n => ∫⁻ w, G n w ∂signWordLaw (rate n) n (2 * n + 1)) atTop (nhds 0))
    (hcompare : ∀ n, 0 < n → ∀ w, SignWordFeasible n w → ∀ delta : ℝ,
      0 < delta → delta ≤ 1 / 2 → ((wordCountsAt n w n).susceptible : ℝ) ≤ delta * n →
        F n w ≤ G n w + ENNReal.ofReal (4 * delta)) :
    Tendsto (fun n => ∫⁻ w, F n w ∂signWordLaw (rate n) n (2 * n + 1)) atTop (nhds 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro eps heps
  obtain ⟨eta, heta, hsmall⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := (5 : ℝ≥0∞)) (b := eps) (by norm_num) heps.ne'
  have hetaR : (0 : ℝ) < eta := by exact_mod_cast heta
  let delta : ℝ := min (1 / 4) (eta : ℝ)
  have hd : 0 < delta := lt_min (by norm_num) hetaR
  have hd1 : delta ≤ 1 / 2 := (min_le_left _ _).trans (by norm_num)
  have hdeta : delta ≤ eta := min_le_right _ _
  let B : (n : ℕ) → Set (Fin (2 * n + 1) → Bool) := fun n =>
    {w | ¬SignWordFeasible n w} ∪ {w | delta * n < (wordCountsAt n w n).susceptible}
  have hbad : Tendsto (fun n => signWordLaw (rate n) n (2 * n + 1) (B n)) atTop (nhds 0) := by
    have hzero (n : ℕ) : signWordLaw (rate n) n (2 * n + 1) {w | ¬SignWordFeasible n w} = 0 :=
      (ae_iff.mp (signWordLaw_feasible (rate n) n (2 * n + 1)))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (terminal_word_large_susceptible_tendsto_zero rate hstrong hd) (fun _ => bot_le)
    intro n
    exact (measure_union_le _ _).trans_eq (by rw [hzero n, zero_add])
  have hsum := hprefix.add hbad
  simp only [add_zero] at hsum
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    (ENNReal.tendsto_nhds_zero.mp hsum) (eta : ℝ≥0∞) (by exact_mod_cast heta)] with n hn hsum
  have hbound := lintegral_le_add_small_bad (signWordLaw (rate n) n (2 * n + 1))
    (F n) (G n) (hF n) (B n) (Set.to_countable _).measurableSet (ENNReal.ofReal (4 * delta))
    (fun w hw => by
      have hf : SignWordFeasible n w := by by_contra h; exact hw (Or.inl h)
      have hU : ((wordCountsAt n w n).susceptible : ℝ) ≤ delta * n := by
        by_contra h
        exact hw (Or.inr (lt_of_not_ge h))
      exact hcompare n hn w hf delta hd hd1 hU)
  have hconst : ENNReal.ofReal (4 * delta) ≤ 4 * (eta : ℝ≥0∞) := by
    calc
      _ ≤ ENNReal.ofReal (4 * (eta : ℝ)) := ENNReal.ofReal_le_ofReal (by nlinarith)
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_coe_nnreal]; norm_num
  calc
    _ ≤ (∫⁻ w, G n w ∂signWordLaw (rate n) n (2 * n + 1)) +
        ENNReal.ofReal (4 * delta) + signWordLaw (rate n) n (2 * n + 1) (B n) := hbound
    _ = ((∫⁻ w, G n w ∂signWordLaw (rate n) n (2 * n + 1)) +
        signWordLaw (rate n) n (2 * n + 1) (B n)) + ENNReal.ofReal (4 * delta) := by ac_rfl
    _ ≤ (eta : ℝ≥0∞) + 4 * eta := add_le_add hsum hconst
    _ = (eta : ℝ≥0∞) * 5 := by ring
    _ ≤ eps := hsmall.le

/-- The height of a conditionally uniform vertex of the complete terminal
embedded SIR tree converges in probability to `log n`. -/
theorem sir_terminal_uniform_height_tendsto (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => sirUniformHeightLaw (rate n) n (2 * n + 1)
      {h | eps ≤ |(h : ℝ) / Real.log (n : ℝ) - 1|}) atTop (nhds 0) := by
  let A : ℕ → Set ℕ := fun n => {h | eps ≤ |(h : ℝ) / Real.log (n : ℝ) - 1|}
  have hprefix : Tendsto (fun n => ∫⁻ w,
      Forward.uniformHeightLaw (ForwardAnnealed.wordSchedule w) n (A n)
        ∂signWordLaw (rate n) n (2 * n + 1)) atTop (nhds 0) := by
    convert sir_time_n_uniform_height_tendsto rate hstrong heps using 1
    funext n
    rw [← longer_word_height_mixture (rate n) n (2 * n + 1) n (by omega),
      Measure.bind_apply (Set.to_countable _).measurableSet (measurable_of_countable _).aemeasurable]
  have hh := strong_terminal_average_tendsto_zero rate hstrong
    (fun n w => Forward.uniformHeightLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1) (A n))
    (fun n w => Forward.uniformHeightLaw (ForwardAnnealed.wordSchedule w) n (A n))
    (fun _ _ => prob_le_one) hprefix (fun n hn w hw d hd hd1 hU =>
      (terminal_word_uniform_samples_bound n hn w hw hd.le hd1 hU (A n) ∅).1)
  convert hh using 1
  funext n
  rw [sirUniformHeightLaw_word_mixture,
    Measure.bind_apply (Set.to_countable _).measurableSet (measurable_of_countable _).aemeasurable]

/-- Two conditionally independent uniform vertices of the complete
terminal tree have distance asymptotic to `2 * log n`. The diagonal is
included in this actual pair law. -/
theorem sir_terminal_uniform_distance_tendsto (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => sirPairDataLaw (rate n) n (2 * n + 1)
      {z | eps ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - 2|}) atTop (nhds 0) := by
  let A : ℕ → Set (ℕ × ℕ × ℕ) := fun n => {z | eps ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - 2|}
  have hprefix : Tendsto (fun n => ∫⁻ w,
      CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule w) n (A n)
        ∂signWordLaw (rate n) n (2 * n + 1)) atTop (nhds 0) := by
    convert sir_time_n_uniform_distance_tendsto rate hstrong heps using 1
    funext n
    rw [← longer_word_pair_mixture (rate n) n (2 * n + 1) n (by omega),
      Measure.bind_apply (Set.to_countable _).measurableSet (measurable_of_countable _).aemeasurable]
  have hbound (n : ℕ) (w : Fin (2 * n + 1) → Bool) :
      CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1) (A n) ≤ 1 := by
    have := original_pair_probability (ForwardAnnealed.wordSchedule w) (2 * n + 1)
    exact prob_le_one
  have hh := strong_terminal_average_tendsto_zero rate hstrong
    (fun n w => CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1) (A n))
    (fun n w => CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule w) n (A n))
    hbound hprefix (fun n hn w hw d hd hd1 hU =>
      (terminal_word_uniform_samples_bound n hn w hw hd.le hd1 hU ∅ (A n)).2)
  convert hh using 1
  funext n
  rw [sirPairDataLaw_word_mixture,
    Measure.bind_apply (Set.to_countable _).measurableSet (measurable_of_countable _).aemeasurable]

end Freezing1.SIR
