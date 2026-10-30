module

public import Freezing1.SIRRandomEnvironmentTransferCounts
public import Freezing1.SIRRandomEnvironmentTransferProfiles
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Averaging the deterministic linear theorem under actual SIR environments

The environment is sampled with the adaptive SIR word law. Uniform-vertex
sampling includes every vertex; uniform-pair sampling uses two independent
draws conditional on the same tree and retains the diagonal.
-/

@[expose] public section

namespace Freezing1.SIR.RandomEnvironment

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem lintegral_le_small_add_bad {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ≥0∞)
    (hbound : ∀ a, f a ≤ 1) (B : Set α) (hB : MeasurableSet B) (e : ℝ≥0∞)
    (hgood : ∀ a ∉ B, f a ≤ e) :
    ∫⁻ a, f a ∂μ ≤ e + μ B := by
  calc
    _ = (∫⁻ a in Bᶜ, f a ∂μ) + ∫⁻ a in B, f a ∂μ := by
      simpa only [compl_compl] using (lintegral_add_compl f hB.compl).symm
    _ ≤ e * μ Bᶜ + μ B := by
      apply add_le_add
      · exact (setLIntegral_mono' hB.compl (fun a ha => hgood a ha)).trans_eq (setLIntegral_const _ _)
      · exact (lintegral_mono hbound).trans_eq (setLIntegral_one _)
    _ ≤ _ := add_le_add (mul_le_of_le_one_right' prob_le_one) (le_refl _)

/-- A bounded conditional bad probability tends to zero after averaging
over genuine adaptive words, once its deterministic good-profile criterion
has been established. -/
theorem strong_average_score_tendsto_zero (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    (score : ℕ → SignSequence → ℝ≥0∞) (hscore : ∀ n x, score n x ≤ 1)
    (huniform : ∀ eta > 0, ∃ e > 0, ∃ N, ∀ n ≥ N, ∀ x,
      PositiveThrough x n → ProfileGood cutoff 1 n x e → (score n x).toReal < eta) :
    Tendsto (fun n => ∫⁻ w, score n (ForwardAnnealed.wordSchedule w)
      ∂signWordLaw (rate n) n n) atTop (nhds 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro eps heps
  obtain ⟨eta, heta, hsmall⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := (2 : ℝ≥0∞)) (b := eps) (by norm_num) heps.ne'
  have hetaR : (0 : ℝ) < eta := by exact_mod_cast heta
  obtain ⟨e, he, N, hN⟩ := huniform (eta : ℝ) hetaR
  let B : (n : ℕ) → Set (Fin n → Bool) := fun n =>
    {w | ¬RegularWord n w} ∪ {w | RegularWord n w ∧ ∃ i ≥ cutoff n, i ≤ n ∧
      e ≤ |(activeCount (ForwardAnnealed.wordSchedule w) i : ℝ) / i - 1|}
  have hbad : Tendsto (fun n => signWordLaw (rate n) n n (B n)) atTop (nhds 0) := by
    have hh := (signWordLaw_not_regular_tendsto_zero rate hstrong).add
      (signWordLaw_strong_regular_profile_tendsto_zero rate hstrong cutoff hcutoff he)
    simp only [add_zero] at hh
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
      (fun _ => bot_le) (fun _ => measure_union_le _ _)
  filter_upwards [eventually_ge_atTop N,
    (ENNReal.tendsto_nhds_zero.mp hbad) (eta : ℝ≥0∞) (by exact_mod_cast heta)] with n hn hbn
  have hbound : (∫⁻ w, score n (ForwardAnnealed.wordSchedule w) ∂signWordLaw (rate n) n n) ≤
      (eta : ℝ≥0∞) + signWordLaw (rate n) n n (B n) := by
    apply lintegral_le_small_add_bad _ _ (fun w => hscore n _) _ (Set.to_countable _).measurableSet
    intro w hw
    have hregular : RegularWord n w := by
      by_contra hr
      exact hw (Or.inl hr)
    have hprofile : ProfileGood cutoff 1 n (ForwardAnnealed.wordSchedule w) e := by
      intro i hi hin
      by_contra hnot
      exact hw (Or.inr ⟨hregular, i, hi, hin, (lt_of_not_ge hnot).le⟩)
    have hpos := (feasible_alive_countsPrefix n w hregular.1 hregular.2).1
    have hs := hN n hn _ hpos hprofile
    have hfinite : score n (ForwardAnnealed.wordSchedule w) ≠ ∞ :=
      ne_top_of_le_ne_top (by norm_num) (hscore n _)
    rw [← ENNReal.ofReal_toReal hfinite, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hs.le
  calc
    _ ≤ (eta : ℝ≥0∞) + signWordLaw (rate n) n n (B n) := hbound
    _ ≤ (eta : ℝ≥0∞) + eta := add_le_add (le_refl _) hbn
    _ = (eta : ℝ≥0∞) * 2 := (mul_two _).symm
    _ ≤ eps := hsmall.le

theorem logLogStartupCutoff_sublog :
    Tendsto (fun n : ℕ => (logLogStartupCutoff n : ℝ) / Real.log (n : ℝ)) atTop (nhds 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  have hratio := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  have hupper : Tendsto (fun n : ℕ =>
      (Real.log (Real.log (n : ℝ)) + 1) / Real.log (n : ℝ)) atTop (nhds 0) := by
    have hh := hratio.add ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hlog)
    convert hh using 1
    · funext n
      simp only [Function.comp_def, id_eq]
      ring
    · simp
  apply squeeze_zero' (Eventually.of_forall fun n =>
    div_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg n)) ?_ hupper
  filter_upwards [hlog.eventually_gt_atTop 0, hloglog.eventually_ge_atTop 0] with n hn hn'
  exact div_le_div_of_nonneg_right (Nat.ceil_lt_add_one hn').le hn.le

theorem original_pair_probability (x : SignSequence) (n : ℕ) :
    IsProbabilityMeasure (CanonicalTree.forwardPairDataLaw x n) := by
  apply isProbabilityMeasure_bind measurable_from_top.aemeasurable
  filter_upwards [Forward.treeLaw_valid x n] with s hs
  have := Forward.uniform_vertices_probability s ⟨0, hs.root_mem⟩
  change IsProbabilityMeasure ((Measure.uniformOfFinset s.vertices).bind (fun u =>
    (Measure.uniformOfFinset s.vertices).map fun v => (s.height u, s.height v, s.graph.dist u v)))
  exact isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
    (Eventually.of_forall fun _ => Measure.isProbabilityMeasure_map_iff
      (measurable_of_countable _).aemeasurable |>.mpr inferInstance)

noncomputable def environmentTreeLaw (rate : ℝ≥0) (n : ℕ) : Measure Forward.State :=
  (signWordLaw rate n n).bind (fun w => Forward.treeLaw (ForwardAnnealed.wordSchedule w) n)

noncomputable def environmentUniformHeightLaw (rate : ℝ≥0) (n : ℕ) : Measure ℕ :=
  (environmentTreeLaw rate n).bind Forward.vertexHeightKernel

noncomputable def environmentPairDataLaw (rate : ℝ≥0) (n : ℕ) : Measure (ℕ × ℕ × ℕ) :=
  (environmentTreeLaw rate n).bind CanonicalTree.forwardPairKernel

theorem strong_environment_uniform_height (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => environmentUniformHeightLaw (rate n) n
      {h | eps ≤ |(h : ℝ) / Real.log (n : ℝ) - 1|}) atTop (nhds 0) := by
  have hh := strong_average_score_tendsto_zero rate hstrong logLogStartupCutoff
    logLogStartupCutoff_tendsto
    (fun n x => Forward.uniformHeightLaw x n {h | eps ≤ |(h : ℝ) / Real.log (n : ℝ) - 1|})
    (fun _ _ => prob_le_one) (fun eta heta => by
      simpa only [Measure.real, show ((1 : ℝ) + 1) / (2 * 1) = 1 by norm_num] using
        uniform_profile_height_bound logLogStartupCutoff logLogStartupCutoff_tendsto
          logLogStartupCutoff_sublog (by norm_num : (0 : ℝ) < 1) le_rfl heps heta)
  convert hh using 1
  funext n
  rw [environmentUniformHeightLaw, environmentTreeLaw,
    Measure.bind_bind (measurable_of_countable _).aemeasurable Forward.vertexHeightKernel.aemeasurable,
    Measure.bind_apply (by measurability) (measurable_of_countable _).aemeasurable]
  rfl

theorem strong_environment_uniform_distance (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => environmentPairDataLaw (rate n) n
      {z | eps ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - 2|}) atTop (nhds 0) := by
  have hbound (n : ℕ) (x : SignSequence) :
      CanonicalTree.forwardPairDataLaw x n
        {z | eps ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - 2|} ≤ 1 := by
    have := original_pair_probability x n
    exact prob_le_one
  have hh := strong_average_score_tendsto_zero rate hstrong logLogStartupCutoff
    logLogStartupCutoff_tendsto
    (fun n x => CanonicalTree.forwardPairDataLaw x n {z | eps ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - 2|})
    hbound (fun eta heta => by
      simpa only [Measure.real, show ((1 : ℝ) + 1) / 1 = 2 by norm_num] using
        uniform_profile_distance_bound logLogStartupCutoff logLogStartupCutoff_tendsto
          logLogStartupCutoff_sublog (by norm_num : (0 : ℝ) < 1) le_rfl heps heta)
  convert hh using 1
  funext n
  rw [environmentPairDataLaw, environmentTreeLaw,
    Measure.bind_bind (measurable_of_countable _).aemeasurable measurable_from_top.aemeasurable,
    Measure.bind_apply (by measurability) (measurable_of_countable _).aemeasurable]
  rfl

theorem strong_environment_maximum (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => environmentTreeLaw (rate n) n
      {s | eps ≤ |(Forward.treeHeight s : ℝ) / Real.log (n : ℝ) - Real.exp 1|}) atTop (nhds 0) := by
  have hh := strong_average_score_tendsto_zero rate hstrong logLogStartupCutoff
    logLogStartupCutoff_tendsto
    (fun n x => Forward.treeLaw x n
      {s | eps ≤ |(Forward.treeHeight s : ℝ) / Real.log (n : ℝ) - Real.exp 1|})
    (fun _ _ => prob_le_one) (fun eta heta => by
      simpa only [Measure.real, linearHeightFactor_one, show ((1 : ℝ) + 1) / (2 * 1) = 1 by norm_num,
        one_mul] using uniform_profile_maximum_bound logLogStartupCutoff
          logLogStartupCutoff_tendsto logLogStartupCutoff_sublog
          ⟨1, by constructor <;> norm_num⟩ heps heta)
  convert hh using 1
  funext n
  rw [environmentTreeLaw, Measure.bind_apply (by trivial) (measurable_of_countable _).aemeasurable]

end Freezing1.SIR.RandomEnvironment
