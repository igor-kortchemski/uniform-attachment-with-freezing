module

public import Freezing1.ForwardCutMaximum
public import Freezing1.SIRLateMaximumWord
public import Freezing1.SIRFixedWordBridge
public import Freezing1.ForwardAbsorption

/-!
# Negligible terminal cut height for the genuine adaptive SIR mixture

The conditional forward cut tail is mixed with actual adaptive word weights.
The scalar budget stops at the true first zero; raw post-extinction integer
walk terms never enter the argument.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable def terminalForwardLaw (rate : ℝ≥0) (n : ℕ) : Measure Forward.State :=
  (signWordLaw rate n (2 * n + 1)).bind
    (fun w => Forward.treeLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1))

instance terminalForwardLaw_probability (rate : ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (terminalForwardLaw rate n) :=
  isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
    (Eventually.of_forall fun _ => inferInstance)

theorem terminal_word_cutMaximum_tail (n : ℕ) (w : Fin (2 * n + 1) → Bool)
    (hw : SignWordFeasible n w) {theta L D : ℝ} (htheta : 0 ≤ theta) (hL : 0 < L)
    (hcharge : wordLateBirthCharge n w ≤ D) :
    (Forward.treeLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1)).real
      {s | L ≤ (Forward.cutMaximum s n : ℝ)} ≤
        (2 * n + 2 : ℝ) * Real.exp theta * Real.exp (D * (Real.exp theta - 1) - theta * L) := by
  obtain ⟨T, hT, hτ, hzero, hpos⟩ := terminal_word_first_extinction n w hw
  have hhold := Forward.treeLaw_constant_after_extinction hτ (2 * n + 1 - T)
  rw [show T + (2 * n + 1 - T) = 2 * n + 1 by omega] at hhold
  rw [hhold]
  by_cases hnT : n ≤ T
  · have hs := terminal_word_late_heightScale_le_charge n w hw hT hnT hpos
    have hh := Forward.cutMaximum_exponential_tail (ForwardAnnealed.wordSchedule w) n T hnT
      (by rw [hτ]) htheta (L := L)
    have he : 0 ≤ Real.exp theta - 1 := sub_nonneg.mpr (Real.one_le_exp htheta)
    have hscale := sub_le_sub_right (mul_le_mul_of_nonneg_right (hs.trans hcharge) he) (theta * L)
    exact hh.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right (by exact_mod_cast (show T + 1 ≤ 2 * n + 2 by omega)) (Real.exp_pos _).le)
      (Real.exp_le_exp.mpr hscale) (Real.exp_pos _).le (by positivity))
  · have hz : ∀ᵐ s ∂Forward.treeLaw (ForwardAnnealed.wordSchedule w) T,
        Forward.cutMaximum s n = 0 := by
      filter_upwards [Forward.treeLaw_valid (ForwardAnnealed.wordSchedule w) T] with s hs
      apply Nat.eq_zero_of_le_zero
      apply Finset.sup_le
      intro v hv
      have hvn : v ≤ n := by have := hs.vertices_le v hv; omega
      rw [show Forward.cutHeight s n v = 0 from Forward.cutHeightAux_eq_zero_of_le s n _ v hvn]
    have hprob : Forward.treeLaw (ForwardAnnealed.wordSchedule w) T
        {s | L ≤ (Forward.cutMaximum s n : ℝ)} = 0 := by
      calc
        _ = Forward.treeLaw (ForwardAnnealed.wordSchedule w) T ∅ := by
          apply measure_congr
          filter_upwards [hz] with s hs
          simp only [mem_empty_iff_false, hs, Nat.cast_zero,
            not_le.mpr hL]
        _ = 0 := measure_empty
    rw [Measure.real, hprob, ENNReal.toReal_zero]
    positivity

noncomputable def lateCutTailBound (theta : ℝ) (n : ℕ) : ℝ :=
  2 * Real.exp theta * (((n : ℝ)⁻¹) ^ 2 + ((n : ℝ)⁻¹) ^ 3)

theorem lateCutTailBound_nonneg (theta : ℝ) (n : ℕ) : 0 ≤ lateCutTailBound theta n := by
  unfold lateCutTailBound
  positivity

theorem lateCutTailBound_tendsto_zero (theta : ℝ) :
    Tendsto (lateCutTailBound theta) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 2 * Real.exp theta * (((n : ℝ)⁻¹) ^ 2 + ((n : ℝ)⁻¹) ^ 3)) atTop (𝓝 0)
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_pow (by norm_num : (3 : ℕ) ≠ 0), add_zero, mul_zero] using
      ((hi.pow 2).add (hi.pow 3)).const_mul (2 * Real.exp theta)

theorem terminal_word_cutMaximum_small_charge (n : ℕ) (hn : 0 < n)
    (w : Fin (2 * n + 1) → Bool) (hw : SignWordFeasible n w)
    {eta : ℝ} (heta : 0 < eta) (hlog : 0 < Real.log n)
    (hcharge : wordLateBirthCharge n w ≤ (1 / (Real.exp (4 / eta) - 1)) * Real.log n) :
    (Forward.treeLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1)).real
      {s | eta * Real.log n ≤ (Forward.cutMaximum s n : ℝ)} ≤ lateCutTailBound (4 / eta) n := by
  have ht : 0 < 4 / eta := by positivity
  have he : 0 < Real.exp (4 / eta) - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)
  have hh := terminal_word_cutMaximum_tail n w hw ht.le (mul_pos heta hlog) hcharge
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hexp : Real.exp (-3 * Real.log (n : ℝ)) = ((n : ℝ) ^ 3)⁻¹ := by
    rw [show -3 * Real.log (n : ℝ) = -((3 : ℕ) * Real.log (n : ℝ)) by norm_num,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log hnR]
  have heq :
      (1 / (Real.exp (4 / eta) - 1) * Real.log (n : ℝ)) * (Real.exp (4 / eta) - 1) -
        (4 / eta) * (eta * Real.log n) = -3 * Real.log n := by
    field_simp [he.ne', heta.ne']
    ring
  rw [heq, hexp] at hh
  convert hh using 1
  unfold lateCutTailBound
  field_simp

/-- The true adaptive original-word mixture has negligible maximum cut
height above event time `n`, normalized by `log n`. -/
theorem terminalForwardLaw_cutMaximum_over_log_tendsto_zero (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {eta : ℝ} (heta : 0 < eta) :
    Tendsto (fun n : ℕ => terminalForwardLaw (rate n) n
      {s | eta * Real.log n ≤ (Forward.cutMaximum s n : ℝ)}) atTop (𝓝 0) := by
  let theta : ℝ := 4 / eta
  let delta : ℝ := 1 / (Real.exp theta - 1)
  have ht : 0 < theta := by dsimp [theta]; positivity
  have hd : 0 < delta := by
    dsimp [delta]
    exact one_div_pos.mpr (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht))
  have hword : Tendsto (fun n : ℕ => signWordLaw (rate n) n (2 * n + 1)
      {w | delta * Real.log n ≤ wordLateBirthCharge n w}) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).mp
      (signWordLaw_wordLateBirthCharge_over_log_tendsto_zero rate hstrong hd)
  have htail : Tendsto (fun n : ℕ => ENNReal.ofReal (lateCutTailBound theta n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (lateCutTailBound_tendsto_zero theta)
  have hsum := hword.add htail
  simp only [add_zero] at hsum
  have hbound : ∀ᶠ n : ℕ in atTop,
      terminalForwardLaw (rate n) n {s | eta * Real.log n ≤ (Forward.cutMaximum s n : ℝ)} ≤
      signWordLaw (rate n) n (2 * n + 1) {w | delta * Real.log n ≤ wordLateBirthCharge n w} +
        ENNReal.ofReal (lateCutTailBound theta n) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_gt_atTop 0]
      with n hn hnlog
    let A : Set (Fin (2 * n + 1) → Bool) := {w | delta * Real.log n ≤ wordLateBirthCharge n w}
    rw [terminalForwardLaw, Measure.bind_apply (by trivial) (measurable_of_countable _).aemeasurable]
    calc
      _ ≤ ∫⁻ w, A.indicator (fun _ => 1) w + ENNReal.ofReal (lateCutTailBound theta n)
          ∂signWordLaw (rate n) n (2 * n + 1) := by
        apply lintegral_mono_ae
        filter_upwards [signWordLaw_feasible (rate n) n (2 * n + 1)] with w hw
        by_cases hwA : w ∈ A
        · rw [indicator_of_mem hwA]
          exact (prob_le_one).trans (le_add_of_nonneg_right zero_le)
        · rw [indicator_of_notMem hwA, zero_add]
          have hcharge : wordLateBirthCharge n w ≤ delta * Real.log n := (not_le.mp hwA).le
          have hh := terminal_word_cutMaximum_small_charge n hn w hw heta hnlog hcharge
          rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
          exact ENNReal.ofReal_le_ofReal hh
      _ = _ := by
        rw [lintegral_add_left ((measurable_const.indicator (Set.to_countable A).measurableSet)),
          lintegral_indicator_const (Set.to_countable A).measurableSet, one_mul]
        simp [A]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) hbound

end Freezing1.SIR
