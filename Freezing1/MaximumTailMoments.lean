module

public import Freezing1.MaximumUniformTail
public import Freezing1.TailIntegralSeven
public import Freezing1.MainMaximum

/-! Source A36's moment upgrade using its proved uniform threshold bound
and the same real tail-integral method as the active-height argument. -/

@[expose] public section

namespace Freezing1

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal Classical

set_option backward.isDefEq.respectTransparency false

namespace Forward

theorem ValidAt.treeHeight_le_stepCount {n : ℕ} {s : State} (hs : ValidAt n s) :
    treeHeight s ≤ n := by
  apply Finset.sup_le
  intro v hv
  exact (hs.height_le_id v hv).trans (hs.vertices_le v hv)

theorem integrable_maximum_error_rpow (x : SignSequence) (n : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun s => |(treeHeight s : ℝ) / heightScale x n - 1| ^ p) (treeLaw x n) := by
  let R : ℝ := (n : ℝ) / |heightScale x n| + 1
  apply (integrable_const (R ^ p)).mono' measurable_from_top.aestronglyMeasurable
  filter_upwards [treeLaw_valid x n] with s hs
  have hh : (treeHeight s : ℝ) ≤ n := by exact_mod_cast hs.treeHeight_le_stepCount
  have hb : |(treeHeight s : ℝ) / heightScale x n - 1| ≤ R := by
    calc
      _ ≤ |(treeHeight s : ℝ) / heightScale x n| + |(1 : ℝ)| := abs_sub _ _
      _ = (treeHeight s : ℝ) / |heightScale x n| + 1 := by
        rw [abs_div, abs_of_nonneg (Nat.cast_nonneg _), abs_one]
      _ ≤ _ := by
        dsimp only [R]
        exact add_le_add (div_le_div_of_nonneg_right hh (abs_nonneg _)) le_rfl
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) hb hp

end Forward

theorem eventually_maximum_error_tail_seven (rows : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (rows n) n)
      atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ u : ℝ, 7 < u →
      (Forward.treeLaw (rows n) n).real
        {s | u ≤ |(Forward.treeHeight s : ℝ) / heightScale (rows n) n - 1|} ≤
        Real.exp (-bennettRate u / 2) := by
  have hd := tendsto_heightScale_atTop rows
    (fun n => (lt_extinctionTime_iff (rows n) n).mp (hτ n))
  filter_upwards [eventually_maximum_uniform_bennett_upper rows hτ hlog,
    hd.eventually_ge_atTop 1] with n hbound hm
  intro u hu
  have hm0 : 0 < heightScale (rows n) n := by linarith
  calc
    _ ≤ (Forward.treeLaw (rows n) n).real
        {s | u + 1 ≤ (Forward.treeHeight s : ℝ) / heightScale (rows n) n} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro s hs
      change u ≤ |(Forward.treeHeight s : ℝ) / heightScale (rows n) n - 1| at hs
      change u + 1 ≤ (Forward.treeHeight s : ℝ) / heightScale (rows n) n
      have hz : 0 ≤ (Forward.treeHeight s : ℝ) / heightScale (rows n) n :=
        div_nonneg (Nat.cast_nonneg _) hm0.le
      rcases le_abs.mp hs with hs | hs <;> linarith
    _ ≤ Real.exp (-heightScale (rows n) n * bennettRate u / 2) := by
      simpa only [add_sub_cancel_right] using hbound (u + 1) (by linarith)
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hg := bennettRate_nonneg (by linarith : 0 ≤ u)
      nlinarith

theorem eventually_maximum_error_moment_le_source_integral (rows : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (rows n) n)
      atTop (𝓝 0)) {p : ℝ} (hp : 1 ≤ p) :
    ∀ᶠ n in atTop,
      (∫ s, |(Forward.treeHeight s : ℝ) / heightScale (rows n) n - 1| ^ p
        ∂Forward.treeLaw (rows n) n) ≤
        (7 : ℝ) ^ p + p * ∫ u in Ioi (7 : ℝ), bennettMomentDensity p (1 / 2) u := by
  filter_upwards [eventually_maximum_error_tail_seven rows hτ hlog] with n hn
  exact moment_le_seven_of_bennett_tail measurable_from_top.aemeasurable
    (Eventually.of_forall fun _ => abs_nonneg _) hp
    (Forward.integrable_maximum_error_rpow (rows n) n (by linarith)) hn

theorem eventually_maximum_error_eLpNorm_le_source_integral (rows : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (rows n) n)
      atTop (𝓝 0)) {p : ℝ} (hp : 1 ≤ p) :
    ∀ᶠ n in atTop,
      eLpNorm (fun s => (Forward.treeHeight s : ℝ) / heightScale (rows n) n - 1)
        (ENNReal.ofReal p) (Forward.treeLaw (rows n) n) ≤
        ENNReal.ofReal ((7 : ℝ) ^ p + p *
          ∫ u in Ioi (7 : ℝ), bennettMomentDensity p (1 / 2) u) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  filter_upwards [eventually_maximum_error_moment_le_source_integral rows hτ hlog hp] with n hn
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne'
    ENNReal.ofReal_ne_top measurable_from_top.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le]
  apply ENNReal.rpow_le_rpow ?_ (by positivity)
  calc
    _ = ENNReal.ofReal (∫ s, |(Forward.treeHeight s : ℝ) / heightScale (rows n) n - 1| ^ p
        ∂Forward.treeLaw (rows n) n) := by
      simp_rw [Real.enorm_eq_ofReal_abs,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
      exact (ofReal_integral_eq_lintegral_ofReal
        (Forward.integrable_maximum_error_rpow (rows n) n hp0.le)
        (Eventually.of_forall fun _ => Real.rpow_nonneg (abs_nonneg _) _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hn

theorem maximum_height_tendsto_Lp_via_tail_integral (rows : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (rows n) n)
      atTop (𝓝 0)) {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm
      (fun s => (Forward.treeHeight s : ℝ) / heightScale (rows n) n - 1)
      (ENNReal.ofReal p) (Forward.treeLaw (rows n) n)) atTop (𝓝 0) := by
  apply tendsto_eLpNorm_of_tail_and_higher_moment (fun _ => measurable_from_top)
    hp (by linarith : p < p + 1)
    (C := ENNReal.ofReal ((7 : ℝ) ^ (p + 1) + (p + 1) *
      ∫ u in Ioi (7 : ℝ), bennettMomentDensity (p + 1) (1 / 2) u) ^ (1 / (p + 1)))
    (by finiteness)
  · exact eventually_maximum_error_eLpNorm_le_source_integral rows hτ hlog (by linarith)
  · intro e he
    simpa only [Real.norm_eq_abs] using maximum_height_deviation_tendsto_zero rows hτ hlog he

end Freezing1
