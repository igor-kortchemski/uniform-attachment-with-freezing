module

public import Freezing1.UniformActiveBennett
public import Freezing1.BernoulliArrayLimits

/-! Uniform active-height moments from the actual independent Bernoulli law. -/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

noncomputable def activeHeightError (x : SignSequence) (n k : ℕ) : ℝ :=
  (k : ℝ) / heightScale x n - 1

theorem activeHeightError_moment_eq (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (q : ℝ) :
    (∫ k, |activeHeightError x n k| ^ q ∂Forward.uniformActiveHeightLaw x n) =
      ∫ Y, |UniformBirth.fixedRelativeError x n h n Y| ^ q
        ∂bernoulliProductLaw (UniformBirth.reciprocalParameter x n h) := by
  have hl : HasLaw (UniformBirth.truncatedSum x n) (Forward.uniformActiveHeightLaw x n)
      (bernoulliProductLaw (UniformBirth.reciprocalParameter x n h)) :=
    ⟨(measurable_of_countable _).aemeasurable, (uniformActiveHeightLaw_eq_bernoulli_array x n h).symm⟩
  have he := hl.integral_comp (f := fun k => |activeHeightError x n k| ^ q)
    (measurable_of_countable _).aestronglyMeasurable
  rw [← he]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro Y
  change |(UniformBirth.truncatedSum x n Y : ℝ) / heightScale x n - 1| ^ q =
    |(UniformBirth.truncatedSum x n Y : ℝ) / UniformBirth.truncatedMean x n h n - 1| ^ q
  rw [UniformBirth.truncatedMean_eq_heightScale x n h le_rfl]

theorem activeHeightError_moment_le (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    (hn : 1 ≤ n) {q : ℝ} (hq : 0 ≤ q) :
    (∫ k, |activeHeightError x n k| ^ q ∂Forward.uniformActiveHeightLaw x n) ≤
      UniformBirth.relativeMomentBound q := by
  rw [activeHeightError_moment_eq x n h q]
  exact UniformBirth.fixedRelativeError_moment_le x n h hn hn hq

theorem activeHeightError_eLpNorm_le (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    (hn : 1 ≤ n) {q : ℝ} (hq : 0 < q) :
    eLpNorm (activeHeightError x n) (ENNReal.ofReal q) (Forward.uniformActiveHeightLaw x n) ≤
      ENNReal.ofReal (UniformBirth.relativeMomentBound q) ^ (1 / q) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hq).ne'
    ENNReal.ofReal_ne_top (measurable_of_countable _).aestronglyMeasurable,
    ENNReal.toReal_ofReal hq.le]
  apply ENNReal.rpow_le_rpow ?_ (by positivity)
  calc
    _ = ENNReal.ofReal (∫ k, |activeHeightError x n k| ^ q
        ∂Forward.uniformActiveHeightLaw x n) := by
      simp_rw [Real.enorm_eq_ofReal_abs,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq.le]
      exact (ofReal_integral_eq_lintegral_ofReal
        (Forward.uniformActiveHeightLaw_integrable x n _)
        (Eventually.of_forall fun _ => Real.rpow_nonneg (abs_nonneg _) _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (activeHeightError_moment_le x n h hn hq.le)

theorem uniformActiveHeight_tendsto_Lp_via_bernoulli (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm (activeHeightError (rows n) n) (ENNReal.ofReal p)
      (Forward.uniformActiveHeightLaw (rows n) n)) atTop (nhds 0) := by
  have hq : 0 < p + 1 := by linarith
  apply tendsto_eLpNorm_of_tail_and_higher_moment (fun _ => measurable_of_countable _)
    hp (by linarith : p < p + 1)
    (C := ENNReal.ofReal (UniformBirth.relativeMomentBound (p + 1)) ^ (1 / (p + 1))) (by finiteness)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact activeHeightError_eLpNorm_le (rows n) n (hrows n) hn hq
  · intro e he
    apply (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).mp
    simpa only [Real.norm_eq_abs, activeHeightError, Measure.real] using
      uniformActiveHeight_closed_deviation_tendsto rows hrows he

end Freezing1
