module

public import Freezing1.UniformActiveBernoulli
public import Freezing1.UniformBirthRelativeMomentLaw

/-! Exact source Bennett concentration for the actual uniform active height. -/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

theorem uniformActiveHeight_closed_deviation_le (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) :
    (Forward.uniformActiveHeightLaw x n).real
      {k | u ≤ |(k : ℝ) / heightScale x n - 1|} ≤
        2 * Real.exp (-heightScale x n * bennettRate u) := by
  rw [uniformActiveHeightLaw_eq_bernoulli_array x n h]
  unfold Measure.real
  rw [Measure.map_apply (measurable_of_countable _) (by measurability)]
  have hm := UniformBirth.truncatedMean_eq_heightScale x n h (b := n) le_rfl
  have hh := UniformBirth.fixedRelativeError_closed_tail x n h n
    (by rw [hm]; exact heightScale_pos hn h) hu
  simpa only [UniformBirth.fixedRelativeError, hm, Set.preimage_ofPred_eq, Measure.real] using hh

theorem uniformActiveHeight_strict_deviation_le (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) :
    (Forward.uniformActiveHeightLaw x n).real
      {k | u < |(k : ℝ) / heightScale x n - 1|} ≤
        2 * Real.exp (-heightScale x n * bennettRate u) := by
  have hsub : {k : ℕ | u < |(k : ℝ) / heightScale x n - 1|} ⊆
      {k | u ≤ |(k : ℝ) / heightScale x n - 1|} := by
    intro k hk
    change u < |(k : ℝ) / heightScale x n - 1| at hk
    change u ≤ |(k : ℝ) / heightScale x n - 1|
    exact le_of_lt hk
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (uniformActiveHeight_closed_deviation_le x n h hn hu)

/-- The paper's A33 probability argument, with the actual independent-array
representation and no assumed height-tail estimate. -/
theorem uniformActiveHeight_closed_deviation_tendsto (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n => (Forward.uniformActiveHeightLaw (rows n) n).real
      {k | u ≤ |(k : ℝ) / heightScale (rows n) n - 1|}) atTop (nhds 0) := by
  have hscaled := (tendsto_heightScale_atTop rows hrows).const_mul_atTop (bennettRate_pos hu)
  have hneg := tendsto_neg_atTop_atBot.comp hscaled
  have he := (Real.tendsto_exp_atBot.comp hneg).const_mul 2
  simp only [Function.comp_def, mul_zero] at he
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ he
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simpa only [neg_mul, mul_comm (heightScale (rows n) n) (bennettRate u)] using
    uniformActiveHeight_closed_deviation_le (rows n) n (hrows n) hn hu

end Freezing1
