module

public import Freezing1.PoissonLowerTail
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! The source's asserted real ceiling-factorial estimate fails just above
two. This defect is separate from the strict-tail witness error S10. -/

@[expose] public section

namespace Freezing1

set_option backward.isDefEq.respectTransparency false

theorem printed_real_ceiling_factorial_counterexample :
    (2 : ℝ) ≤ 21 / 10 ∧
    (21 / 10 : ℝ) ^ 3 * Real.rpow ((21 / 10) / Real.exp 1) (21 / 10) <
      ((Nat.ceil (21 / 10 : ℝ)).factorial : ℝ) := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have ha : 0 < (21 / 10 : ℝ) / Real.exp 1 := div_pos (by norm_num) he
  have hau : (21 / 10 : ℝ) / Real.exp 1 ≤ 63 / 80 := by
    apply (div_le_iff₀ he).mpr
    linarith [Real.exp_one_gt_d9]
  have hp := Real.rpow_le_rpow_of_exponent_ge ha
    (hau.trans (by norm_num : (63 / 80 : ℝ) ≤ 1))
    (by norm_num : (2 : ℝ) ≤ 21 / 10)
  rw [Real.rpow_two] at hp
  have hs := pow_le_pow_left₀ ha.le hau 2
  have hceil : Nat.ceil (21 / 10 : ℝ) = 3 :=
    (Nat.ceil_eq_iff (by norm_num)).mpr (by norm_num)
  refine ⟨by norm_num, ?_⟩
  rw [hceil]
  calc
    _ ≤ (21 / 10 : ℝ) ^ 3 * (((21 / 10 : ℝ) / Real.exp 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ (21 / 10 : ℝ) ^ 3 * (63 / 80 : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ < _ := by norm_num

theorem ceiling_factorial_counterexample_is_source_admissible :
    (2 : ℝ) < 41 / 20 ∧ (1 : ℝ) < 42 / 41 ∧
      (41 / 20 : ℝ) * (42 / 41) = 21 / 10 := by norm_num

end Freezing1
