module

public import Freezing1.UniformBirthTail
public import Freezing1.UniformBirthRandomMean
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The source logarithmic birth tail with explicit integer rounding. -/

@[expose] public section

namespace Freezing1.UniformBirth

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

noncomputable def powerBirthScale (delta : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (1 - delta) * (2 : ℝ) ^ delta

noncomputable def powerBirthCutoff (delta : ℝ) (n : ℕ) : ℕ := ⌈powerBirthScale delta n⌉₊

theorem ceil_sublinear (A : ℕ → ℝ) (hA : ∀ᶠ n in atTop, 0 ≤ A n)
    (hsmall : Tendsto (fun n : ℕ => A n / n) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => (⌈A n⌉₊ : ℝ) / n) atTop (nhds 0) := by
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := hsmall.add hinv
  simp only [add_zero] at hh
  apply squeeze_zero' (Eventually.of_forall (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg n))) ?_ hh
  filter_upwards [hA] with n hn
  rw [← add_div]
  exact div_le_div_of_nonneg_right (Nat.ceil_lt_add_one hn).le (Nat.cast_nonneg n)

theorem powerBirthCutoff_sublinear {delta : ℝ} (hd : 0 < delta) :
    Tendsto (fun n : ℕ => (powerBirthCutoff delta n : ℝ) / n) atTop (nhds 0) := by
  apply ceil_sublinear (powerBirthScale delta)
    (Eventually.of_forall (fun n => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (Real.rpow_nonneg (by norm_num) _)))
  have hh := ((tendsto_rpow_neg_atTop hd).comp (tendsto_natCast_atTop_atTop (R := ℝ))).mul_const ((2 : ℝ) ^ delta)
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  dsimp only [Function.comp_def]
  rw [show -delta = (1 - delta) - 1 by ring, Real.rpow_sub hnR, Real.rpow_one]
  dsimp [powerBirthScale]
  ring

theorem log_birth_event_iff {n b : ℕ} (hn : 1 ≤ n) (hb : 1 ≤ b) (delta : ℝ) :
    delta * Real.log ((n : ℝ) / 2) < Real.log ((n : ℝ) / b) ↔ (b : ℝ) < powerBirthScale delta n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hp1 : 0 < (n : ℝ) ^ (1 - delta) := Real.rpow_pos_of_pos hnR _
  have hp2 : 0 < (2 : ℝ) ^ delta := Real.rpow_pos_of_pos (by norm_num) _
  unfold powerBirthScale
  rw [← Real.log_lt_log_iff hbR (mul_pos hp1 hp2)]
  rw [Real.log_div hnR.ne' hbR.ne', Real.log_div hnR.ne' (by norm_num),
    Real.log_mul hp1.ne' hp2.ne', Real.log_rpow hnR, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  constructor <;> intro hh <;> nlinarith

theorem auxiliary_log_birth_eq_cutoff (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    (hn : 1 ≤ n) (delta : ℝ) :
    (auxiliaryLaw x n h).real
      {z | delta * Real.log ((n : ℝ) / 2) < Real.log ((n : ℝ) / z.1)} =
      (auxiliaryLaw x n h).real {z | z.1 < powerBirthCutoff delta n} := by
  unfold Measure.real
  congr 1
  apply measure_congr
  filter_upwards [auxiliary_birth_pos x n h hn] with z hz
  exact propext ((log_birth_event_iff hn hz delta).trans (Nat.lt_ceil).symm)

/-- The paper's displayed CDF is read at the ceiling of its real threshold. -/
theorem auxiliary_log_birth_exact_CDF (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    (hn : 1 ≤ n) (delta : ℝ) (hcut : powerBirthCutoff delta n ≤ n) :
    (auxiliaryLaw x n h).real
      {z | delta * Real.log ((n : ℝ) / 2) < Real.log ((n : ℝ) / z.1)} =
      ((powerBirthCutoff delta n : ℝ) + 1 - activeCount x (powerBirthCutoff delta n)) /
        ((n : ℝ) + 1 + activeCount x n) := by
  rw [auxiliary_log_birth_eq_cutoff x n h hn delta]
  have hh := (auxiliary_birth_hasLaw x n h).measureReal_eq
    (p := fun b : ℕ => b < powerBirthCutoff delta n) (by measurability)
  exact hh.trans (birthLaw_lt x n h hcut)

theorem auxiliary_log_birth_tendsto_zero (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) {delta : ℝ} (hd : 0 < delta) :
    Tendsto (fun n => (auxiliaryLaw (rows n) n (hrows n)).real
      {z | delta * Real.log ((n : ℝ) / 2) < Real.log ((n : ℝ) / z.1)}) atTop (nhds 0) := by
  have hh := auxiliary_sublinear_birth_tendsto rows hrows (powerBirthCutoff delta)
    (powerBirthCutoff_sublinear hd)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact (auxiliary_log_birth_eq_cutoff (rows n) n (hrows n) hn delta).symm

end Freezing1.UniformBirth
