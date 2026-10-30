module

public import Freezing1.BennettMomentIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# The source's tail integral above seven, for every real moment

The exact dilation is retained. The exponential asymptotic is proved by
a logarithmic envelope centred at seven, rather than by repeated integration
by parts; thus noninteger exponents are handled without an integer premise.
-/

@[expose] public section

namespace Freezing1

open Filter Set MeasureTheory Asymptotics
open scoped Topology Classical

set_option backward.isDefEq.respectTransparency false

theorem exp_two_sub_one_le_seven : Real.exp 2 - 1 ≤ 7 := by
  have he : Real.exp 1 < 11 / 4 := Real.exp_one_lt_d9.trans (by norm_num)
  have hp := Real.exp_pos (1 : ℝ)
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith

theorem self_le_bennettRate_of_seven {u : ℝ} (hu : 7 ≤ u) : u ≤ bennettRate u :=
  self_le_bennettRate (exp_two_sub_one_le_seven.trans hu)

noncomputable def exponentialMomentTail (p m : ℝ) : ℝ :=
  ∫ u in Ioi (7 : ℝ), Real.exp (-m * u) * u ^ (p - 1)

theorem integrable_exponentialMomentTail {p m : ℝ} (hp : 1 ≤ p) (hm : 0 < m) :
    IntegrableOn (fun u : ℝ => Real.exp (-m * u) * u ^ (p - 1)) (Ioi 7) := by
  have hh : IntegrableOn (fun u : ℝ => u ^ (p - 1) * Real.exp (-m * u)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (s := p - 1) (p := 1) (b := m)
        (by linarith) (by norm_num) hm
  simpa only [mul_comm] using hh.mono_set
    (show Ioi (7 : ℝ) ⊆ Ioi 0 by intro u hu; exact lt_trans (by norm_num) hu)

theorem exponentialMomentTail_nonneg (p m : ℝ) : 0 ≤ exponentialMomentTail p m := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro u hu
  exact mul_nonneg (Real.exp_pos _).le
    (Real.rpow_nonneg (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 7) hu)) _)

theorem rpow_le_seven_envelope {q u : ℝ} (hq : 0 ≤ q) (hu : 7 ≤ u) :
    u ^ q ≤ (7 : ℝ) ^ q * Real.exp (q * (u - 7) / 7) := by
  have hu0 : 0 < u := by linarith
  have hh := Real.log_le_sub_one_of_pos (div_pos hu0 (by norm_num : (0 : ℝ) < 7))
  rw [Real.log_div hu0.ne' (by norm_num : (7 : ℝ) ≠ 0)] at hh
  rw [Real.rpow_def_of_pos hu0, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 7),
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hh hq]

theorem exponential_tail_density_le {p m u : ℝ} (hp : 1 ≤ p)
    (hm : 2 * (p - 1) / 7 ≤ m) (hu : 7 ≤ u) :
    Real.exp (-m * u) * u ^ (p - 1) ≤
      (7 : ℝ) ^ (p - 1) * Real.exp (-7 * m / 2) * Real.exp (-(m / 2) * u) := by
  have hpow := rpow_le_seven_envelope (q := p - 1) (by linarith) hu
  calc
    _ ≤ Real.exp (-m * u) * ((7 : ℝ) ^ (p - 1) *
        Real.exp ((p - 1) * (u - 7) / 7)) :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = (7 : ℝ) ^ (p - 1) *
        Real.exp (-m * u + (p - 1) * (u - 7) / 7) := by rw [Real.exp_add]; ring
    _ ≤ _ := by
      rw [mul_assoc, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hm (show 0 ≤ u - 7 by linarith)
      nlinarith

theorem exponentialMomentTail_le {p m : ℝ} (hp : 1 ≤ p) (hm : 0 < m)
    (hlarge : 2 * (p - 1) / 7 ≤ m) :
    exponentialMomentTail p m ≤ 2 * (7 : ℝ) ^ (p - 1) * Real.exp (-7 * m) / m := by
  have hi := (integrableOn_exp_mul_Ioi
    (a := -(m / 2)) (by linarith) 7).const_mul
      ((7 : ℝ) ^ (p - 1) * Real.exp (-7 * m / 2))
  calc
    _ ≤ ∫ u in Ioi (7 : ℝ),
        ((7 : ℝ) ^ (p - 1) * Real.exp (-7 * m / 2)) * Real.exp (-(m / 2) * u) := by
      apply integral_mono_ae (integrable_exponentialMomentTail hp hm) hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact exponential_tail_density_le hp hlarge hu.le
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -(m / 2) < 0)]
      have he : Real.exp (-7 * m / 2) * Real.exp (-(m / 2) * 7) = Real.exp (-7 * m) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = 2 * (7 : ℝ) ^ (p - 1) *
            (Real.exp (-7 * m / 2) * Real.exp (-(m / 2) * 7)) / m := by
          field_simp
        _ = _ := by rw [he]

/-- Exact positive dilation from the source's display, with real exponents. -/
theorem exponentialMomentTail_dilation (p : ℝ) {m : ℝ} (hm : 0 < m) :
    exponentialMomentTail p m = m ^ (-p) *
      ∫ u in Ioi (7 * m), Real.exp (-u) * u ^ (p - 1) := by
  have hc : m ^ (p - 1) * exponentialMomentTail p m =
      m⁻¹ * ∫ u in Ioi (7 * m), Real.exp (-u) * u ^ (p - 1) := by
    calc
      _ = ∫ u in Ioi (7 : ℝ), Real.exp (-(m * u)) * (m * u) ^ (p - 1) := by
        rw [exponentialMomentTail, ← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        dsimp only
        rw [Real.mul_rpow hm.le (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 7) hu))]
        simp only [neg_mul]
        ring
      _ = _ := by
        simpa only [smul_eq_mul, mul_comm m 7] using
          integral_comp_mul_left_Ioi (fun u : ℝ => Real.exp (-u) * u ^ (p - 1)) 7 hm
  apply (mul_left_cancel₀ (Real.rpow_pos_of_pos hm (p - 1)).ne')
  rw [hc, ← mul_assoc, ← Real.rpow_add hm]
  have he : p - 1 + -p = -1 := by ring
  rw [he, Real.rpow_neg_one]

theorem exponentialMomentTail_isBigO (p : ℝ) (hp : 1 ≤ p) :
    (fun m : ℝ => exponentialMomentTail p m) =O[atTop]
      (fun m => Real.exp (-7 * m) / m) := by
  apply Asymptotics.IsBigO.of_bound (2 * (7 : ℝ) ^ (p - 1))
  filter_upwards [eventually_ge_atTop (max 1 (2 * (p - 1) / 7))] with m hm
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans hm)
  rw [Real.norm_eq_abs, abs_of_nonneg (exponentialMomentTail_nonneg p m),
    Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) hm0)]
  simpa only [mul_div_assoc] using exponentialMomentTail_le hp hm0 ((le_max_right _ _).trans hm)

theorem bennett_tail_le_exponentialMomentTail {p m : ℝ} (hp : 1 ≤ p) (hm : 0 < m) :
    (∫ u in Ioi (7 : ℝ), bennettMomentDensity p m u) ≤ exponentialMomentTail p m := by
  apply integral_mono_ae
    (IntegrableOn.mono_set (integrable_bennettMomentDensity (by linarith) hm)
      (show Ioi (7 : ℝ) ⊆ Ioi 0 by intro u hu; exact lt_trans (by norm_num) hu))
    (integrable_exponentialMomentTail hp hm)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  apply mul_le_mul_of_nonneg_right _
    (Real.rpow_nonneg (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 7) hu)) _)
  apply Real.exp_le_exp.mpr
  have hg := self_le_bennettRate_of_seven hu.le
  nlinarith

end Freezing1
