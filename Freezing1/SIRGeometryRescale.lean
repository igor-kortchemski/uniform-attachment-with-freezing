module

public import Freezing1.LinearRegimeCutoffs

/-! Fixed positive observation proportions preserve logarithmic geometry. -/

@[expose] public section

namespace Freezing1.SIR

open Filter Set
open scoped Topology

set_option backward.isDefEq.respectTransparency false

theorem deviation_rescale_subset {a b c eps : ℝ} (heps : 0 < eps)
    (ha : a ≠ 0) (hb : b ≠ 0) (hr : |a / b| ≤ 2)
    (hnear : |a / b - 1| < eps / (4 * (|c| + 1))) :
    {v : ℝ | eps ≤ |v / b - c|} ⊆ {v : ℝ | eps / 4 ≤ |v / a - c|} := by
  intro v hv
  change eps ≤ |v / b - c| at hv
  change eps / 4 ≤ |v / a - c|
  by_contra hnot
  have hsmall : |v / a - c| < eps / 4 := lt_of_not_ge hnot
  have he : v / b - c = (v / a - c) * (a / b) + c * (a / b - 1) := by
    field_simp
    ring
  have hbound := abs_add_le ((v / a - c) * (a / b)) (c * (a / b - 1))
  simp only [abs_mul] at hbound
  have hfirst := mul_le_mul_of_nonneg_left hr (abs_nonneg (v / a - c))
  have hsecond : |c| * |a / b - 1| < eps / 4 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 4 * (|c| + 1))).mp hnear
    have hn := abs_nonneg (a / b - 1)
    nlinarith
  rw [he] at hv
  nlinarith

theorem eventually_log_prefix_rescale_subset {t c eps : ℝ} (ht : 0 < t) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      {v : ℝ | eps ≤ |v / Real.log (n : ℝ) - c|} ⊆
        {v : ℝ | eps / 4 ≤ |v / Real.log (⌊t * (n : ℝ)⌋₊ : ℝ) - c|} := by
  have hratio := tendsto_log_floor_mul_div_log ht
  have hratioabs := hratio.abs
  have hnear := (hratio.sub (tendsto_const_nhds (x := (1 : ℝ)))).abs
  simp only [abs_one] at hratioabs
  simp only [sub_self, abs_zero] at hnear
  have hfloor : Tendsto (fun n : ℕ => ⌊t * (n : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop ht)
  filter_upwards [eventually_ge_atTop (2 : ℕ), hfloor.eventually (eventually_ge_atTop (2 : ℕ)),
    hratioabs.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)),
    hnear.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < eps / (4 * (|c| + 1))))]
      with n hn hm hr he
  exact deviation_rescale_subset heps (Real.log_pos (by exact_mod_cast hm)).ne'
    (Real.log_pos (by exact_mod_cast hn)).ne' hr.le he

end Freezing1.SIR
