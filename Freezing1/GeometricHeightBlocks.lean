module

public import Freezing1.LinearRegimeIntervals
public import Mathlib.Order.Interval.Finset.Floor

/-!
# Exact geometric subdivisions of integer intervals

The source's decomposition requires `β < C` when `a * C < b`. Every
geometric cutoff is floored before forming an integer interval. Empty
individual blocks are permitted and are not counted as nonempty blocks.
-/

@[expose] public section

namespace Freezing1.GeometricHeight

open scoped BigOperators Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def firstIndex (β : ℝ) (a : ℕ) : ℕ :=
  Nat.ceil (Real.log (a : ℝ) / Real.log β)

noncomputable def lastIndex (β : ℝ) (b : ℕ) : ℕ :=
  Nat.floor (Real.log (b : ℝ) / Real.log β)

noncomputable def cut (β : ℝ) (k : ℕ) : ℕ := Nat.floor (β ^ k)

theorem log_ratio_nonneg {β : ℝ} (hβ : 1 < β) {a : ℕ} (ha : 1 ≤ a) :
    0 ≤ Real.log (a : ℝ) / Real.log β := by
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast ha)) (Real.log_pos hβ).le

theorem first_pow_bounds {β : ℝ} (hβ : 1 < β) {a : ℕ} (ha : 1 ≤ a) :
    (a : ℝ) ≤ β ^ firstIndex β a ∧ β ^ firstIndex β a < β * a := by
  have hβ0 : 0 < β := lt_trans zero_lt_one hβ
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hl := Real.log_pos hβ
  have hlo := (div_le_iff₀ hl).mp (Nat.le_ceil (Real.log (a : ℝ) / Real.log β))
  have hhi := (lt_div_iff₀ hl).mp
    (show (firstIndex β a : ℝ) < (Real.log (a : ℝ) + Real.log β) / Real.log β by
      simpa only [firstIndex, add_div, div_self hl.ne'] using
        Nat.ceil_lt_add_one (log_ratio_nonneg hβ ha))
  constructor
  · apply (Real.log_le_log_iff ha0 (pow_pos hβ0 _)).mp
    simpa only [Real.log_pow, firstIndex] using hlo
  · apply (Real.log_lt_log_iff (pow_pos hβ0 _) (mul_pos hβ0 ha0)).mp
    simpa only [Real.log_pow, Real.log_mul hβ0.ne' ha0.ne', add_comm] using hhi

theorem last_pow_bounds {β : ℝ} (hβ : 1 < β) {b : ℕ} (hb : 1 ≤ b) :
    β ^ lastIndex β b ≤ (b : ℝ) ∧ (b : ℝ) < β ^ (lastIndex β b + 1) := by
  have hβ0 : 0 < β := lt_trans zero_lt_one hβ
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hl := Real.log_pos hβ
  have hlo := (le_div_iff₀ hl).mp (Nat.floor_le (log_ratio_nonneg hβ hb))
  have hhi := (div_lt_iff₀ hl).mp (Nat.lt_floor_add_one (Real.log (b : ℝ) / Real.log β))
  constructor
  · apply (Real.log_le_log_iff (pow_pos hβ0 _) hb0).mp
    simpa only [Real.log_pow, lastIndex] using hlo
  · apply (Real.log_lt_log_iff hb0 (pow_pos hβ0 _)).mp
    simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one, lastIndex] using hhi

theorem first_le_last {β C : ℝ} (hβ : 1 < β) (hβC : β < C)
    {a b : ℕ} (ha : 1 ≤ a) (haC : (a : ℝ) * C < b) :
    firstIndex β a ≤ lastIndex β b := by
  have hβ0 : 0 < β := lt_trans zero_lt_one hβ
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hpow := (first_pow_bounds hβ ha).2
  have hbpow : β ^ firstIndex β a < (b : ℝ) := by
    exact hpow.trans ((by nlinarith : β * (a : ℝ) < a * C).trans haC)
  have hb0 := (pow_pos hβ0 (firstIndex β a)).trans hbpow
  have hb1 : 1 ≤ b := Nat.succ_le_of_lt (by exact_mod_cast hb0)
  apply (Nat.le_floor_iff (div_nonneg
    (Real.log_nonneg (by exact_mod_cast hb1)) (Real.log_pos hβ).le)).mpr
  apply (le_div_iff₀ (Real.log_pos hβ)).mpr
  have hlog := (Real.log_lt_log_iff (pow_pos hβ0 _) hb0).mpr hbpow
  simpa only [firstIndex, Real.log_pow] using hlog.le

theorem cut_mono {β : ℝ} (hβ : 1 ≤ β) : Monotone (cut β) := by
  intro i j hij
  exact Nat.floor_mono (pow_le_pow_right₀ hβ hij)

theorem cut_endpoints {β C : ℝ} (hβ : 1 < β) (hβC : β < C)
    {a b : ℕ} (ha : 1 ≤ a) (haC : (a : ℝ) * C < b) :
    a ≤ cut β (firstIndex β a) ∧
    cut β (firstIndex β a) ≤ cut β (lastIndex β b) ∧
    cut β (lastIndex β b) ≤ b := by
  have hab : a < b := by
    have hC : 1 < C := hβ.trans hβC
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    have : (a : ℝ) < b := by nlinarith
    exact_mod_cast this
  refine ⟨(Nat.le_floor_iff (pow_nonneg (lt_trans zero_lt_one hβ).le _)).mpr
    (first_pow_bounds hβ ha).1,
    cut_mono hβ.le (first_le_last hβ hβC ha haC), ?_⟩
  exact Nat.floor_le_of_le (last_pow_bounds hβ (by omega : 1 ≤ b)).1

theorem index_count_bounds {β C : ℝ} (hβ : 1 < β) (hβC : β < C)
    {a b : ℕ} (ha : 1 ≤ a) (haC : (a : ℝ) * C < b) :
    ((lastIndex β b - firstIndex β a : ℕ) : ℝ) ≤
        Real.log ((b : ℝ) / a) / Real.log β ∧
    Real.log ((b : ℝ) / a) / Real.log β - 2 ≤
      ((lastIndex β b - firstIndex β a : ℕ) : ℝ) := by
  have hle := first_le_last hβ hβC ha haC
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hb0 : (0 : ℝ) < b := by
    have hC0 := lt_trans zero_lt_one (hβ.trans hβC)
    exact (mul_pos ha0 hC0).trans haC
  have hb1 : 1 ≤ b := Nat.succ_le_of_lt (by exact_mod_cast hb0)
  have hfl := Nat.floor_le (log_ratio_nonneg hβ hb1)
  have hfh := Nat.lt_floor_add_one (Real.log (b : ℝ) / Real.log β)
  have hcl := Nat.le_ceil (Real.log (a : ℝ) / Real.log β)
  have hch := Nat.ceil_lt_add_one (log_ratio_nonneg hβ ha)
  rw [Nat.cast_sub hle, Real.log_div hb0.ne' ha0.ne', sub_div]
  change (lastIndex β b : ℝ) - firstIndex β a ≤ _ ∧
    _ - 2 ≤ (lastIndex β b : ℝ) - firstIndex β a
  dsimp only [firstIndex, lastIndex]
  constructor <;> linarith

noncomputable def intervalSum (f : ℕ → ℝ) (a b : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ioc a b, f i

theorem intervalSum_telescope (f : ℕ → ℝ) (v : ℕ → ℕ) (hv : Monotone v)
    {l m : ℕ} (hlm : l ≤ m) :
    (∑ k ∈ Finset.Ico l m, intervalSum f (v k) (v (k + 1))) =
      intervalSum f (v l) (v m) := by
  induction m, hlm using Nat.le_induction with
  | base => simp [intervalSum]
  | succ m hlm ih =>
    rw [Finset.sum_Ico_succ_top hlm, ih]
    exact Finset.sum_Ioc_consecutive f (hv hlm) (hv (Nat.le_succ m))

theorem intervalSum_partition (f : ℕ → ℝ) {β C : ℝ}
    (hβ : 1 < β) (hβC : β < C) {a b : ℕ} (ha : 1 ≤ a)
    (haC : (a : ℝ) * C < b) :
    intervalSum f a b = intervalSum f a (cut β (firstIndex β a)) +
      (∑ k ∈ Finset.Ico (firstIndex β a) (lastIndex β b),
        intervalSum f (cut β k) (cut β (k + 1))) +
      intervalSum f (cut β (lastIndex β b)) b := by
  obtain ⟨hal, hlm, hmb⟩ := cut_endpoints hβ hβC ha haC
  rw [intervalSum_telescope f _ (cut_mono hβ.le) (first_le_last hβ hβC ha haC)]
  exact (Finset.sum_Ioc_consecutive f hal (hlm.trans hmb)).symm.trans
    (congrArg (fun y => intervalSum f a (cut β (firstIndex β a)) + y)
      (Finset.sum_Ioc_consecutive f hlm hmb).symm) |>.trans (by simp only [intervalSum]; ring)

theorem heightInterval_eq_intervalSum (x : SignSequence) (a b : ℕ) :
    heightInterval x a b = intervalSum
      (fun i => if x i then 1 / (activeCount x i : ℝ) else 0) a b := by
  exact (Finset.sum_Ico_add'
    (fun i : ℕ => if x i then 1 / (activeCount x i : ℝ) else 0) a b 1).trans (by
    simp only [Finset.Ico_add_one_add_one_eq_Ioc]; rfl)

end Freezing1.GeometricHeight
