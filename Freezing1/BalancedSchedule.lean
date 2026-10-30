module

public import Freezing1.LinearRegimeAssumptions
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Deterministic reference schedules of every positive linear slope

Ceiling the desired attachment count gives a schedule that survives forever
and whose active population differs from its linear target by at most three.
These reference rows can fill indices outside a selected subsequence when
transporting deterministic linear-regime results to random environments.
-/

@[expose] public section

namespace Freezing1

open Filter
open scoped Topology Classical

noncomputable def balancedPlusCount (c : ℝ) (n : ℕ) : ℕ := ⌈((1 + c) / 2) * n⌉₊

noncomputable def balancedSchedule (c : ℝ) (i : ℕ) : Bool :=
  decide (balancedPlusCount c (i - 1) < balancedPlusCount c i)

theorem balancedPlusCount_mono {c : ℝ} (hc : 0 < c) : Monotone (balancedPlusCount c) := by
  intro m n hmn
  unfold balancedPlusCount
  exact Nat.ceil_mono (mul_le_mul_of_nonneg_left (by exact_mod_cast hmn) (by positivity))

theorem balancedPlusCount_step_le {c : ℝ} (_hc : 0 < c) (hc1 : c ≤ 1) (n : ℕ) :
    balancedPlusCount c (n + 1) ≤ balancedPlusCount c n + 1 := by
  apply Nat.ceil_le.mpr
  have hh := Nat.le_ceil (((1 + c) / 2) * n)
  push_cast
  change ((1 + c) / 2) * (n : ℝ) ≤ (balancedPlusCount c n : ℝ) at hh
  linarith

theorem balancedSchedule_plusCount {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (n : ℕ) :
    plusCount (balancedSchedule c) n = balancedPlusCount c n := by
  induction n with
  | zero => simp [balancedPlusCount]
  | succ n ih =>
    rw [plusCount_succ, ih]
    have hm := balancedPlusCount_mono hc (Nat.le_succ n)
    have hu := balancedPlusCount_step_le hc hc1 n
    simp only [Nat.succ_eq_add_one] at hm hu ⊢
    by_cases hn : balancedPlusCount c n < balancedPlusCount c (n + 1)
    · simp only [balancedSchedule, Nat.add_sub_cancel, hn, decide_true, ite_true]
      omega
    · simp only [balancedSchedule, Nat.add_sub_cancel, hn, decide_false, Bool.false_eq_true, ite_false]
      omega

theorem balancedSchedule_active_bounds {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (n : ℕ) :
    1 + c * n ≤ (activeCount (balancedSchedule c) n : ℝ) ∧
      (activeCount (balancedSchedule c) n : ℝ) < 3 + c * n := by
  have hlo := Nat.le_ceil (((1 + c) / 2) * n)
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ ((1 + c) / 2) * (n : ℝ) by positivity)
  rw [activeCount_eq, balancedSchedule_plusCount hc hc1]
  push_cast
  change ((1 + c) / 2) * (n : ℝ) ≤ (balancedPlusCount c n : ℝ) at hlo
  change (balancedPlusCount c n : ℝ) < ((1 + c) / 2) * (n : ℝ) + 1 at hhi
  constructor <;> linarith

theorem balancedSchedule_survives {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    extinctionTime (balancedSchedule c) = ⊤ := by
  apply (extinctionTime_eq_top_iff (balancedSchedule c)).mpr
  intro n
  have hh := (balancedSchedule_active_bounds hc hc1 n).1
  have hp : 0 < (activeCount (balancedSchedule c) n : ℝ) := by
    have hcn : 0 ≤ c * (n : ℝ) := mul_nonneg hc.le (Nat.cast_nonneg n)
    linarith
  exact_mod_cast hp

theorem balancedSchedule_relative_error {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    {i : ℕ} (hi : 0 < i) :
    |(activeCount (balancedSchedule c) i : ℝ) / i - c| ≤ 3 / (i : ℝ) := by
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hh := balancedSchedule_active_bounds hc hc1 i
  rw [abs_le]
  constructor
  · have hp : 0 ≤ (activeCount (balancedSchedule c) i : ℝ) / i - c := by
      rw [sub_nonneg, le_div_iff₀ hiR]
      linarith
    exact (neg_nonpos.mpr (div_nonneg (by norm_num) hiR.le)).trans hp
  · rw [sub_le_iff_le_add, div_le_iff₀ hiR]
    have he : (3 / (i : ℝ) + c) * i = 3 + c * i := by field_simp
    rw [he]
    exact hh.2.le

theorem balancedSchedule_nearOrigin {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (A : ℕ → ℝ) (hA : Tendsto A atTop atTop) :
    NearOriginLinear (fun _ => balancedSchedule c) A c := by
  intro eta heta
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  filter_upwards [hA.eventually_gt_atTop (max 0 (3 / eta))] with n hn
  intro i hi _
  have hAn : 0 < A n := (le_max_left _ _).trans_lt hn
  have hiR : (0 : ℝ) < i := hAn.trans_le hi
  have hiN : 0 < i := by exact_mod_cast hiR
  apply (balancedSchedule_relative_error hc hc1 hiN).trans
  apply (div_le_iff₀ hiR).mpr
  have hAi : 3 / eta < (i : ℝ) := (le_max_right _ _).trans_lt (hn.trans_le hi)
  have hh := (div_lt_iff₀ heta).mp hAi
  nlinarith

theorem balancedSchedule_bulk {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    BulkLowerBound (fun _ => balancedSchedule c) := by
  intro eps heps _
  refine ⟨c * eps, mul_pos hc heps, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  intro i hi _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hnR]
  have hh := (balancedSchedule_active_bounds hc hc1 i).1
  have hm := mul_le_mul_of_nonneg_left hi hc.le
  nlinarith

end Freezing1
