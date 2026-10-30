module

public import Freezing1.GeometricHeightBlocks

/-! Concrete obstructions to the printed unrestricted partition and the
last partial-block cardinality estimate. These checks retain S15 rather
than silently identify a repaired proof with the literal printed chain. -/

@[expose] public section

namespace Freezing1.GeometricHeight

open scoped BigOperators Classical

set_option backward.isDefEq.respectTransparency false

theorem firstIndex_eq_of_pow_bounds {β : ℝ} (hβ : 1 < β) {a k : ℕ}
    (hk : k ≠ 0) (ha : 1 ≤ a) (hlo : β ^ (k - 1) < (a : ℝ))
    (hhi : (a : ℝ) ≤ β ^ k) : firstIndex β a = k := by
  have hβ0 : 0 < β := by linarith
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  apply (Nat.ceil_eq_iff hk).mpr
  constructor
  · apply (lt_div_iff₀ (Real.log_pos hβ)).mpr
    simpa only [Real.log_pow] using
      (Real.log_lt_log_iff (pow_pos hβ0 _) ha0).mpr hlo
  · apply (div_le_iff₀ (Real.log_pos hβ)).mpr
    simpa only [Real.log_pow] using
      (Real.log_le_log_iff ha0 (pow_pos hβ0 _)).mpr hhi

theorem lastIndex_eq_of_pow_bounds {β : ℝ} (hβ : 1 < β) {b k : ℕ}
    (hb : 1 ≤ b) (hlo : β ^ k ≤ (b : ℝ))
    (hhi : (b : ℝ) < β ^ (k + 1)) : lastIndex β b = k := by
  have hβ0 : 0 < β := by linarith
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  apply (Nat.floor_eq_iff (log_ratio_nonneg hβ hb)).mpr
  constructor
  · apply (le_div_iff₀ (Real.log_pos hβ)).mpr
    simpa only [Real.log_pow] using
      (Real.log_le_log_iff (pow_pos hβ0 _) hb0).mpr hlo
  · apply (div_lt_iff₀ (Real.log_pos hβ)).mpr
    simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using
      (Real.log_lt_log_iff hb0 (pow_pos hβ0 _)).mpr hhi

/-- The source's announced `β > 1` alone allows reversed endpoint indices. -/
theorem printed_partition_indices_counterexample :
    firstIndex 4 2 = 1 ∧ lastIndex 4 3 = 0 ∧
    cut 4 (firstIndex 4 2) > 3 ∧ cut 4 (lastIndex 4 3) < 2 := by
  have hl : firstIndex 4 2 = 1 :=
    firstIndex_eq_of_pow_bounds (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hm : lastIndex 4 3 = 0 :=
    lastIndex_eq_of_pow_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hl, hm, by norm_num [cut, hl], by norm_num [cut, hm]⟩

/-- The printed three-sum equality fails for actual reciprocal populations
of the strictly surviving all-attachment schedule. -/
theorem printed_partition_height_counterexample :
    let x : SignSequence := fun _ => true
    heightInterval x 2 3 ≠ heightInterval x 2 (cut 4 (firstIndex 4 2)) +
      (∑ k ∈ Finset.Ico (firstIndex 4 2) (lastIndex 4 3),
        heightInterval x (cut 4 k) (cut 4 (k + 1))) +
      heightInterval x (cut 4 (lastIndex 4 3)) 3 := by
  obtain ⟨hl, hm, _, _⟩ := printed_partition_indices_counterexample
  norm_num [hl, hm, cut, heightInterval, activeCount, Finset.sum_Ico_succ_top,
    Finset.sum_range_succ]

/-- Even with `1 < β < C` and `a C < b`, the last interval's number of
integer points can exceed its real geometric length. -/
theorem printed_last_count_counterexample :
    let β : ℝ := 4 / 3
    firstIndex β 2 = 3 ∧ lastIndex β 3 = 3 ∧
    1 < β ∧ β < (7 / 5 : ℝ) ∧ (2 : ℝ) * (7 / 5) < 3 ∧
    β ^ 3 ≤ (3 : ℝ) ∧ (3 : ℝ) < β ^ 4 ∧
    (β ^ 4 - β ^ 3) < (intervalPlusCount (fun _ => true) (Nat.floor (β ^ 3)) 3 : ℝ) := by
  dsimp only
  have hl : firstIndex (4 / 3) 2 = 3 :=
    firstIndex_eq_of_pow_bounds (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hm : lastIndex (4 / 3) 3 = 3 :=
    lastIndex_eq_of_pow_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf : Nat.floor (64 / 27 : ℝ) = 2 :=
    (Nat.floor_eq_iff (by positivity)).mpr (by norm_num)
  refine ⟨hl, hm, ?_⟩
  norm_num [intervalPlusCount, hf, Nat.card_Ioc]

/-- This last-count example also has valid actual near-linear populations
with positive `c - η`: `c = 1`, `η = 1/2`, and integer window `[2,3]`. -/
theorem last_count_example_ratio_bounds :
    ∀ i ∈ Finset.Icc 2 3,
      |(activeCount (fun _ => true) i : ℝ) / i - 1| ≤ 1 / 2 := by
  intro i hi
  have hi' : i = 2 ∨ i = 3 := by simp only [Finset.mem_Icc] at hi; omega
  rcases hi' with rfl | rfl <;> norm_num [activeCount, Finset.sum_range_succ]

/-- The intermediate denominator printed as `β^(ell-1)` can be far
smaller than the correct final-block denominator `β^m`. The claimed next
cardinality comparison then fails even when the last count has no
fractional-cutoff issue. -/
theorem printed_last_denominator_counterexample :
    let β : ℝ := 2
    firstIndex β 2 = 1 ∧ lastIndex β 7 = 2 ∧
    (intervalPlusCount (fun _ => true) (Nat.floor (β ^ 2)) 7 : ℝ) /
        (β ^ (1 - 1 : ℕ) * (1 - 1 / 2)) >
      (β ^ 3 - β ^ 2) / (β ^ 2 * (1 - 1 / 2)) := by
  dsimp only
  have hl : firstIndex 2 2 = 1 :=
    firstIndex_eq_of_pow_bounds (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hm : lastIndex 2 7 = 2 :=
    lastIndex_eq_of_pow_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hl, hm, ?_⟩
  norm_num [intervalPlusCount, Nat.card_Ioc]

end Freezing1.GeometricHeight
