module

public import Freezing1.UniformCoalescence
public import Freezing1.LinearRegimeAssumptions
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Sublinear coalescence time for actual uniform pairs

Only the bulk lower bound is needed for this conclusion. The finite estimate
includes the diagonal probability and applies to all active/frozen pairs.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

theorem inverse_vertex_card_le_two_div_nat {x : SignSequence} {n : ℕ}
    (hn : 0 < n) (hs : 0 ≤ activeCount x n) :
    1 / ((vertexLabels x n).card : ℝ) ≤ 2 / (n : ℝ) := by
  have hcard : (0 : ℝ) < (vertexLabels x n).card := by
    exact_mod_cast (vertexLabels_nonempty hs).card_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_div_iff₀ hcard hnR).mpr
  rw [card_vertexLabels_real hs]
  have hsR : (0 : ℝ) ≤ activeCount x n := by exact_mod_cast hs
  linarith

theorem two_div_mul_sub_one_le_four_div_sq {s : ℝ} (hs : 2 ≤ s) :
    2 / (s * (s - 1)) ≤ 4 / s ^ 2 := by
  have hs0 : 0 < s := by linarith
  apply (div_le_div_iff₀ (mul_pos hs0 (by linarith)) (sq_pos_of_pos hs0)).mpr
  nlinarith

namespace ReverseHistory

theorem uniformCoalescenceLaw_linear_cutoff_tail (x : SignSequence) (n : ℕ)
    (hn : 0 < n) (hτ : (n : ℕ∞) ≤ extinctionTime x)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδn : 2 ≤ δ * n)
    (hwalk : ∀ j : ℕ, ε * n ≤ (j : ℝ) → j ≤ n → δ ≤ (activeCount x j : ℝ) / n) :
    (uniformCoalescenceLaw x n).real {c : ℕ | ε < (c : ℝ) / n} ≤
      2 / (n : ℝ) + (4 / δ ^ 2) / n := by
  let := uniformCoalescenceLaw_probability x n hτ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let i := Nat.floor (ε * n) + 1
  have hsub : {c : ℕ | ε < (c : ℝ) / n} ⊆ {c | i ≤ c} := by
    intro c hc
    apply Nat.succ_le_iff.mpr
    exact (Nat.floor_lt (mul_nonneg hε.le hnR.le)).mpr ((lt_div_iff₀ hnR).mp hc)
  have hwalk' : ∀ j ∈ Finset.Ioc i n, δ * n ≤ (activeCount x j : ℝ) := by
    intro j hj
    rcases Finset.mem_Ioc.mp hj with ⟨hij, hjn⟩
    have hεj : ε * n ≤ (j : ℝ) := (Nat.lt_of_floor_lt (by omega : Nat.floor (ε * n) < j)).le
    exact (le_div_iff₀ hnR).mp (hwalk j hεj hjn)
  calc
    _ ≤ (uniformCoalescenceLaw x n).real {c | i ≤ c} := measureReal_mono hsub
    _ ≤ 1 / ((vertexLabels x n).card : ℝ) +
        ∑ t ∈ Finset.Ioc i n, Reverse.coalescenceHazard x t :=
      uniformCoalescenceLaw_tail_le x n i hτ
    _ ≤ 2 / (n : ℝ) + (n : ℝ) * (2 / ((δ * n) * (δ * n - 1))) :=
      add_le_add (inverse_vertex_card_le_two_div_nat hn
        (activeCount_nonneg_of_le_extinctionTime hτ))
        (sum_coalescenceHazard_le x n i (by linarith) hwalk')
    _ ≤ 2 / (n : ℝ) + (n : ℝ) * (4 / (δ * n) ^ 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (two_div_mul_sub_one_le_four_div_sq hδn) hnR.le)
    _ = _ := by
      congr 1
      field_simp [ne_of_gt hδ, ne_of_gt hnR]

/-- The actual two-uniform-vertex coalescence time divided by `n` tends to
zero in probability. This stronger version uses only the bulk source condition. -/
theorem uniform_coalescence_div_nat_tendsto_zero
    (x : ℕ → SignSequence) (hτ : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n))
    (hbulk : BulkLowerBound x) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (uniformCoalescenceLaw (x n) n).real
      {c : ℕ | ε < (c : ℝ) / n}) atTop (𝓝 0) := by
  let ε' : ℝ := min ε (1 / 2)
  have hε' : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨δ, hδ, hwalk⟩ := hbulk ε' hε' hε'1
  have hnInf : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hδInf : Tendsto (fun n : ℕ => δ * n) atTop atTop := hnInf.const_mul_atTop hδ
  have hbound : Tendsto (fun n : ℕ => 2 / (n : ℝ) + (4 / δ ^ 2) / n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 2 / (n : ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnInf
    have h2 : Tendsto (fun n : ℕ => (4 / δ ^ 2) / n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnInf
    simpa only [add_zero] using h1.add h2
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg) ?_ hbound
  filter_upwards [hwalk, hδInf.eventually_ge_atTop 2, eventually_ge_atTop 1]
    with n hwalkn hδn hn
  let := uniformCoalescenceLaw_probability (x n) n (hτ n)
  have hsub : {k : ℕ | ε < (k : ℝ) / n} ⊆ {k : ℕ | ε' < (k : ℝ) / n} := by
    intro k hk
    exact lt_of_le_of_lt (show ε' ≤ ε from min_le_left ε (1 / 2)) hk
  calc
    _ ≤ (uniformCoalescenceLaw (x n) n).real {c : ℕ | ε' < (c : ℝ) / n} :=
      measureReal_mono hsub
    _ ≤ _ := uniformCoalescenceLaw_linear_cutoff_tail (x n) n (by omega)
      (hτ n) hε' hδ hδn hwalkn

/-- Literal bulk-liminf assumption of the paper, rather than an additional
uniform bound supplied by the user. This is Lemma 9 with the omitted pair
cases included. -/
theorem linear_uniform_coalescence_tendsto_zero
    (x : ℕ → SignSequence) (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hbulk : BulkLiminf x) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (uniformCoalescenceLaw (x n) n).real
      {c : ℕ | ε < (c : ℝ) / n}) atTop (𝓝 0) := by
  apply uniform_coalescence_div_nat_tendsto_zero x (fun n => (hτ n).le) _ hε
  exact (bulkLiminf_iff x (fun n => (lt_extinctionTime_iff (x n) n).mp (hτ n))).mp hbulk

end ReverseHistory
end Freezing1
