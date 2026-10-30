module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic

/-!
# The zero-limit criterion for survival products

For nonnegative risks strictly below one, the finite survival products tend
to zero precisely when the risk series diverges. In the summable case,
Mathlib's logarithm theorem identifies a strictly positive product limit.
Removing finitely many initial risks leaves the criterion unchanged.
-/

@[expose] public section

namespace Freezing1

open Filter
open scoped Topology BigOperators

theorem survivalProduct_le_exp_neg_sum {p : ℕ → ℝ} (hp1 : ∀ i, p i ≤ 1) (n : ℕ) :
    (∏ i ∈ Finset.range n, (1 - p i)) ≤ Real.exp (-(∑ i ∈ Finset.range n, p i)) := by
  calc
    _ ≤ ∏ i ∈ Finset.range n, Real.exp (-p i) := by
      apply Finset.prod_le_prod₀ (fun i _ => sub_nonneg.mpr (hp1 i))
      intro i _
      have hh := Real.add_one_le_exp (-p i)
      linarith
    _ = Real.exp (∑ i ∈ Finset.range n, -p i) := (Real.exp_sum _ _).symm
    _ = _ := by rw [Finset.sum_neg_distrib]

theorem tendsto_survivalProduct_of_summable {p : ℕ → ℝ}
    (hp1 : ∀ i, p i < 1) (hs : Summable p) :
    Tendsto (fun n => ∏ i ∈ Finset.range n, (1 - p i)) atTop
      (𝓝 (Real.exp (∑' i, Real.log (1 - p i)))) := by
  have hlog : Summable (fun i => Real.log (1 - p i)) := by
    simpa only [sub_eq_add_neg] using Real.summable_log_one_add_of_summable hs.neg
  exact (Real.hasProd_of_hasSum_log (fun i => sub_pos.mpr (hp1 i)) hlog.hasSum).tendsto_prod_nat

theorem tendsto_survivalProduct_zero_iff_not_summable {p : ℕ → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1) :
    Tendsto (fun n => ∏ i ∈ Finset.range n, (1 - p i)) atTop (𝓝 0) ↔ ¬Summable p := by
  constructor
  · intro hz hs
    have he := tendsto_nhds_unique (tendsto_survivalProduct_of_summable hp1 hs) hz
    exact Real.exp_ne_zero _ he
  · intro hs
    have hsum := (not_summable_iff_tendsto_nat_atTop_of_nonneg hp0).mp hs
    have he := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hsum)
    simp only [Function.comp_def] at he
    apply squeeze_zero (fun n => Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hp1 i).le))
      (survivalProduct_le_exp_neg_sum (fun i => (hp1 i).le)) he

theorem tendsto_survivalProduct_tail_zero_iff_not_summable {p : ℕ → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1) (a : ℕ) :
    Tendsto (fun n => ∏ i ∈ Finset.Ico a (a + n), (1 - p i)) atTop (𝓝 0) ↔
      ¬Summable p := by
  have hh := tendsto_survivalProduct_zero_iff_not_summable
    (fun i => hp0 (a + i)) (fun i => hp1 (a + i))
  have hshift : Summable (fun i => p (a + i)) ↔ Summable p := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff a (f := p))
  simpa only [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel_left, hshift] using hh

end Freezing1
