module

public import Freezing1.FreezingReciprocalSeries
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Positive freezing density implies the source local-convergence criterion

A summable sequence has a vanishing linearly weighted average, by finite
summation by parts and Cesaro convergence. Applied to freezing indicators
weighted by 1/(i+1), this gives the required reciprocal-series divergence.
-/

@[expose] public section

namespace Freezing1

open Filter
open scoped Topology BigOperators Classical

set_option backward.isDefEq.respectTransparency false

theorem weighted_partialSum_identity (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * a i =
      (n : ℝ) * (∑ i ∈ Finset.range n, a i) -
        ∑ j ∈ Finset.range n, (∑ i ∈ Finset.range j, a i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one, ih]
    ring

theorem summable_weighted_average_tendsto_zero (a : ℕ → ℝ) (ha : Summable a) :
    Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, ((i : ℝ) + 1) * a i) / n)
      atTop (𝓝 0) := by
  have hA := ha.hasSum.tendsto_sum_nat
  have hC := hA.cesaro
  have hh := hA.sub hC
  simp only [sub_self] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [weighted_partialSum_identity]
  field_simp

namespace Forward

noncomputable def freezingTimeReciprocal (x : SignSequence) (i : ℕ) : ℝ :=
  if x (i + 1) then 0 else 1 / ((i : ℝ) + 1)

theorem freezingTimeReciprocal_nonneg (x : SignSequence) (i : ℕ) :
    0 ≤ freezingTimeReciprocal x i := by
  unfold freezingTimeReciprocal
  split_ifs <;> positivity

theorem weighted_freezingTimeReciprocal (x : SignSequence) (i : ℕ) :
    ((i : ℝ) + 1) * freezingTimeReciprocal x i =
      if x (i + 1) then (0 : ℝ) else 1 := by
  have hi : (i : ℝ) + 1 ≠ 0 := by positivity
  cases hx : x (i + 1) <;> simp [freezingTimeReciprocal, hx, one_div, hi]

theorem not_summable_freezingTimeReciprocal_of_density (x : SignSequence) {q : ℝ}
    (hq : 0 < q) (h : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n,
      if x (i + 1) then (0 : ℝ) else 1) / (n : ℝ)) atTop (𝓝 q)) :
    ¬Summable (freezingTimeReciprocal x) := by
  intro hs
  have hh := summable_weighted_average_tendsto_zero (freezingTimeReciprocal x) hs
  simp only [weighted_freezingTimeReciprocal] at hh
  have hz : q = 0 := tendsto_nhds_unique h hh
  linarith

theorem freezingTimeReciprocal_le_printed (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (i : ℕ) :
    freezingTimeReciprocal x i ≤ printedFreezingReciprocal x i := by
  cases hx : x (i + 1)
  · have hS : (0 : ℝ) < activeCount x (i + 1) := by
      exact_mod_cast (extinctionTime_eq_top_iff x).mp hτ (i + 1)
    have hupper : activeCount x (i + 1) ≤ (i : ℤ) + 1 := by
      have hc := activeCount_eq x i
      have hp := plusCount_le x i
      rw [activeCount_succ, hx]
      simp only [Bool.false_eq_true, ite_false]
      omega
    simp only [freezingTimeReciprocal, printedFreezingReciprocal, hx, Bool.false_eq_true, ite_false]
    exact one_div_le_one_div_of_le hS (by exact_mod_cast hupper)
  · simp [freezingTimeReciprocal, printedFreezingReciprocal, hx]

/-- The exact printed reciprocal condition in T01 follows from positive
asymptotic freezing density on every nonextinct schedule. -/
theorem not_summable_printedFreezingReciprocal_of_density (x : SignSequence)
    (hτ : extinctionTime x = ⊤) {q : ℝ} (hq : 0 < q)
    (h : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n,
      if x (i + 1) then (0 : ℝ) else 1) / (n : ℝ)) atTop (𝓝 q)) :
    ¬Summable (printedFreezingReciprocal x) := by
  intro hs
  exact not_summable_freezingTimeReciprocal_of_density x hq h
    (hs.of_nonneg_of_le (freezingTimeReciprocal_nonneg x)
      (freezingTimeReciprocal_le_printed x hτ))

end Forward

end Freezing1
