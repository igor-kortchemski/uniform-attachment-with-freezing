module

public import Freezing1.Extinction
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Tactic

/-!
# Corrected and printed freezing reciprocals have the same convergence

On a freezing step the preceding active count is the following count plus
one. If extinction never occurs, both are positive integers, and replacing
the correct preceding count by the printed following count changes the
reciprocal by at most a factor of two. The finite products are different,
but convergence or divergence of their reciprocal series is equivalent.
-/

@[expose] public section

namespace Freezing1.Forward

noncomputable def freezingHazard (x : SignSequence) (i : ℕ) : ℝ :=
  if x (i + 1) then 0 else 1 / (activeCount x i : ℝ)

noncomputable def printedFreezingReciprocal (x : SignSequence) (i : ℕ) : ℝ :=
  if x (i + 1) then 0 else 1 / (activeCount x (i + 1) : ℝ)

theorem freezing_reciprocal_comparison (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (i : ℕ) (hx : x (i + 1) = false) :
    1 / (activeCount x i : ℝ) ≤ 1 / (activeCount x (i + 1) : ℝ) ∧
      1 / (activeCount x (i + 1) : ℝ) ≤ 2 * (1 / (activeCount x i : ℝ)) := by
  have hp := (extinctionTime_eq_top_iff x).mp hτ
  have hp0 : (0 : ℝ) < activeCount x i := by exact_mod_cast hp i
  have hp1 : (0 : ℝ) < activeCount x (i + 1) := by exact_mod_cast hp (i + 1)
  have hge : (1 : ℝ) ≤ activeCount x (i + 1) := by
    exact_mod_cast (show (1 : ℤ) ≤ activeCount x (i + 1) by have := hp (i + 1); omega)
  have hs := activeCount_succ x i
  simp only [hx, Bool.false_eq_true, ↓reduceIte] at hs
  have hsR : (activeCount x i : ℝ) = (activeCount x (i + 1) : ℝ) + 1 := by
    exact_mod_cast (show activeCount x i = activeCount x (i + 1) + 1 by omega)
  constructor
  · apply (div_le_div_iff₀ hp0 hp1).mpr
    linarith
  · calc
      1 / (activeCount x (i + 1) : ℝ) ≤ 2 / (activeCount x i : ℝ) := by
        apply (div_le_div_iff₀ hp1 hp0).mpr
        linarith
      _ = _ := by ring

theorem freezingHazard_nonneg (x : SignSequence) (hτ : extinctionTime x = ⊤) (i : ℕ) :
    0 ≤ freezingHazard x i := by
  have hp : (0 : ℝ) < activeCount x i := by
    exact_mod_cast (extinctionTime_eq_top_iff x).mp hτ i
  unfold freezingHazard
  split_ifs <;> positivity

theorem printedFreezingReciprocal_nonneg (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (i : ℕ) :
    0 ≤ printedFreezingReciprocal x i := by
  have hp : (0 : ℝ) < activeCount x (i + 1) := by
    exact_mod_cast (extinctionTime_eq_top_iff x).mp hτ (i + 1)
  unfold printedFreezingReciprocal
  split_ifs <;> positivity

theorem freezingHazard_le_half (x : SignSequence) (hτ : extinctionTime x = ⊤) (i : ℕ) :
    freezingHazard x i ≤ 1 / 2 := by
  cases hx : x (i + 1)
  · have hp := (extinctionTime_eq_top_iff x).mp hτ (i + 1)
    have hs := activeCount_succ x i
    simp only [hx, Bool.false_eq_true, ↓reduceIte] at hs
    have hge : (2 : ℝ) ≤ activeCount x i := by
      exact_mod_cast (show (2 : ℤ) ≤ activeCount x i by omega)
    simp only [freezingHazard, hx, Bool.false_eq_true, ↓reduceIte]
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hge
  · simp [freezingHazard, hx]

theorem freezingHazard_lt_one (x : SignSequence) (hτ : extinctionTime x = ⊤) (i : ℕ) :
    freezingHazard x i < 1 :=
  (freezingHazard_le_half x hτ i).trans_lt (by norm_num)

theorem freezingHazard_comparison (x : SignSequence) (hτ : extinctionTime x = ⊤) (i : ℕ) :
    freezingHazard x i ≤ printedFreezingReciprocal x i ∧
      printedFreezingReciprocal x i ≤ 2 * freezingHazard x i := by
  cases hx : x (i + 1)
  · simpa only [freezingHazard, printedFreezingReciprocal, hx, Bool.false_eq_true, ↓reduceIte]
      using freezing_reciprocal_comparison x hτ i hx
  · simp [freezingHazard, printedFreezingReciprocal, hx]

theorem summable_freezingHazard_iff (x : SignSequence) (hτ : extinctionTime x = ⊤) :
    Summable (freezingHazard x) ↔ Summable (printedFreezingReciprocal x) := by
  constructor
  · intro h
    exact (h.mul_left 2).of_nonneg_of_le (printedFreezingReciprocal_nonneg x hτ)
      (fun i => (freezingHazard_comparison x hτ i).2)
  · intro h
    exact h.of_nonneg_of_le (freezingHazard_nonneg x hτ)
      (fun i => (freezingHazard_comparison x hτ i).1)

end Freezing1.Forward
