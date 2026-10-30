module

public import Freezing1.HeightScale
public import Freezing1.Extinction
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Divergence of the actual attachment selection probabilities

At attachment step i+1 a specified active vertex is selected with probability
1/S_i. This is at least the reciprocal 1/S_(i+1) in the already proved height
scale. Consequently the cumulative selection probability diverges whenever
the schedule never becomes extinct.
-/

@[expose] public section

namespace Freezing1.Forward

open Filter
open scoped Topology BigOperators

noncomputable def attachmentHazard (x : SignSequence) (i : ℕ) : ℝ :=
  if x (i + 1) then 1 / (activeCount x i : ℝ) else 0

theorem attachmentHazard_nonneg (x : SignSequence) (hτ : extinctionTime x = ⊤) (i : ℕ) :
    0 ≤ attachmentHazard x i := by
  have hp : (0 : ℝ) < activeCount x i := by
    exact_mod_cast (extinctionTime_eq_top_iff x).mp hτ i
  unfold attachmentHazard
  split_ifs <;> positivity

theorem attachmentHazard_le_one (x : SignSequence) (hτ : extinctionTime x = ⊤) (i : ℕ) :
    attachmentHazard x i ≤ 1 := by
  have hp := (extinctionTime_eq_top_iff x).mp hτ i
  have hge : (1 : ℝ) ≤ activeCount x i := by
    exact_mod_cast (show (1 : ℤ) ≤ activeCount x i by omega)
  unfold attachmentHazard
  split_ifs
  · exact (div_le_one (by linarith)).mpr hge
  · norm_num

theorem heightScale_le_sum_attachmentHazard (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (n : ℕ) :
    heightScale x n ≤ ∑ i ∈ Finset.range n, attachmentHazard x i := by
  unfold heightScale
  apply Finset.sum_le_sum
  intro i _
  cases hx : x (i + 1)
  · simp only [attachmentHazard, hx, Bool.false_eq_true, ↓reduceIte, le_refl]
  · simp only [attachmentHazard, hx, ↓reduceIte]
    have hp : (0 : ℝ) < activeCount x i := by
      exact_mod_cast (extinctionTime_eq_top_iff x).mp hτ i
    have hs := activeCount_succ x i
    simp only [hx, ↓reduceIte] at hs
    have hle : (activeCount x i : ℝ) ≤ activeCount x (i + 1) := by
      exact_mod_cast (show activeCount x i ≤ activeCount x (i + 1) by omega)
    exact one_div_le_one_div_of_le hp hle

theorem tendsto_sum_attachmentHazard_atTop (x : SignSequence)
    (hτ : extinctionTime x = ⊤) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, attachmentHazard x i) atTop atTop := by
  have hh := tendsto_heightScale_atTop (fun _ => x)
    (fun n i _ => (extinctionTime_eq_top_iff x).mp hτ i)
  exact tendsto_atTop_mono' atTop
    (Eventually.of_forall (heightScale_le_sum_attachmentHazard x hτ)) hh

theorem not_summable_attachmentHazard (x : SignSequence) (hτ : extinctionTime x = ⊤) :
    ¬Summable (attachmentHazard x) :=
  (not_summable_iff_tendsto_nat_atTop_of_nonneg (attachmentHazard_nonneg x hτ)).mpr
    (tendsto_sum_attachmentHazard_atTop x hτ)

end Freezing1.Forward
