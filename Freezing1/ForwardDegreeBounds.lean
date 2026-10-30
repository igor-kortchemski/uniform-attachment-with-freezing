module

public import Freezing1.ForwardDegreeProducts

/-!
# Finite bounds for a surviving root of bounded degree

The exact product separates the freezing-survival factors from the
attachment factors. Exponential comparison gives a bound on the actual
joint event, with the correct preceding-population attachment reciprocals.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped ENNReal BigOperators Classical

theorem degreeSurvivalFactor_succ (x : SignSequence) (θ : ℝ) (i : ℕ) :
    degreeSurvivalFactor x θ (i + 1) = vertexSurvivalFactor x (i + 1) *
      (1 + (Real.exp (-θ) - 1) *
        (if x (i + 1) then 1 / (activeCount x i : ℝ) else 0)) := by
  cases hx : x (i + 1) <;>
    simp [degreeSurvivalFactor, vertexSurvivalFactor, hx, div_eq_mul_inv]

theorem degree_attachmentFactor_nonneg {x : SignSequence} {i : ℕ}
    (hi : (i : ℕ∞) < extinctionTime x) (θ : ℝ) :
    0 ≤ 1 + (Real.exp (-θ) - 1) *
      (if x (i + 1) then 1 / (activeCount x i : ℝ) else 0) := by
  have hp := ((lt_extinctionTime_iff x i).mp hi) i le_rfl
  have hS : (1 : ℝ) ≤ activeCount x i := by exact_mod_cast hp
  have hS0 : (0 : ℝ) < activeCount x i := by linarith
  have hrec0 : 0 ≤ 1 / (activeCount x i : ℝ) := by positivity
  have hrec1 : 1 / (activeCount x i : ℝ) ≤ 1 := (div_le_one hS0).mpr hS
  cases x (i + 1)
  · norm_num
  · simp only [↓reduceIte]
    have hh := mul_nonneg (Real.exp_pos (-θ)).le hrec0
    nlinarith

theorem treeLaw_survivingRootWeight_le (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {θ : ℝ} (hθ : 0 ≤ θ) :
    (∫ s, survivingRootWeight θ s ∂treeLaw x n) ≤
      (treeLaw x n).real {s | 0 ∈ s.active} *
        Real.exp ((Real.exp (-θ) - 1) * ∑ i ∈ Finset.range n,
          (if x (i + 1) then 1 / (activeCount x i : ℝ) else 0)) := by
  rw [treeLaw_survivingRootWeight_product x n hn hθ, prod_Ioc_zero_eq_range_succ]
  simp_rw [degreeSurvivalFactor_succ]
  rw [Finset.prod_mul_distrib, ← prod_Ioc_zero_eq_range_succ,
    ← treeLaw_root_survival_product x n hn]
  apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
  calc
    _ ≤ ∏ i ∈ Finset.range n, Real.exp ((Real.exp (-θ) - 1) *
        (if x (i + 1) then 1 / (activeCount x i : ℝ) else 0)) := by
      apply Finset.prod_le_prod₀
        (fun i hi => degree_attachmentFactor_nonneg
          (lt_of_lt_of_le (by exact_mod_cast Finset.mem_range.mp hi) hn) θ)
      intro i _
      simpa only [add_comm] using Real.add_one_le_exp ((Real.exp (-θ) - 1) *
        (if x (i + 1) then 1 / (activeCount x i : ℝ) else 0))
    _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]

theorem treeLaw_active_bounded_degree_le_weight (x : SignSequence) (n d : ℕ)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    (treeLaw x n).real {s | 0 ∈ s.active ∧ rootDegree s ≤ d} ≤
      Real.exp (θ * (d : ℝ)) * (∫ s, survivingRootWeight θ s ∂treeLaw x n) := by
  let E : Set State := {s | 0 ∈ s.active ∧ rootDegree s ≤ d}
  have hi : Integrable (E.indicator (fun _ => (1 : ℝ))) (treeLaw x n) :=
    (integrable_const (1 : ℝ)).indicator (by trivial)
  have hp : ∀ s, E.indicator (fun _ => (1 : ℝ)) s ≤
      Real.exp (θ * (d : ℝ)) * survivingRootWeight θ s := by
    intro s
    by_cases hs : s ∈ E
    · rw [Set.indicator_of_mem hs, survivingRootWeight, ite_eq_left hs.1, ← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      have hd : (rootDegree s : ℝ) ≤ d := by exact_mod_cast hs.2
      have hm := mul_nonneg hθ (sub_nonneg.mpr hd)
      nlinarith
    · rw [Set.indicator_of_notMem hs]
      exact mul_nonneg (Real.exp_pos _).le (survivingRootWeight_bounds hθ s).1
  have hh := integral_mono hi ((integrable_survivingRootWeight hθ (treeLaw x n)).const_mul
    (Real.exp (θ * (d : ℝ)))) hp
  change (∫ s, E.indicator (1 : State → ℝ) s ∂treeLaw x n) ≤ _ at hh
  rw [integral_indicator_one (by trivial), integral_const_mul] at hh
  exact hh

theorem treeLaw_active_bounded_degree_le (x : SignSequence) (n d : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {θ : ℝ} (hθ : 0 ≤ θ) :
    (treeLaw x n).real {s | 0 ∈ s.active ∧ rootDegree s ≤ d} ≤
      Real.exp (θ * (d : ℝ) + (Real.exp (-θ) - 1) * ∑ i ∈ Finset.range n,
        (if x (i + 1) then 1 / (activeCount x i : ℝ) else 0)) := by
  have hp : (treeLaw x n).real {s | 0 ∈ s.active} ≤ 1 := measureReal_le_one
  calc
    _ ≤ Real.exp (θ * (d : ℝ)) * (∫ s, survivingRootWeight θ s ∂treeLaw x n) :=
      treeLaw_active_bounded_degree_le_weight x n d hθ
    _ ≤ Real.exp (θ * (d : ℝ)) *
        ((treeLaw x n).real {s | 0 ∈ s.active} *
          Real.exp ((Real.exp (-θ) - 1) * ∑ i ∈ Finset.range n,
            (if x (i + 1) then 1 / (activeCount x i : ℝ) else 0))) :=
      mul_le_mul_of_nonneg_left (treeLaw_survivingRootWeight_le x n hn hθ) (Real.exp_pos _).le
    _ ≤ Real.exp (θ * (d : ℝ)) *
        Real.exp ((Real.exp (-θ) - 1) * ∑ i ∈ Finset.range n,
          (if x (i + 1) then 1 / (activeCount x i : ℝ) else 0)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

end Freezing1.Forward
