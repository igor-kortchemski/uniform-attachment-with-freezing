module

public import Freezing1.BernoulliArrayLimits
public import Freezing1.HeightScale

/-!
# Bernoulli sums with the paper's height normalization

For an admissible schedule the parameter is `1 / S_(i+1)` at an attachment
step and zero at a freezing step. Indices beyond the horizon are zero, so the
finite row may be represented by a family on the common index type `ℕ`.
The exact sum of the parameters is `heightScale`.

The limit below is still a statement about independent Bernoulli sums. The
identification with an active vertex height is a separate probabilistic theorem.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

/-- The height-increment parameter, with indices outside the row assigned zero. -/
noncomputable def scheduleBernoulliParameter (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) (i : ℕ) : unitInterval :=
  if hi : i < n then
    ⟨if x (i + 1) then 1 / (activeCount x (i + 1) : ℝ) else 0, by
      have hS : (1 : ℝ) ≤ (activeCount x (i + 1) : ℝ) := by
        have hs : (1 : ℤ) ≤ activeCount x (i + 1) := by
          have := h (i + 1) (by omega)
          omega
        exact_mod_cast hs
      split
      · exact ⟨by positivity, (div_le_one (lt_of_lt_of_le zero_lt_one hS)).mpr hS⟩
      · exact ⟨le_rfl, zero_le_one⟩⟩
  else 0

theorem scheduleBernoulliParameter_coe_of_lt (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) {i : ℕ} (hi : i < n) :
    (scheduleBernoulliParameter x n h i : ℝ) =
      if x (i + 1) then 1 / (activeCount x (i + 1) : ℝ) else 0 := by
  simp [scheduleBernoulliParameter, hi]

@[simp] theorem scheduleBernoulliParameter_eq_zero_of_le (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) {i : ℕ} (hi : n ≤ i) :
    scheduleBernoulliParameter x n h i = 0 := by
  simp [scheduleBernoulliParameter, not_lt.mpr hi]

/-- No normalization is assumed: the Bernoulli mean is exactly the paper's sum. -/
theorem sum_scheduleBernoulliParameter (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) :
    (∑ i ∈ Finset.range n, (scheduleBernoulliParameter x n h i : ℝ)) = heightScale x n := by
  unfold heightScale
  apply Finset.sum_congr rfl
  intro i hi
  exact scheduleBernoulliParameter_coe_of_lt x n h (Finset.mem_range.mp hi)

/-- The Bernoulli-sum part of the active-height limit for every admissible
triangular array of schedules, on arbitrary horizon-dependent probability spaces. -/
theorem scheduleBernoulli_tendsto_Lp
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    {ν : ∀ n, Measure (Ξ n)} [∀ n, IsProbabilityMeasure (ν n)]
    (x : ℕ → SignSequence) (h : ∀ n, PositiveThrough (x n) n)
    {Y : ∀ n, ℕ → Ξ n → ℝ}
    (hY : ∀ n i, Measurable (Y n i)) (h_indep : ∀ n, iIndepFun (Y n) (ν n))
    (hLaw : ∀ n i, HasLaw (Y n i)
      (bernoulliMeasure (1 : ℝ) 0 (scheduleBernoulliParameter (x n) n (h n) i)) (ν n))
    {r : ℝ} (hr : 1 ≤ r) :
    Tendsto (fun n ↦ eLpNorm
      (fun ω ↦ (∑ i ∈ Finset.range n, Y n i ω) / heightScale (x n) n - 1)
      (ENNReal.ofReal r) (ν n)) atTop (𝓝 0) := by
  have hm : Tendsto (fun n ↦ ∑ i ∈ Finset.range n,
      (scheduleBernoulliParameter (x n) n (h n) i : ℝ)) atTop atTop := by
    simpa only [sum_scheduleBernoulliParameter] using tendsto_heightScale_atTop x h
  simpa only [sum_scheduleBernoulliParameter] using
    bernoulli_normalized_tendsto_Lp_varying hY h_indep hLaw Finset.range hm hr

end Freezing1
