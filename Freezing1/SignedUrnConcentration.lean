module

public import Freezing1.SignedUrnContinuation
public import Mathlib.Probability.Moments.Basic

/-!
# Finite endpoint concentration for the signed urn

These estimates concern the actual iterated two-point kernel. They suffice
for endpoint component-size estimates; the separate infinite-time maximal
statement in L13 is not asserted here.
-/

@[expose] public section

namespace Freezing1.SignedUrn

open MeasureTheory ProbabilityTheory

/-- Chernoff's upper tail with the exact finite square budget. -/
theorem continuationLaw_upper_tail (Z : ℕ → ℤ) {a k : ℕ} {u : ℤ}
    (hZ : ∀ i ∈ Finset.Icc a (a + k), 0 < Z i)
    (hz : ∀ i ∈ Finset.Ico a (a + k), Z (i + 1) - Z i = 1 ∨ Z (i + 1) - Z i = -1)
    (hu : 0 ≤ u) (huZ : u ≤ Z a) {θ : ℝ} (hθ : 0 ≤ θ)
    (hbudget : |θ| * squareBudget Z a k ≤ 1 / 4)
    (hinc : ∀ i ∈ Finset.Ioc a (a + k), |θ / (Z i : ℝ)| ≤ 1 / 4) (t : ℝ) :
    (continuationLaw Z a k u).real
      {v | (1 + t) * ((u : ℝ) / Z a) ≤ (v : ℝ) / Z (a + k)} ≤
      Real.exp ((θ ^ 2 * squareBudget Z a k - θ * t) * ((u : ℝ) / Z a)) := by
  calc
    _ ≤ Real.exp (-θ * ((1 + t) * ((u : ℝ) / Z a))) *
        mgf (fun v : ℤ => (v : ℝ) / Z (a + k)) (continuationLaw Z a k u) θ :=
      measure_ge_le_exp_mul_mgf _ hθ (continuationLaw_integrable Z a k u _)
    _ ≤ Real.exp (-θ * ((1 + t) * ((u : ℝ) / Z a))) *
        Real.exp ((θ * (1 + θ * squareBudget Z a k)) * ((u : ℝ) / Z a)) :=
      mul_le_mul_of_nonneg_left (continuationLaw_exponential_le Z hZ hz hu huZ hbudget hinc)
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- A parameter inside both MGF budgets, with the paper's denominator 4.
It avoids a case distinction between the Gaussian and linear tail ranges. -/
theorem chernoff_parameter_cost {D M t : ℝ} (hD : 0 < D) (hM : 0 ≤ M)
    (ht : 0 ≤ t) :
    let θ := t / (2 * D + 4 * M * t)
    0 ≤ θ ∧ θ * M ≤ 1 / 4 ∧
      t ^ 2 / (4 * (D + t * M)) ≤ θ * t - θ ^ 2 * D := by
  dsimp
  have hd : 0 < 2 * D + 4 * M * t := by positivity
  have hd' : 0 < D + t * M := by positivity
  refine ⟨div_nonneg ht hd.le, ?_, ?_⟩
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  · have he : t / (2 * D + 4 * M * t) * t -
        (t / (2 * D + 4 * M * t)) ^ 2 * D - t ^ 2 / (4 * (D + t * M)) =
        D * M * t ^ 3 / ((2 * D + 4 * M * t) ^ 2 * (D + t * M)) := by
      field_simp [hd.ne', hd'.ne']
      ring
    have hn : 0 ≤ D * M * t ^ 3 / ((2 * D + 4 * M * t) ^ 2 * (D + t * M)) :=
      div_nonneg (by positivity) (by positivity)
    linarith

/-- The finite signed urn has the source exponential scale, with any explicit
upper bound D on its square budget and M on D and every reciprocal population.
This is an endpoint inequality; it does not assert L13's running supremum. -/
theorem continuationLaw_upper_tail_optimized (Z : ℕ → ℤ) {a k : ℕ} {u : ℤ}
    (hZ : ∀ i ∈ Finset.Icc a (a + k), 0 < Z i)
    (hz : ∀ i ∈ Finset.Ico a (a + k), Z (i + 1) - Z i = 1 ∨ Z (i + 1) - Z i = -1)
    (hu : 0 ≤ u) (huZ : u ≤ Z a) {D M t : ℝ} (hD : 0 < D) (hDM : D ≤ M)
    (hbudget : squareBudget Z a k ≤ D)
    (hinc : ∀ i ∈ Finset.Ioc a (a + k), (Z i : ℝ)⁻¹ ≤ M) (ht : 0 ≤ t) :
    (continuationLaw Z a k u).real
      {v | (1 + t) * ((u : ℝ) / Z a) ≤ (v : ℝ) / Z (a + k)} ≤
      Real.exp (-(t ^ 2 * ((u : ℝ) / Z a)) / (4 * (D + t * M))) := by
  let θ := t / (2 * D + 4 * M * t)
  obtain ⟨hθ, hθM, hcost⟩ := chernoff_parameter_cost hD (hD.le.trans hDM) ht
  change 0 ≤ θ at hθ
  change θ * M ≤ 1 / 4 at hθM
  change t ^ 2 / (4 * (D + t * M)) ≤ θ * t - θ ^ 2 * D at hcost
  have hθB : |θ| * squareBudget Z a k ≤ 1 / 4 := by
    rw [abs_of_nonneg hθ]
    exact (mul_le_mul_of_nonneg_left (hbudget.trans hDM) hθ).trans hθM
  have hθi : ∀ i ∈ Finset.Ioc a (a + k), |θ / (Z i : ℝ)| ≤ 1 / 4 := by
    intro i hi
    have hZi : (0 : ℝ) < Z i := by
      exact_mod_cast hZ i (Finset.mem_Icc.mpr
        ⟨(Finset.mem_Ioc.mp hi).1.le, (Finset.mem_Ioc.mp hi).2⟩)
    rw [abs_of_nonneg (div_nonneg hθ hZi.le), div_eq_mul_inv]
    exact (mul_le_mul_of_nonneg_left (hinc i hi) hθ).trans hθM
  apply (continuationLaw_upper_tail Z hZ hz hu huZ hθ hθB hθi t).trans
  apply Real.exp_le_exp.mpr
  have hx : 0 ≤ (u : ℝ) / Z a :=
    div_nonneg (by exact_mod_cast hu) (by exact_mod_cast (hZ a (by simp)).le)
  have hc : θ ^ 2 * squareBudget Z a k - θ * t ≤ -t ^ 2 / (4 * (D + t * M)) := by
    have hh := mul_le_mul_of_nonneg_left hbudget (sq_nonneg θ)
    rw [neg_div]
    linarith
  convert mul_le_mul_of_nonneg_right hc hx using 1; ring

end Freezing1.SignedUrn
