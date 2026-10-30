module

public import Freezing1.SignedUrnPath
public import Freezing1.SignedUrnConcentration

/-!
# Finite maximal concentration of the signed urn

The event ranges over all coordinates of the actual trajectory. The argument
uses backward exponential comparison, rather than an assumed martingale or
independence between different times. Infinite-time passage is separate.
-/

@[expose] public section

namespace Freezing1.SignedUrn

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

def deviates (Z : ℕ → ℤ) (x t : ℝ) : ℕ → List ℤ → Prop
  | _, [] => False
  | a, u :: us => t * x < |(u : ℝ) / Z a - x| ∨ deviates Z x t (a + 1) us

/-- The recursive event is exactly a deviation at some recorded time. -/
theorem deviates_iff_exists (Z : ℕ → ℤ) (x t : ℝ) (a : ℕ) (us : List ℤ) :
    deviates Z x t a us ↔
      ∃ i, i < us.length ∧ t * x < |((us.getD i 0 : ℤ) : ℝ) / Z (a + i) - x| := by
  induction us generalizing a with
  | nil => simp [deviates]
  | cons u us ih =>
    simp only [deviates, ih, List.length_cons]
    constructor
    · rintro (h | ⟨i, hi, hd⟩)
      · exact ⟨0, by simp, by simpa using h⟩
      · refine ⟨i + 1, by simpa using hi, ?_⟩
        simpa only [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm 1] using hd
    · rintro ⟨i, hi, hd⟩
      cases i with
      | zero => exact Or.inl (by simpa using hd)
      | succ i =>
        refine Or.inr ⟨i, by omega, ?_⟩
        simpa only [List.getD_cons_succ, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1] using hd

theorem deviates_subset_crossings (Z : ℕ → ℤ) (x t : ℝ) {θ : ℝ}
    (hθ : 0 < θ) (a : ℕ) (us : List ℤ) :
    deviates Z x t a us →
      crosses Z θ (θ * (1 + t) * x) a us ∨
        crosses Z (-θ) ((-θ) * (1 - t) * x) a us := by
  induction us generalizing a with
  | nil => simp [deviates]
  | cons u us ih =>
    rintro (h | h)
    · rcases lt_abs.mp h with h | h
      · apply Or.inl; apply Or.inl
        have hh := mul_lt_mul_of_pos_left h hθ
        nlinarith
      · apply Or.inr; apply Or.inl
        have hh := mul_lt_mul_of_pos_left h hθ
        nlinarith
    · rcases ih (a + 1) h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)

/-- Two-sided maximal concentration at any finite horizon, before choosing θ. -/
theorem pathLaw_maximal_chernoff (Z : ℕ → ℤ) {a k : ℕ} {u : ℤ}
    (hZ : ∀ i ∈ Finset.Icc a (a + k), 0 < Z i)
    (hz : ∀ i ∈ Finset.Ico a (a + k), Z (i + 1) - Z i = 1 ∨ Z (i + 1) - Z i = -1)
    (hu : 0 ≤ u) (huZ : u ≤ Z a) {θ : ℝ} (hθ : 0 < θ)
    (hbudget : |θ| * squareBudget Z a k ≤ 1 / 4)
    (hinc : ∀ i ∈ Finset.Ioc a (a + k), |θ / (Z i : ℝ)| ≤ 1 / 4) (t : ℝ) :
    (pathLaw Z a k u).real {H | deviates Z ((u : ℝ) / Z a) t a H.values} ≤
      2 * Real.exp ((θ ^ 2 * squareBudget Z a k - θ * t) * ((u : ℝ) / Z a)) := by
  let x := (u : ℝ) / Z a
  have hp := crossingProbability_le Z hZ hz hu huZ hbudget hinc (θ * (1 + t) * x)
  have hm := crossingProbability_le Z hZ hz hu huZ
    (θ := -θ) (by simpa only [abs_neg] using hbudget)
    (fun i hi => by simpa only [neg_div, abs_neg] using hinc i hi)
    ((-θ) * (1 - t) * x)
  have ep : (θ * (1 + θ * squareBudget Z a k)) * x - θ * (1 + t) * x =
      (θ ^ 2 * squareBudget Z a k - θ * t) * x := by ring
  have em : ((-θ) * (1 + (-θ) * squareBudget Z a k)) * x - (-θ) * (1 - t) * x =
      (θ ^ 2 * squareBudget Z a k - θ * t) * x := by ring
  change crossingProbability Z a k u θ _ ≤ Real.exp _ at hp
  change crossingProbability Z a k u (-θ) _ ≤ Real.exp _ at hm
  rw [show (u : ℝ) / Z a = x from rfl, ep] at hp
  rw [show (u : ℝ) / Z a = x from rfl, em] at hm
  calc
    _ ≤ (pathLaw Z a k u).real
        ({H | crosses Z θ (θ * (1 + t) * x) a H.values} ∪
          {H | crosses Z (-θ) ((-θ) * (1 - t) * x) a H.values}) := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro H hH
      exact deviates_subset_crossings Z x t hθ a H.values hH
    _ ≤ crossingProbability Z a k u θ (θ * (1 + t) * x) +
        crossingProbability Z a k u (-θ) ((-θ) * (1 - t) * x) := measureReal_union_le _ _
    _ ≤ _ := by dsimp [x] at hp hm ⊢; linarith

/-- The paper's maximal tail scale for the actual finite signed urn path.
The bound is uniform in the horizon whenever D and M are uniform budgets. -/
theorem pathLaw_maximal_optimized (Z : ℕ → ℤ) {a k : ℕ} {u : ℤ}
    (hZ : ∀ i ∈ Finset.Icc a (a + k), 0 < Z i)
    (hz : ∀ i ∈ Finset.Ico a (a + k), Z (i + 1) - Z i = 1 ∨ Z (i + 1) - Z i = -1)
    (hu : 0 ≤ u) (huZ : u ≤ Z a) {D M t : ℝ} (hD : 0 < D) (hDM : D ≤ M)
    (hbudget : squareBudget Z a k ≤ D)
    (hinc : ∀ i ∈ Finset.Ioc a (a + k), (Z i : ℝ)⁻¹ ≤ M) (ht : 0 ≤ t) :
    (pathLaw Z a k u).real {H | deviates Z ((u : ℝ) / Z a) t a H.values} ≤
      2 * Real.exp (-(t ^ 2 * ((u : ℝ) / Z a)) / (4 * (D + t * M))) := by
  by_cases ht0 : t = 0
  · subst t
    simpa using (measureReal_le_one (μ := pathLaw Z a k u)
      (s := {H | deviates Z ((u : ℝ) / Z a) 0 a H.values})).trans (by norm_num : (1 : ℝ) ≤ 2)
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hM : 0 ≤ M := hD.le.trans hDM
  let θ := t / (2 * D + 4 * M * t)
  have hθp : 0 < θ := div_pos htp (by positivity)
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
  apply (pathLaw_maximal_chernoff Z hZ hz hu huZ hθp hθB hθi t).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  have hx : 0 ≤ (u : ℝ) / Z a :=
    div_nonneg (by exact_mod_cast hu) (by exact_mod_cast (hZ a (by simp)).le)
  have hc : θ ^ 2 * squareBudget Z a k - θ * t ≤ -t ^ 2 / (4 * (D + t * M)) := by
    have hh := mul_le_mul_of_nonneg_left hbudget (sq_nonneg θ)
    rw [neg_div]
    linarith
  convert mul_le_mul_of_nonneg_right hc hx using 1; ring

end Freezing1.SignedUrn
