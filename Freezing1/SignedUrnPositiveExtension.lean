module

public import Freezing1.ForwardPositiveExtension
public import Freezing1.SignedUrnInfinite
public import Freezing1.LinearComponentTail

/-! The source's shifted infinite positive extension and its exact budgets. -/

@[expose] public section

namespace Freezing1.SignedUrn

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

theorem continuationLaw_shift (Z : ℕ → ℤ) (offset a k : ℕ) (u : ℤ) :
    continuationLaw (fun i => Z (offset + i)) a k u = continuationLaw Z (offset + a) k u := by
  induction k generalizing a u with
  | zero => rfl
  | succ k ih =>
    simp only [continuationLaw, Nat.add_assoc]
    congr 1
    funext v
    exact ih (a + 1) v

theorem continuationLaw_congr_population {Z W : ℕ → ℤ} (a k : ℕ) (u : ℤ)
    (h : ∀ i ∈ Finset.Icc a (a + k), Z i = W i) :
    continuationLaw Z a k u = continuationLaw W a k u := by
  induction k generalizing a u with
  | zero => rfl
  | succ k ih =>
    rw [continuationLaw, continuationLaw, h a (by simp), h (a + 1) (by simp)]
    congr 1
    funext v
    apply ih
    intro i hi
    exact h i (by simp only [Finset.mem_Icc] at hi ⊢; omega)

theorem squareBudget_shift (Z : ℕ → ℤ) (offset a k : ℕ) :
    squareBudget (fun i => Z (offset + i)) a k = squareBudget Z (offset + a) k := by
  induction k generalizing a with
  | zero => simp [squareBudget]
  | succ k ih => simp only [squareBudget_succ, ih, Nat.add_assoc]

def positiveExtensionPopulation (x : SignSequence) (a b : ℕ) : ℕ → ℤ :=
  fun i => activeCount (positiveExtension x b) (a + i)

theorem positiveExtensionPopulation_retained (x : SignSequence) {a b i : ℕ}
    (hab : a ≤ b) (hi : i ≤ b - a) :
    positiveExtensionPopulation x a b i = activeCount x (a + i) :=
  activeCount_positiveExtension_prefix x b (by omega)

theorem positiveExtensionPopulation_zero (x : SignSequence) {a b : ℕ} (hab : a ≤ b) :
    positiveExtensionPopulation x a b 0 = activeCount x a := by
  simpa only [Nat.add_zero] using positiveExtensionPopulation_retained x hab (Nat.zero_le (b - a))

theorem positiveExtensionPopulation_tail (x : SignSequence) {a b : ℕ} (hab : a ≤ b) (j : ℕ) :
    positiveExtensionPopulation x a b (b - a + j) = activeCount x b + (j : ℤ) := by
  unfold positiveExtensionPopulation
  rw [show a + (b - a + j) = b + j by omega, activeCount_positiveExtension_tail]

theorem positiveExtensionPopulation_positive (x : SignSequence) {a b : ℕ}
    (hb : PositiveThrough x b) (i : ℕ) :
    0 < positiveExtensionPopulation x a b i := positiveExtension_positive x hb (a + i)

theorem positiveExtensionPopulation_steps (x : SignSequence) {a b : ℕ} (hab : a ≤ b) (i : ℕ) :
    positiveExtensionPopulation x a b (i + 1) - positiveExtensionPopulation x a b i =
      if i + 1 ≤ b - a then (if x (a + i + 1) then 1 else -1) else 1 := by
  unfold positiveExtensionPopulation
  rw [show a + (i + 1) = a + i + 1 by omega, activeCount_succ]
  unfold positiveExtension
  by_cases hi : i + 1 ≤ b - a
  · simp only [ite_eq_left hi, ite_eq_left (show a + i + 1 ≤ b by omega)]
    omega
  · simp only [ite_eq_right hi, ite_eq_right (show ¬a + i + 1 ≤ b by omega), ↓reduceIte]
    omega

theorem positiveExtensionPopulation_signed (x : SignSequence) {a b : ℕ} (hab : a ≤ b) (i : ℕ) :
    positiveExtensionPopulation x a b (i + 1) - positiveExtensionPopulation x a b i = 1 ∨
      positiveExtensionPopulation x a b (i + 1) - positiveExtensionPopulation x a b i = -1 := by
  rw [positiveExtensionPopulation_steps x hab i]
  split_ifs <;> simp

/-- The exact original finite component count is an endpoint of the source
infinite population extension, initialized at one true active descendant. -/
theorem positiveExtension_original_component_endpoint {x : SignSequence} {a b : ℕ}
    {s : Forward.State} (hd : Forward.PhaseData x a s) (hab : a ≤ b) (hb : PositiveThrough x b)
    {r : ℕ} (hr : r ∈ s.active) :
    (Forward.continuationLaw x a (b - a) s).map
        (fun t => Forward.componentPopulation t a r) =
      continuationLaw (positiveExtensionPopulation x a b) 0 (b - a) 1 := by
  rw [Forward.continuationLaw_componentPopulation_of_root hd
    (by simpa only [Nat.add_sub_of_le hab] using ((lt_extinctionTime_iff x b).mpr hb).le) hr]
  change continuationLaw (activeCount x) a (b - a) 1 =
    continuationLaw (fun i => activeCount (positiveExtension x b) (a + i)) 0 (b - a) 1
  rw [continuationLaw_shift, Nat.add_zero]
  apply continuationLaw_congr_population
  intro i hi
  exact (activeCount_positiveExtension_prefix x b (by have := (Finset.mem_Icc.mp hi).2; omega)).symm

theorem inv_sq_succ_le_sub {z : ℝ} (hz : 0 < z) :
    ((z + 1)⁻¹) ^ 2 ≤ z⁻¹ - (z + 1)⁻¹ := by
  have hz1 : 0 < z + 1 := by linarith
  have he : z⁻¹ - (z + 1)⁻¹ = (z * (z + 1))⁻¹ := by
    field_simp
    ring
  rw [he, inv_pow]
  simpa only [one_div] using one_div_le_one_div_of_le (mul_pos hz hz1) (by nlinarith only [hz])

theorem reciprocal_tail_square_partial {z : ℝ} (hz : 0 < z) (k : ℕ) :
    (∑ i ∈ Finset.range k, ((z + (i + 1 : ℕ))⁻¹) ^ 2) ≤ z⁻¹ - (z + k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hzK : 0 < z + (k : ℝ) := by positivity
    have hh := inv_sq_succ_le_sub hzK
    push_cast at ih hh ⊢
    have hadd : z + (k : ℝ) + 1 = z + ((k : ℝ) + 1) := by ring
    rw [hadd] at hh
    linarith only [ih, hh]

theorem reciprocal_tail_square_summable {z : ℝ} (hz : 0 < z) :
    Summable (fun i : ℕ => ((z + (i + 1 : ℕ))⁻¹) ^ 2) := by
  apply summable_of_sum_range_le (fun _ => sq_nonneg _) (c := z⁻¹)
  intro k
  exact (reciprocal_tail_square_partial hz k).trans (sub_le_self _ (by positivity))

theorem reciprocal_tail_square_le {z : ℝ} (hz : 0 < z) :
    (∑' i : ℕ, ((z + (i + 1 : ℕ))⁻¹) ^ 2) ≤ z⁻¹ := by
  apply Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _)
  intro k
  exact (reciprocal_tail_square_partial hz k).trans (sub_le_self _ (by positivity))

theorem positiveExtension_square_summable (x : SignSequence) {a b : ℕ} (hab : a ≤ b)
    (hb : PositiveThrough x b) :
    Summable (fun i : ℕ => ((positiveExtensionPopulation x a b (i + 1) : ℝ)⁻¹) ^ 2) := by
  apply (summable_nat_add_iff (b - a)).mp
  have hS : 0 < (activeCount x b : ℝ) := by exact_mod_cast hb b le_rfl
  apply (reciprocal_tail_square_summable hS).congr
  intro i
  rw [show i + (b - a) + 1 = b - a + (i + 1) by omega,
    positiveExtensionPopulation_tail x hab (i + 1)]
  push_cast
  rfl

theorem positiveExtension_square_budget_eq (x : SignSequence) {a b : ℕ} (hab : a ≤ b)
    (hb : PositiveThrough x b) :
    infiniteSquareBudget (positiveExtensionPopulation x a b) = squareBudget (activeCount x) a (b - a) +
      ∑' j : ℕ, (((activeCount x b : ℝ) + (j + 1 : ℕ))⁻¹) ^ 2 := by
  have hs := positiveExtension_square_summable x hab hb
  unfold infiniteSquareBudget
  rw [← hs.sum_add_tsum_nat_add (b - a)]
  congr 1
  · rw [← squareBudget_zero_eq_sum]
    change squareBudget (fun i => activeCount (positiveExtension x b) (a + i)) 0 (b - a) = _
    rw [squareBudget_shift, Nat.add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    rw [activeCount_positiveExtension_prefix x b (by have := (Finset.mem_Ioc.mp hi).2; omega)]
  · apply tsum_congr
    intro i
    rw [show i + (b - a) + 1 = b - a + (i + 1) by omega,
      positiveExtensionPopulation_tail x hab (i + 1)]
    push_cast
    rfl

end Freezing1.SignedUrn
