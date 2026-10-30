module

public import Freezing1.ForwardUniformHeight
public import Freezing1.ForwardHeightOrder

/-!
# Lower tails for uniform vertices

The finite birth mixture separates the at most `l+1` early vertices from
later births. Stochastic increase of the active-height law controls every
later birth by the active-height law at time `l`.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- A finite lower-tail estimate for uniform sampling among all vertices.
The first term is the cost of the root and the early attachment times. -/
theorem uniformHeightLaw_lower_tail_le (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) < extinctionTime x) {l : ℕ} (_hl : l ≤ n) (r : ℝ) :
    (uniformHeightLaw x n).real {k : ℕ | (k : ℝ) ≤ r} ≤
      ((l : ℝ) + 1) / (plusCount x n + 1 : ℕ) +
        (uniformActiveHeightLaw x l).real {k : ℕ | (k : ℝ) ≤ r} := by
  let f : ℕ → ℝ := {k : ℕ | (k : ℝ) ≤ r}.indicator (fun _ => 1)
  let P : ℝ := (uniformActiveHeightLaw x l).real {k : ℕ | (k : ℝ) ≤ r}
  have hP : 0 ≤ P := measureReal_nonneg
  have hf1 : ∀ k, f k ≤ 1 := by
    intro k
    simp only [f, Set.indicator_apply]
    split_ifs <;> norm_num
  have hfanti : Antitone f := by
    intro a b hab
    change (if (b : ℝ) ≤ r then 1 else 0) ≤ (if (a : ℝ) ≤ r then 1 else 0)
    have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
    split_ifs <;> norm_num
    linarith
  have hfl : (∫ k, f k ∂uniformActiveHeightLaw x l) = P :=
    integral_indicator_one (by measurability)
  have hfAll : (∫ k, f k ∂uniformHeightLaw x n) =
      (uniformHeightLaw x n).real {k : ℕ | (k : ℝ) ≤ r} :=
    integral_indicator_one (by measurability)
  have hterm : ∀ i ∈ Finset.range n,
      (if x (i + 1) then (∫ k, f (k + 1) ∂uniformActiveHeightLaw x i) else 0) ≤
        (if i < l then 1 else 0) + (if x (i + 1) then P else 0) := by
    intro i hi
    have hin := (Finset.mem_range.mp hi).le
    have hiτ : (i : ℕ∞) < extinctionTime x :=
      lt_of_le_of_lt (by exact_mod_cast hin) hτ
    by_cases hil : i < l
    · have hb : (∫ k, f (k + 1) ∂uniformActiveHeightLaw x i) ≤ 1 := by
        calc
          _ ≤ ∫ _k, (1 : ℝ) ∂uniformActiveHeightLaw x i :=
            integral_mono (uniformActiveHeightLaw_integrable x i _) (integrable_const 1)
              (fun k => hf1 (k + 1))
          _ = 1 := by simp
      cases x (i + 1) <;> simp only [Bool.false_eq_true, ↓reduceIte, hil] <;> linarith
    · have hli : l ≤ i := Nat.le_of_not_gt hil
      have hb := uniformActiveHeightLaw_shift_integral_le_earlier x hfanti hli hiτ
      rw [hfl] at hb
      cases x (i + 1) <;> simp only [Bool.false_eq_true, ↓reduceIte, hil, zero_add]
      · exact le_rfl
      · exact hb
  have hearly : (∑ i ∈ Finset.range n, if i < l then (1 : ℝ) else 0) ≤ l := by
    calc
      _ = (((Finset.range n).filter (fun i => i < l)).card : ℝ) := by simp
      _ ≤ l := by
        have hs : (Finset.range n).filter (fun i => i < l) ⊆ Finset.range l := by
          intro i hi
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
        exact_mod_cast (show ((Finset.range n).filter (fun i => i < l)).card ≤ l by
          simpa using Finset.card_le_card hs)
  have hcount : (∑ i ∈ Finset.range n, if x (i + 1) then P else 0) = plusCount x n * P := by
    rw [plusCount, Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    cases x (i + 1) <;> simp
  have hsum : (∑ i ∈ Finset.range n, if x (i + 1) then
      (∫ k, f (k + 1) ∂uniformActiveHeightLaw x i) else 0) ≤ l + plusCount x n * P := by
    have hh := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, hcount] at hh
    exact hh.trans (add_le_add hearly le_rfl)
  rw [← hfAll, uniformHeightLaw_integral_mixture x n hτ]
  change _ ≤ ((l : ℝ) + 1) / (plusCount x n + 1 : ℕ) + P
  have hN : (0 : ℝ) < (plusCount x n + 1 : ℕ) := by positivity
  apply (div_le_iff₀ hN).mpr
  have heq : (((l : ℝ) + 1) / (plusCount x n + 1 : ℕ) + P) *
      (plusCount x n + 1 : ℕ) = l + 1 + (plusCount x n + 1) * P := by
    push_cast
    field_simp
  rw [heq]
  linarith [hf1 0]

end Freezing1.Forward
