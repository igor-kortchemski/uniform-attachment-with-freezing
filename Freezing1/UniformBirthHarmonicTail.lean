module

public import Freezing1.UniformBirthConditionalMean
public import Freezing1.UniformBirthRandomMean
public import Freezing1.LinearRegimeIntervals
public import Freezing1.LinearRegimeAssumptions

/-!
# The corrected strict harmonic tail in the random-mean argument

The source includes its birth endpoint twice. The actual complement is
strictly after birth; that correction also makes the logarithmic sum bound
valid when birth equals the final horizon.
-/

@[expose] public section

namespace Freezing1.UniformBirth

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology BigOperators

set_option backward.isDefEq.respectTransparency false

theorem strict_height_tail_le_log (x : SignSequence) {n b : ℕ} (hb : 1 ≤ b) (hbn : b ≤ n)
    {c gamma : ℝ} (hc : 0 < c) (hg : 0 < gamma)
    (hlower : ∀ i : ℕ, b < i → i ≤ n →
      (c / 2) * i ≤ (activeCount x i : ℝ) ∨ gamma * n ≤ (activeCount x i : ℝ)) :
    heightScaleOn x (Finset.Ioc b n) ≤ (2 / c) * Real.log ((n : ℝ) / b) + 1 / gamma := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hgn : 0 < gamma * n := mul_pos hg hn
  have hi (i : ℕ) (hbi : b ≤ i) (hin : i < n) :
      (if x (i + 1) then 1 / (activeCount x (i + 1) : ℝ) else 0) ≤
        (2 / c) * (1 / ((i : ℝ) + 1)) + 1 / (gamma * n) := by
    have hip : 0 < (i : ℝ) + 1 := by positivity
    have hci : 0 < (c / 2) * ((i : ℝ) + 1) := mul_pos (by positivity) hip
    split
    · rcases hlower (i + 1) (by omega) (by omega) with hl | hl
      · have ht := one_div_le_one_div_of_le hci (by simpa only [Nat.cast_add, Nat.cast_one] using hl)
        have he : 1 / ((c / 2) * ((i : ℝ) + 1)) = (2 / c) * (1 / ((i : ℝ) + 1)) := by
          field_simp
        exact (ht.trans_eq he).trans (le_add_of_nonneg_right (by positivity))
      · exact (one_div_le_one_div_of_le hgn hl).trans (le_add_of_nonneg_left (by positivity))
    · positivity
  calc
    _ ≤ ∑ i ∈ Finset.Ico b n, ((2 / c) * (1 / ((i : ℝ) + 1)) + 1 / (gamma * n)) := by
      rw [heightScaleOn_Ioc_eq]
      exact Finset.sum_le_sum (fun i hi' => hi i (Finset.mem_Ico.mp hi').1 (Finset.mem_Ico.mp hi').2)
    _ = (2 / c) * harmonicInterval b n + (n - b : ℕ) * (1 / (gamma * n)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [harmonicInterval, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ (2 / c) * Real.log ((n : ℝ) / b) + 1 / gamma := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (by linarith [(harmonicInterval_log_error hb hbn).1]) (by positivity)
      · calc
          _ ≤ (n : ℝ) * (1 / (gamma * n)) := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.sub_le n b)) (by positivity)
          _ = 1 / gamma := by field_simp

theorem strict_mean_tail_normalized_le_log (x : SignSequence) {n b : ℕ}
    (h : PositiveThrough x n) (hn : 5 ≤ n) (hb : 1 ≤ b) (hbn : b ≤ n)
    {c gamma : ℝ} (hc : 0 < c) (hg : 0 < gamma)
    (hlower : ∀ i : ℕ, b < i → i ≤ n →
      (c / 2) * i ≤ (activeCount x i : ℝ) ∨ gamma * n ≤ (activeCount x i : ℝ)) :
    0 ≤ 1 - truncatedMean x n h b / heightScale x n ∧
      1 - truncatedMean x n h b / heightScale x n ≤
        (1 / Real.log ((n : ℝ) / 4)) * (2 / c) * Real.log ((n : ℝ) / b) +
          1 / (gamma * heightScale x n) := by
  have hs := heightScale_pos (by omega) h
  have hn4 : (4 : ℝ) < n := by exact_mod_cast (show 4 < n by omega)
  have hlog : 0 < Real.log ((n : ℝ) / 4) := Real.log_pos (by linarith)
  have hlogscale := log_quarter_le_heightScale (by omega) h
  have hlogbn : 0 ≤ Real.log ((n : ℝ) / b) := Real.log_nonneg
    ((le_div_iff₀ (by exact_mod_cast (show 0 < b by omega))).mpr
      (by simpa only [one_mul] using (show (b : ℝ) ≤ n by exact_mod_cast hbn)))
  have he : 1 - truncatedMean x n h b / heightScale x n =
      heightScaleOn x (Finset.Ioc b n) / heightScale x n := by
    rw [← heightScale_sub_truncatedMean x n h hbn, sub_div, div_self hs.ne']
  constructor
  · rw [he]
    apply div_nonneg _ hs.le
    unfold heightScaleOn
    apply Finset.sum_nonneg
    intro i hi
    split
    · exact one_div_nonneg.mpr (by exact_mod_cast (h i (Finset.mem_Ioc.mp hi).2).le)
    · exact le_rfl
  · rw [he]
    calc
      _ ≤ ((2 / c) * Real.log ((n : ℝ) / b) + 1 / gamma) / heightScale x n :=
        div_le_div_of_nonneg_right (strict_height_tail_le_log x hb hbn hc hg hlower) hs.le
      _ = (2 / c) * Real.log ((n : ℝ) / b) / heightScale x n + 1 / (gamma * heightScale x n) := by ring
      _ ≤ _ := by
        have ht := div_le_div_of_nonneg_left (by positivity : 0 ≤ (2 / c) * Real.log ((n : ℝ) / b)) hlog hlogscale
        apply add_le_add _ (le_refl _)
        convert ht using 1; ring

/-- The source hypotheses supply the finite harmonic bound uniformly for
all birth indices beyond A_n. No harmonic estimate is assumed. -/
theorem eventual_mean_tail_normalized_le_log (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) {A : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hnear : NearOriginLinear rows A c) (hbulk : BulkLowerBound rows) :
    ∃ gamma > 0, ∀ᶠ n : ℕ in atTop, ∀ b : ℕ, 1 ≤ b → b ≤ n → A n ≤ (b : ℝ) →
      0 ≤ 1 - truncatedMean (rows n) n (hrows n) b / heightScale (rows n) n ∧
        1 - truncatedMean (rows n) n (hrows n) b / heightScale (rows n) n ≤
          (1 / Real.log ((n : ℝ) / 4)) * (2 / c) * Real.log ((n : ℝ) / b) +
            1 / (gamma * heightScale (rows n) n) := by
  obtain ⟨e, he, he1, hgood⟩ := hnear (c / 2) (by positivity)
  obtain ⟨gamma, hg, hbulkGood⟩ := hbulk e he he1
  refine ⟨gamma, hg, ?_⟩
  filter_upwards [eventually_ge_atTop (5 : ℕ), hgood, hbulkGood] with n hn hng hnb
  intro b hb hbn hAb
  apply strict_mean_tail_normalized_le_log (rows n) (hrows n) hn hb hbn hc hg
  intro i hbi hin
  by_cases hie : (i : ℝ) ≤ e * n
  · left
    have hi0 : 0 < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
    have hAi : A n ≤ (i : ℝ) := hAb.trans (by exact_mod_cast (show b ≤ i by omega))
    have hratio := (abs_le.mp (hng i hAi hie)).1
    have ht : c / 2 ≤ (activeCount (rows n) i : ℝ) / i := by linarith
    exact (le_div_iff₀ hi0).mp ht
  · right
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    exact (le_div_iff₀ hn0).mp (hnb i (le_of_not_ge hie) hin)

end Freezing1.UniformBirth
