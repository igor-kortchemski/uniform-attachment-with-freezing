module

public import Freezing1.SIRLateHarmonic
public import Freezing1.CountableMarkovPotential

/-!
# Expected forward reciprocal sums in a low-infection phase

The hypothesis concerns the starting susceptible population only. Its
monotonicity supplies the probability bound at every later state of the
actual chain. The accumulated-potential argument then controls all horizons.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Classical

noncomputable def reciprocalCost (eps : ℝ) (c : Counts) : ℝ :=
  (1 - 2 * eps) / c.infectious

theorem reciprocalCost_nonneg {eps : ℝ} (heps : eps ≤ 1 / 2) (c : Counts) :
    0 ≤ reciprocalCost eps c := div_nonneg (by linarith) (Nat.cast_nonneg _)

noncomputable def reciprocalHistoryCost (eps : ℝ) (H : ℕ → Counts) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, reciprocalCost eps (H i)

noncomputable def reciprocalBudgetUpdate (eps : ℝ) (a : ℝ × Counts) (d : Counts) : ℝ × Counts :=
  (a.1 + reciprocalCost eps a.2, d)

noncomputable def reciprocalBudgetPotential (a : ℝ × Counts) (c : Counts) : ℝ≥0∞ :=
  ENNReal.ofReal a.1 + ENNReal.ofReal (harmonicPopulation c)

theorem accumulate_reciprocalBudget {H : ℕ → Counts} {c : Counts}
    (h0 : H 0 = c) (eps : ℝ) (k : ℕ) :
    CountableMarkovChain.accumulate ((0 : ℝ), c) (reciprocalBudgetUpdate eps) H k =
      (reciprocalHistoryCost eps H k, H k) := by
  induction k with
  | zero => simp [CountableMarkovChain.accumulate_zero, reciprocalHistoryCost, h0]
  | succ k ih =>
    rw [CountableMarkovChain.accumulate_succ, ih]
    simp [reciprocalBudgetUpdate, reciprocalHistoryCost, Finset.sum_range_succ]

theorem countsKernel_accumulated_harmonic_budget (rate : ℝ≥0) (c : Counts)
    {eps a : ℝ} (heps : eps ≤ 1 / 2) (ha : 0 ≤ a)
    (hp : (infectionProbability rate c.susceptible : ℝ) ≤ eps) :
    (∫⁻ d, reciprocalBudgetPotential (reciprocalBudgetUpdate eps (a, c) d) d
      ∂countsKernel rate c) ≤ reciprocalBudgetPotential (a, c) c := by
  simp only [reciprocalBudgetPotential, reciprocalBudgetUpdate]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    ENNReal.ofReal_add ha (reciprocalCost_nonneg heps c)]
  have hh : ENNReal.ofReal a +
      ((∫⁻ d, ENNReal.ofReal (harmonicPopulation d) ∂countsKernel rate c) +
        ENNReal.ofReal ((1 - 2 * eps) / c.infectious)) ≤
      ENNReal.ofReal a + ENNReal.ofReal (harmonicPopulation c) :=
    add_le_add le_rfl (countsKernel_lintegral_harmonic_budget rate c heps hp)
  simpa only [reciprocalCost, add_assoc, add_comm, add_left_comm] using hh

theorem countsPath_susceptible_le_initial (rate : ℝ≥0) (c : Counts) :
    ∀ᵐ H ∂CountableMarkovChain.fullLaw (countsKernel rate) c,
      ∀ k, (H k).susceptible ≤ c.susceptible := by
  filter_upwards [CountableMarkovChain.fullLaw_initial (countsKernel rate) c,
    CountableMarkovChain.fullLaw_steps (countsKernel rate) c Counts.LegalNext
      (countsKernel_legal rate)] with H h0 hl
  intro k
  induction k with
  | zero => rw [h0]
  | succ k ih => exact (hl k).susceptible_le.trans ih

theorem countsPath_lintegral_reciprocalHistoryCost_le (rate : ℝ≥0) (c : Counts)
    {eps : ℝ} (heps : eps ≤ 1 / 2)
    (hp : (infectionProbability rate c.susceptible : ℝ) ≤ eps) (k : ℕ) :
    (∫⁻ H, ENNReal.ofReal (reciprocalHistoryCost eps H k)
      ∂CountableMarkovChain.fullLaw (countsKernel rate) c) ≤
        ENNReal.ofReal (harmonicPopulation c) := by
  have hbudget := CountableMarkovChain.lintegral_accumulate_of_superharmonic
    (countsKernel rate) c ((0 : ℝ), c) (reciprocalBudgetUpdate eps)
    reciprocalBudgetPotential (fun j => ?_) k
  · calc
      _ ≤ ∫⁻ H, reciprocalBudgetPotential
          (CountableMarkovChain.accumulate ((0 : ℝ), c) (reciprocalBudgetUpdate eps) H k) (H k)
          ∂CountableMarkovChain.fullLaw (countsKernel rate) c := by
        apply lintegral_mono_ae
        filter_upwards [CountableMarkovChain.fullLaw_initial (countsKernel rate) c] with H h0
        rw [accumulate_reciprocalBudget h0]
        exact le_add_right le_rfl
      _ ≤ _ := by simpa [reciprocalBudgetPotential] using hbudget
  · filter_upwards [CountableMarkovChain.fullLaw_initial (countsKernel rate) c,
      countsPath_susceptible_le_initial rate c] with H h0 hu
    rw [accumulate_reciprocalBudget h0]
    apply countsKernel_accumulated_harmonic_budget rate (H j) heps
    · exact Finset.sum_nonneg fun i _ => reciprocalCost_nonneg heps _
    · have hm : (infectionProbability rate (H j).susceptible : ℝ) ≤
          (infectionProbability rate c.susceptible : ℝ) := by
        exact_mod_cast infectionProbability_mono_susceptible rate (hu j)
      exact hm.trans hp

noncomputable def reciprocalHistorySum (H : ℕ → Counts) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, 1 / ((H i).infectious : ℝ)

theorem measurable_reciprocalHistorySum (k : ℕ) :
    Measurable (fun H : ℕ → Counts => reciprocalHistorySum H k) := by
  unfold reciprocalHistorySum
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_of_countable (fun c : Counts => 1 / (c.infectious : ℝ))).comp
      (measurable_pi_apply i)

theorem reciprocalHistoryCost_eq_mul (eps : ℝ) (H : ℕ → Counts) (k : ℕ) :
    reciprocalHistoryCost eps H k = (1 - 2 * eps) * reciprocalHistorySum H k := by
  unfold reciprocalHistoryCost reciprocalCost reciprocalHistorySum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem countsPath_lintegral_reciprocalHistorySum_le (rate : ℝ≥0) (c : Counts)
    {eps : ℝ} (heps : eps < 1 / 2)
    (hp : (infectionProbability rate c.susceptible : ℝ) ≤ eps) (k : ℕ) :
    (∫⁻ H, ENNReal.ofReal (reciprocalHistorySum H k)
      ∂CountableMarkovChain.fullLaw (countsKernel rate) c) ≤
        ENNReal.ofReal (harmonicPopulation c / (1 - 2 * eps)) := by
  have hcoef : 0 < 1 - 2 * eps := by linarith
  rw [ENNReal.ofReal_div_of_pos hcoef]
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr hcoef)) (Or.inl ENNReal.ofReal_ne_top)).mpr
  have hh := countsPath_lintegral_reciprocalHistoryCost_le rate c heps.le hp k
  simp_rw [reciprocalHistoryCost_eq_mul, ENNReal.ofReal_mul hcoef.le] at hh
  rw [lintegral_const_mul _ (measurable_reciprocalHistorySum k).ennreal_ofReal] at hh
  simpa only [mul_comm] using hh

end Freezing1.SIR
