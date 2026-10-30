module

public import Freezing1.SIRLateMaximumWord

/-!
# A genuine SIR word at the reverse-window boundary

The source late-hazard event does not itself bound every forward hazard
used by the displayed reversed half-window. This is a positive-probability
word counterexample to that window-inheritance implication. It does not
refute existence of a noncausal coupling with an unconditional iid marginal.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem signWordLaw_real_singleton_pos_of_susceptible_pos (rate : ℝ≥0) (hr : 0 < rate)
    (n : ℕ) {k : ℕ} (w : Fin k → Bool)
    (hu : ∀ j < k, 0 < (wordCountsAt n w j).susceptible) :
    0 < (signWordLaw rate n k).real {w} := by
  induction k with
  | zero =>
    have hw : w = fun i : Fin 0 => Fin.elim0 i := by funext i; exact Fin.elim0 i
    simp [hw, signWordLaw, measureReal_def]
  | succ k ih =>
    rw [signWordLaw_real_singleton_succ]
    apply mul_pos
    · apply ih (Fin.init w)
      intro j hj
      have hh := hu j (by omega)
      rwa [wordCountsAt_init n w hj.le] at hh
    · rw [bernoulli_sign_real_singleton]
      have hup : 0 < (countsRunWord n (Fin.init w)).susceptible := by
        have hh := hu k (by omega)
        rwa [wordCountsAt_init n w le_rfl, wordCountsAt_last] at hh
      cases hb : w (Fin.last k)
      · simp only [Bool.false_eq_true, ite_false]
        linarith [infectionProbability_lt_one rate (countsRunWord n (Fin.init w)).susceptible]
      · simp only [ite_true]
        rw [infectionProbability_coe]
        exact div_pos (mul_pos (show (0 : ℝ) < rate from hr) (by exact_mod_cast hup)) (by positivity)

def reverseWindowExampleWord : Fin 9 → Bool :=
  ![true, true, true, false, false, false, true, false, false]

theorem reverseWindowExampleWord_feasible : SignWordFeasible 6 reverseWindowExampleWord := by
  norm_num [reverseWindowExampleWord, SignWordFeasible, countsRunWord, initialCounts,
    countsStep, infectCounts, recoverCounts, Fin.init]

theorem reverseWindowExampleWord_counts (j : ℕ) (hj : j ≤ 9) :
    wordCountsAt 6 reverseWindowExampleWord j =
      (![⟨6, 1⟩, ⟨5, 2⟩, ⟨4, 3⟩, ⟨3, 4⟩, ⟨3, 3⟩,
        ⟨3, 2⟩, ⟨3, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨2, 0⟩] : Fin 10 → Counts)
          ⟨j, by omega⟩ := by
  revert hj
  induction j with
  | zero =>
    intro hj
    rw [wordCountsAt_zero]
    rfl
  | succ j ih =>
    intro hj
    have hj9 : j < 9 := by omega
    rw [wordCountsAt_succ 6 reverseWindowExampleWord hj9, ih (by omega)]
    interval_cases j <;>
      norm_num [ForwardAnnealed.wordSchedule, reverseWindowExampleWord,
        countsStep, infectCounts, recoverCounts]

theorem reverseWindowExampleWord_first_zero :
    (wordCountsAt 6 reverseWindowExampleWord 9).infectious = 0 ∧
      ∀ j < 9, 0 < (wordCountsAt 6 reverseWindowExampleWord j).infectious := by
  refine ⟨by rw [reverseWindowExampleWord_counts 9 le_rfl]; rfl, ?_⟩
  intro j hj
  rw [reverseWindowExampleWord_counts j hj.le]
  interval_cases j <;> norm_num

theorem reverseWindowExampleWord_susceptible_pos :
    ∀ j < 9, 0 < (wordCountsAt 6 reverseWindowExampleWord j).susceptible := by
  intro j hj
  rw [reverseWindowExampleWord_counts j hj.le]
  interval_cases j <;> norm_num

theorem reverseWindowExampleWord_positive_probability (rate : ℝ≥0) (hr : 0 < rate) :
    0 < (signWordLaw rate 6 9).real {reverseWindowExampleWord} :=
  signWordLaw_real_singleton_pos_of_susceptible_pos rate hr 6 reverseWindowExampleWord
    reverseWindowExampleWord_susceptible_pos

theorem reverseWindowExampleWord_held (j : ℕ) (hj : 9 ≤ j) :
    wordCountsAt 6 reverseWindowExampleWord j = ⟨2, 0⟩ := by
  by_cases he : j = 9
  · subst j
    exact reverseWindowExampleWord_counts 9 le_rfl
  · rw [wordCountsAt, dite_eq_right (by omega)]
    have hh := reverseWindowExampleWord_counts 9 le_rfl
    rw [wordCountsAt_last] at hh
    exact hh

/-- Every hazard in the source's late gate is at most p(rate,2), yet
the third reversed increment in its stated window uses p(rate,3). -/
theorem reverseWindowExampleWord_gate_and_earlier_hazard (rate : ℝ≥0) (hr : 0 < rate) :
    (∀ j : ℕ, 9 ≤ j → j ≤ 12 →
      (infectionProbability rate (wordCountsAt 6 reverseWindowExampleWord j).susceptible : ℝ) ≤
        infectionProbability rate 2) ∧
    3 ≤ min (6 / 2 : ℕ) (9 - 6) ∧
    ForwardAnnealed.wordSchedule reverseWindowExampleWord (9 - 3 + 1) = true ∧
    (infectionProbability rate 2 : ℝ) <
      infectionProbability rate (wordCountsAt 6 reverseWindowExampleWord (9 - 3)).susceptible := by
  refine ⟨?_, by norm_num, ?_, ?_⟩
  · intro j hj _
    rw [reverseWindowExampleWord_held j hj]
  · norm_num [ForwardAnnealed.wordSchedule, reverseWindowExampleWord]
  · rw [reverseWindowExampleWord_counts 6 (by omega)]
    change (infectionProbability rate 2 : ℝ) < infectionProbability rate 3
    rw [infectionProbability_coe, infectionProbability_coe]
    have hr0 : (0 : ℝ) < rate := hr
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    norm_num
    nlinarith

end Freezing1.SIR
