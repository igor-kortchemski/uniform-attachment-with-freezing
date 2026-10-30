module

public import Freezing1.SIRTerminalSamplingRestriction

/-! Averaging terminal capture and a genuine surviving-prefix estimate. -/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory RandomEnvironment
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

theorem finiteRate_terminal_average_tendsto_zero (rate : ℕ → ℝ≥0) {lam : ℝ}
    (hlam : 1 < lam)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds lam))
    (F : (n : ℕ) → (Fin (2 * n + 1) → Bool) → ℝ≥0∞)
    (G : ℝ → (n : ℕ) → (Fin (2 * n + 1) → Bool) → ℝ≥0∞)
    (hF : ∀ n w, F n w ≤ 1)
    (hprefix : ∀ t, 0 < t → t < fluidExtinctionTime lam →
      Tendsto (fun n => ∫⁻ w, G t n w ∂signWordLaw (rate n) n (2 * n + 1)) atTop (nhds 0))
    (hcompare : ∀ n t, 0 < t → t < fluidExtinctionTime lam → ∀ w, SignWordFeasible n w →
      ∀ eta : ℝ, 0 < eta →
        ((wordCountsAt n w ⌊t * (n : ℝ)⌋₊).susceptible : ℝ) -
            (wordCountsAt n w (2 * n + 1)).susceptible ≤
          eta * ((n + 1 - (wordCountsAt n w (2 * n + 1)).susceptible : ℕ) : ℝ) →
        F n w ≤ G t n w + ENNReal.ofReal (2 * eta)) :
    Tendsto (fun n => ∫⁻ w, F n w ∂signWordLaw (rate n) n (2 * n + 1)) atTop (nhds 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro e he
  obtain ⟨eta, heta, hsmall⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := (3 : ℝ≥0∞)) (b := e) (by norm_num) he.ne'
  have hetaR : (0 : ℝ) < eta := by exact_mod_cast heta
  obtain ⟨t, ht, httop, htt, hgap⟩ := exists_finite_rate_capture_time hlam hetaR
    (lower := 0) (fluidExtinctionTime_spec hlam).1
  let B : (n : ℕ) → Set (Fin (2 * n + 1) → Bool) := fun n =>
    {w | ¬SignWordFeasible n w} ∪
    {w | (eta : ℝ) * ((n + 1 - (wordCountsAt n w (2 * n + 1)).susceptible : ℕ) : ℝ) ≤
      (wordCountsAt n w ⌊t * (n : ℝ)⌋₊).susceptible -
        ((wordCountsAt n w (2 * n + 1)).susceptible : ℝ)}
  have hbad : Tendsto (fun n => signWordLaw (rate n) n (2 * n + 1) (B n)) atTop (nhds 0) := by
    have hzero (n : ℕ) : signWordLaw (rate n) n (2 * n + 1) {w | ¬SignWordFeasible n w} = 0 :=
      ae_iff.mp (signWordLaw_feasible (rate n) n (2 * n + 1))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (signWordLaw_relative_late_births_tendsto rate hlam hrate hetaR httop htt hgap) (fun _ => bot_le)
    intro n
    exact (measure_union_le _ _).trans_eq (by rw [hzero n, zero_add])
  have hsum := (hprefix t ht htt).add hbad
  simp only [add_zero] at hsum
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hsum) (eta : ℝ≥0∞) (by exact_mod_cast heta)]
    with n hn
  have hbound := lintegral_le_add_small_bad (signWordLaw (rate n) n (2 * n + 1))
    (F n) (G t n) (hF n) (B n) (Set.to_countable _).measurableSet
    (ENNReal.ofReal (2 * (eta : ℝ))) (fun w hw => by
      have hf : SignWordFeasible n w := by by_contra h; exact hw (Or.inl h)
      have hrelative : ((wordCountsAt n w ⌊t * (n : ℝ)⌋₊).susceptible : ℝ) -
            (wordCountsAt n w (2 * n + 1)).susceptible ≤
          (eta : ℝ) * ((n + 1 - (wordCountsAt n w (2 * n + 1)).susceptible : ℕ) : ℝ) := by
        have hh : ¬(eta : ℝ) * ((n + 1 - (wordCountsAt n w (2 * n + 1)).susceptible : ℕ) : ℝ) ≤
            (wordCountsAt n w ⌊t * (n : ℝ)⌋₊).susceptible -
              ((wordCountsAt n w (2 * n + 1)).susceptible : ℝ) := fun h => hw (Or.inr h)
        exact (lt_of_not_ge hh).le
      exact hcompare n t ht htt w hf (eta : ℝ) hetaR hrelative)
  have hconst : ENNReal.ofReal (2 * (eta : ℝ)) = 2 * (eta : ℝ≥0∞) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_coe_nnreal]
    norm_num
  calc
    _ ≤ (∫⁻ w, G t n w ∂signWordLaw (rate n) n (2 * n + 1)) +
        ENNReal.ofReal (2 * (eta : ℝ)) + signWordLaw (rate n) n (2 * n + 1) (B n) := hbound
    _ = ((∫⁻ w, G t n w ∂signWordLaw (rate n) n (2 * n + 1)) +
        signWordLaw (rate n) n (2 * n + 1) (B n)) + 2 * (eta : ℝ≥0∞) := by rw [hconst]; ac_rfl
    _ ≤ (eta : ℝ≥0∞) + 2 * eta := add_le_add hn (le_refl _)
    _ = (eta : ℝ≥0∞) * 3 := by ring
    _ ≤ e := hsmall.le

end Freezing1.SIR
