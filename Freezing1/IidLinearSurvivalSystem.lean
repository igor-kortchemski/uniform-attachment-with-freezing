module

public import Freezing1.ConditionalSurvivalCoupling
public import Freezing1.IidLinearAssumptions

/-! The actual iid walk supplies every hypothesis of the survival coupling. -/

@[expose] public section

namespace Freezing1.ForwardAnnealed

open Filter Set MeasureTheory ProbabilityTheory
open scoped Classical Topology ENNReal

set_option backward.isDefEq.respectTransparency false

def survivesThrough (n : ℕ) : Set SignSequence := {x | (n : ℕ∞) < extinctionTime x}

theorem survivesThrough_eq_compl (n : ℕ) : survivesThrough n = (extinctBy n)ᶜ := by
  ext x
  change (n : ℕ∞) < extinctionTime x ↔ ¬∃ k ≤ n, activeCount x k = 0
  rw [← extinctionTime_le_iff]
  exact lt_iff_not_ge

theorem measurableSet_survivesThrough (n : ℕ) : MeasurableSet (survivesThrough n) := by
  rw [survivesThrough_eq_compl]
  exact (measurableSet_extinctBy n).compl

theorem survivesThrough_antitone : Antitone survivesThrough := by
  intro n m hnm x hx
  exact (show (n : ℕ∞) ≤ m by exact_mod_cast hnm).trans_lt hx

theorem iInter_survivesThrough : (⋂ n, survivesThrough n) = {x | extinctionTime x = ⊤} := by
  ext x
  simp only [mem_iInter, survivesThrough, mem_ofPred_eq]
  constructor
  · intro h
    by_contra hfinite
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfinite
    have hh := h n
    rw [← hn] at hh
    exact (lt_irrefl _) hh
  · intro h n
    simp [h]

theorem iid_survival_positive (p : unitInterval) (hp : (1 : ℝ) / 2 < p) :
    iidSignLaw p (⋂ n, survivesThrough n) ≠ 0 := by
  rw [iInter_survivesThrough, iid_nonextinction_probability_supercritical p hp]
  have hp0 : (0 : ℝ) < p := by linarith only [hp]
  have hlt : (1 - (p : ℝ)) / p < 1 := (div_lt_one hp0).mpr (by linarith only [hp])
  exact (tsub_pos_iff_lt.mpr (ENNReal.ofReal_lt_one.mpr hlt)).ne'

noncomputable def iidSurvivalSystem (p : unitInterval) (hp : (1 : ℝ) / 2 < p) :
    ConditionalSurvival.System SignSequence where
  law := iidSignLaw p
  probability := inferInstance
  event := survivesThrough
  measurable := measurableSet_survivesThrough
  antitone := survivesThrough_antitone
  positive := iid_survival_positive p hp

end Freezing1.ForwardAnnealed
