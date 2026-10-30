module

public import Freezing1.SIRReverseCouplingWindowGap
public import Freezing1.SIRReverseCouplingFormulation

/-! The actual positive-probability window gap, expressed with the exact
source gate and the genuine bounded first-extinction index. The refuted
statement is hazard inheritance across the shifted window, not existence
of the weaker unconditional iid coupling. -/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory Filter Set
open scoped NNReal Classical

theorem reverseWindowHazardGap_extinctionIndex (rate : ℝ≥0) (H : ℕ → Counts)
    (hH : H ∈ reverseWindowHazardGap rate) : boundedExtinctionIndex 6 H = 9 := by
  unfold boundedExtinctionIndex
  apply (Nat.find_eq_iff _).mpr
  refine ⟨Or.inr hH.1, ?_⟩
  intro j hj hc
  rcases hc with he | hz
  · omega
  · exact (hH.2.1 j hj).ne' hz

theorem reverseWindowHazardGap_sourceGate (rate : ℝ≥0) (H : ℕ → Counts)
    (hH : H ∈ reverseWindowHazardGap rate) :
    H ∈ sourceLatePressureEvent rate 6 (infectionProbability rate 2) := by
  intro k hlo hhi
  apply hH.2.2.1 k
  · norm_num at hlo
    exact_mod_cast hlo
  · norm_num at hhi
    exact hhi

theorem reverseWindowHazardGap_sourceBad (rate : ℝ≥0) (H : ℕ → Counts)
    (hH : H ∈ reverseWindowHazardGap rate) :
    H ∈ sourceReverseBadEvent rate 6 (infectionProbability rate 2) 3 ∧
      (infectionProbability rate 2 : ℝ) <
        infectionProbability rate (H (boundedExtinctionIndex 6 H - 3)).susceptible := by
  have hτ := reverseWindowHazardGap_extinctionIndex rate H hH
  refine ⟨⟨reverseWindowHazardGap_sourceGate rate H hH, by norm_num, ?_, ?_⟩, ?_⟩
  · simp [sourceReverseWindow, hτ]
  · change (H (boundedExtinctionIndex 6 H - 3)).infectious <
      (H (boundedExtinctionIndex 6 H - 3 + 1)).infectious
    rw [hτ]
    norm_num
    have hinfect := hH.2.2.2.1
    omega
  · simpa only [hτ, show (9 - 3 : ℕ) = 6 by norm_num] using hH.2.2.2.2

/-- The forward late event does not imply an a.e. bound on every
pre-step hazard in the printed reverse window. This stronger shortcut
is false under the actual full SIR count-history law. -/
theorem late_gate_reverse_hazard_inheritance_false (rate : ℝ≥0) (hr : 0 < rate) :
    ¬ (∀ᵐ H ∂countsFullLaw rate 6,
      H ∈ sourceLatePressureEvent rate 6 (infectionProbability rate 2) →
        ∀ j : ℕ, 1 ≤ j → j ≤ sourceReverseWindow 6 H →
          (infectionProbability rate (H (boundedExtinctionIndex 6 H - j)).susceptible : ℝ) ≤
            infectionProbability rate 2) := by
  intro hbound
  have hnot : ∀ᵐ H ∂countsFullLaw rate 6, H ∉ reverseWindowHazardGap rate := by
    filter_upwards [hbound] with H hH
    intro hgap
    obtain ⟨hbad, hstrict⟩ := reverseWindowHazardGap_sourceBad rate H hgap
    exact (not_lt_of_ge (hH hbad.1 3 hbad.2.1 hbad.2.2.1)) hstrict
  have hzero : (countsFullLaw rate 6) (reverseWindowHazardGap rate) = 0 := by
    have hs : {H : ℕ → Counts | ¬H ∉ reverseWindowHazardGap rate} =
        reverseWindowHazardGap rate := by
      ext H
      simp only [Set.mem_ofPred_eq, not_not]
    rw [← hs]
    exact ae_iff.mp hnot
  exact (countsFullLaw_reverseWindowHazardGap_pos rate hr).ne' hzero

end Freezing1.SIR
