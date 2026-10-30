module

public import Freezing1.SIRReverseCouplingWord

/-! Positive probability under the actual complete SIR count law of the
reverse-window hazard inheritance failure. This is not a counterexample
to an unconditional iid coupling, which is a weaker distributional claim. -/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem reverseWindowExampleWord_prefix_positive (rate : ℝ≥0) (hr : 0 < rate) :
    0 < (countsFullLaw rate 6)
      {H | Preorder.frestrictLe 9 H = countsPrefixWord 6 reverseWindowExampleWord} := by
  have hatom := reverseWindowExampleWord_positive_probability rate hr
  change 0 < ((signWordLaw rate 6 9) {reverseWindowExampleWord}).toReal at hatom
  have hpos := (ENNReal.toReal_pos_iff.mp hatom).1
  apply hpos.trans_le
  calc
    (signWordLaw rate 6 9) {reverseWindowExampleWord} ≤
        (signWordLaw rate 6 9)
          ((countsPrefixWord 6) ⁻¹' {countsPrefixWord 6 reverseWindowExampleWord}) := by
      apply measure_mono
      intro w hw
      obtain rfl := Set.mem_singleton_iff.mp hw
      rfl
    _ = ((signWordLaw rate 6 9).map (countsPrefixWord 6))
        {countsPrefixWord 6 reverseWindowExampleWord} :=
      (Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)).symm
    _ = ((countsFullLaw rate 6).map (Preorder.frestrictLe 9))
        {countsPrefixWord 6 reverseWindowExampleWord} := by
      rw [signWordLaw_map_countsPrefixWord]
    _ = _ := by
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
      rfl

def reverseWindowHazardGap (rate : ℝ≥0) : Set (ℕ → Counts) :=
  {H | (H 9).infectious = 0 ∧ (∀ j < 9, 0 < (H j).infectious) ∧
    (∀ j : ℕ, 9 ≤ j → j ≤ 12 →
      (infectionProbability rate (H j).susceptible : ℝ) ≤ infectionProbability rate 2) ∧
    (H 7).infectious = (H 6).infectious + 1 ∧
    (infectionProbability rate 2 : ℝ) < infectionProbability rate (H 6).susceptible}

/-- Here n=6, the genuine first extinction is τ=9, and j=3 belongs
to min(floor(n/2),τ-n). The late gate starts at 3n/2=9, but the
third reversed birth uses the larger forward hazard at τ-j=6. -/
theorem countsFullLaw_reverseWindowHazardGap_pos (rate : ℝ≥0) (hr : 0 < rate) :
    0 < (countsFullLaw rate 6) (reverseWindowHazardGap rate) := by
  apply (reverseWindowExampleWord_prefix_positive rate hr).trans_le
  apply measure_mono_ae
  filter_upwards [countsFullLaw_legal rate 6] with H hlegal
  intro hprefix
  have hstate (j : ℕ) (hj : j ≤ 9) : H j = wordCountsAt 6 reverseWindowExampleWord j := by
    have hh := congrFun hprefix ⟨j, Finset.mem_Iic.mpr hj⟩
    change H j = countsPrefixWord 6 reverseWindowExampleWord ⟨j, Finset.mem_Iic.mpr hj⟩ at hh
    simpa only [wordCountsAt, dite_eq_left hj] using hh
  have hzero : (H 9).infectious = 0 := by
    rw [hstate 9 le_rfl]
    exact reverseWindowExampleWord_first_zero.1
  have hheld (j : ℕ) (hj : 9 ≤ j) : H j = ⟨2, 0⟩ := by
    rw [legalHistory_absorbed_persists hlegal hzero j hj, hstate 9 le_rfl,
      reverseWindowExampleWord_counts 9 le_rfl]
    rfl
  refine ⟨hzero, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [hstate j hj.le]
    exact reverseWindowExampleWord_first_zero.2 j hj
  · intro j hj _
    rw [hheld j hj]
  · rw [hstate 7 (by omega), hstate 6 (by omega),
      reverseWindowExampleWord_counts 7 (by omega), reverseWindowExampleWord_counts 6 (by omega)]
    rfl
  · rw [hstate 6 (by omega)]
    exact (reverseWindowExampleWord_gate_and_earlier_hazard rate hr).2.2.2

end Freezing1.SIR
