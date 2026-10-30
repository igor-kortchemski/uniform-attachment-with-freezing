module

public import Freezing1.SIRRaceWithUnused
public import Freezing1.SIRClockNextCoordinates

/-!
# The actual one-event residual law for labelled SIR clocks

The next-slot injection instantiates the proved live/unused clock race.
Consequently infection and recovery delete old clocks and activate unused
coordinates with the exact next independent residual law. This is a
one-event law, not yet an identification of the entire static-array history.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def populationNextClockView {n : ℕ} {z : PopulationState n} (hz : z.Valid)
    {winner : ClockSlot n} (hw : winner ∈ z.liveSlots)
    (x : (LiveCoordinate z → ℝ) × (UnusedCoordinate z → ℝ)) :
    ℝ × (RelevantCoordinate (populationStep z winner) → ℝ) :=
  designatedRaceWithUnused (⟨winner, hw⟩ : LiveCoordinate z) (nextClockCoordinate hz hw) x

theorem population_winner_next_clock_law {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {r : ℝ} (hr : 0 < r) {winner : ClockSlot n}
    (hw : winner ∈ z.liveSlots) :
    (((Measure.pi (fun c : LiveCoordinate z => expMeasure (clockSlotRate (n := n) r c.val))).prod
      (Measure.pi (fun c : UnusedCoordinate z => expMeasure (clockSlotRate (n := n) r c.val)))).restrict
        (clockWins (⟨winner, hw⟩ : LiveCoordinate z) ×ˢ univ)).map
          (populationNextClockView hz hw) =
      ENNReal.ofReal (clockSlotRate r winner /
        ((z.active.card : ℝ) * (1 + r * z.susceptible.card))) •
        ((expMeasure ((z.active.card : ℝ) * (1 + r * z.susceptible.card))).prod
          (Measure.pi (fun c : RelevantCoordinate (populationStep z winner) =>
            expMeasure (clockSlotRate (n := n) r c.val)))) := by
  unfold populationNextClockView
  have hh := exponential_designated_race_with_unused_projection
    (fun c : LiveCoordinate z => clockSlotRate (n := n) r c.val)
    (fun c => clockSlotRate_pos hr c.val)
    (fun c : UnusedCoordinate z => clockSlotRate (n := n) r c.val)
    (fun c => clockSlotRate_pos hr c.val)
    (⟨winner, hw⟩ : LiveCoordinate z) (nextClockCoordinate hz hw)
    (nextClockCoordinate_injective hz hw)
  simpa only [sum_liveCoordinate_rates, nextClockCoordinate_rate] using hh

end Freezing1.SIR
