module

public import Freezing1.SIRClockPopulationUpdates

/-!
# The next relevant clocks are inherited coordinates

Every next slot comes either from a nonwinning old live slot or from an
untouched unused slot. The injection below preserves the physical clock
coordinate and therefore preserves its rate.
-/

@[expose] public section

namespace Freezing1.SIR

open scoped Classical

set_option backward.isDefEq.respectTransparency false

abbrev LiveCoordinate {n : ℕ} (z : PopulationState n) := {c // c ∈ z.liveSlots}
abbrev UnusedCoordinate {n : ℕ} (z : PopulationState n) := {c // c ∈ z.unusedSlots}
abbrev RelevantCoordinate {n : ℕ} (z : PopulationState n) := {c // c ∈ z.relevantSlots}

def inheritedClockSlot {n : ℕ} {z : PopulationState n} (winner : LiveCoordinate z) :
    ({c : LiveCoordinate z // c ≠ winner} ⊕ UnusedCoordinate z) → ClockSlot n :=
  Sum.elim (fun c => c.val.val) Subtype.val

noncomputable def nextClockCoordinate {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {winner : ClockSlot n} (hw : winner ∈ z.liveSlots)
    (c : RelevantCoordinate (populationStep z winner)) :
    {d : LiveCoordinate z // d ≠ ⟨winner, hw⟩} ⊕ UnusedCoordinate z :=
  let hold := hz.step_relevant_subset hw c.property
  if hL : c.val ∈ z.liveSlots then
    Sum.inl ⟨⟨c.val, hL⟩, fun he => (Finset.mem_erase.mp hold).1 (congrArg Subtype.val he)⟩
  else
    Sum.inr ⟨c.val, (Finset.mem_union.mp (Finset.mem_erase.mp hold).2).resolve_left hL⟩

theorem nextClockCoordinate_slot {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {winner : ClockSlot n} (hw : winner ∈ z.liveSlots)
    (c : RelevantCoordinate (populationStep z winner)) :
    inheritedClockSlot ⟨winner, hw⟩ (nextClockCoordinate hz hw c) = c.val := by
  unfold nextClockCoordinate
  split_ifs <;> rfl

theorem nextClockCoordinate_injective {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {winner : ClockSlot n} (hw : winner ∈ z.liveSlots) :
    Function.Injective (nextClockCoordinate hz hw) := by
  intro c d he
  apply Subtype.ext
  have hh := congrArg (inheritedClockSlot ⟨winner, hw⟩) he
  simpa only [nextClockCoordinate_slot] using hh

theorem inheritedClockSlot_rate {n : ℕ} {z : PopulationState n} (r : ℝ)
    (winner : LiveCoordinate z)
    (c : {d : LiveCoordinate z // d ≠ winner} ⊕ UnusedCoordinate z) :
    clockSlotRate r (inheritedClockSlot winner c) =
      Sum.elim (fun d : {d : LiveCoordinate z // d ≠ winner} =>
        clockSlotRate (n := n) r d.val.val)
        (fun d : UnusedCoordinate z => clockSlotRate (n := n) r d.val) c := by
  cases c <;> rfl

theorem nextClockCoordinate_rate {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) (r : ℝ) {winner : ClockSlot n} (hw : winner ∈ z.liveSlots)
    (c : RelevantCoordinate (populationStep z winner)) :
    Sum.elim (fun d : {d : LiveCoordinate z // d ≠ ⟨winner, hw⟩} =>
      clockSlotRate (n := n) r d.val.val)
      (fun d : UnusedCoordinate z => clockSlotRate (n := n) r d.val)
        (nextClockCoordinate hz hw c) = clockSlotRate (n := n) r c.val := by
  rw [← inheritedClockSlot_rate, nextClockCoordinate_slot]

theorem sum_liveCoordinate_rates {n : ℕ} (r : ℝ) (z : PopulationState n) :
    (∑ c : LiveCoordinate z, clockSlotRate (n := n) r c.val) =
      (z.active.card : ℝ) * (1 + r * z.susceptible.card) := by
  rw [Finset.sum_coe_sort, sum_clockSlotRate_live]

end Freezing1.SIR
