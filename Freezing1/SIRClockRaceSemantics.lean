module

public import Freezing1.SIRClockRaceStep
public import Freezing1.SIRPreassignedChronology

/-!
# The race-coordinate map equals the static array's next residual view

The probabilistic one-event factorization acts on the very same clocks as
the deterministic preassigned-array epidemic. This diagram identifies the
next-coordinate map without replacing the static process by a resampling
definition.
-/

@[expose] public section

namespace Freezing1.SIR

open scoped Classical

set_option backward.isDefEq.respectTransparency false

def frameLiveClockValues {n : ℕ} (F : ClockFrame n) (omega : ClockArray n) :
    LiveCoordinate F.population → ℝ := fun c => remainingClock F omega c.val

def frameUnusedClockValues {n : ℕ} (F : ClockFrame n) (omega : ClockArray n) :
    UnusedCoordinate F.population → ℝ := fun c => omega c.val

theorem frameLiveClockValues_eq_relevant {n : ℕ} (F : ClockFrame n) (omega : ClockArray n) :
    frameLiveClockValues F omega =
      fun c : LiveCoordinate F.population => relevantClockView F omega c.val := by
  funext c
  exact (relevantClockView_of_live F omega c.property).symm

theorem frameUnusedClockValues_eq_relevant {n : ℕ} {F : ClockFrame n}
    (hf : F.population.Valid) (omega : ClockArray n) :
    frameUnusedClockValues F omega =
      fun c : UnusedCoordinate F.population => relevantClockView F omega c.val := by
  funext c
  exact (relevantClockView_of_unused hf omega c.property).symm

theorem populationNextClockView_static {n : ℕ} {F : ClockFrame n}
    (hf : F.population.Valid) (omega : ClockArray n) {winner : ClockSlot n}
    (hw : winner ∈ F.population.liveSlots) :
    ((populationNextClockView hf hw
      (frameLiveClockValues F omega, frameUnusedClockValues F omega)).1 =
        remainingClock F omega winner) ∧
    (∀ c : RelevantCoordinate (populationStep F.population winner),
      (populationNextClockView hf hw
        (frameLiveClockValues F omega, frameUnusedClockValues F omega)).2 c =
      relevantClockView (advanceClockFrame F omega winner) omega c.val) := by
  constructor
  · rfl
  · intro c
    have hR : c.val ∈ (advanceClockFrame F omega winner).population.relevantSlots := by
      simpa only [advanceClockFrame_population] using c.property
    rw [relevantClockView_advance hf omega hw hR]
    unfold populationNextClockView designatedRaceWithUnused untouchedClockProject nextClockCoordinate
    dsimp only
    split_ifs with hL
    · change remainingClock F omega c.val - remainingClock F omega winner =
        agedClockView F.population (remainingClock F omega winner) (relevantClockView F omega) c.val
      rw [agedClockView, ite_eq_left hL, relevantClockView_of_live F omega hL]
    · change omega c.val =
        agedClockView F.population (remainingClock F omega winner) (relevantClockView F omega) c.val
      rw [agedClockView, ite_eq_right hL]
      have hold := (Finset.mem_erase.mp (hf.step_relevant_subset hw c.property)).2
      have hU := (Finset.mem_union.mp hold).resolve_left hL
      exact (relevantClockView_of_unused hf omega hU).symm

end Freezing1.SIR
