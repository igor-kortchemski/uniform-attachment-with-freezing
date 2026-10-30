module

public import Freezing1.SIRPreassignedResiduals

/-!
# Forward chronology of the actual static-array epidemic

Positive preassigned delays keep every live physical clock strictly in the
future. Event times are therefore nondecreasing, with strict increase at
each selected event. The proof uses the deterministic residual identities,
not a resampling or conditional-distribution assumption.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory
open scoped Classical

set_option backward.isDefEq.respectTransparency false

def FutureLiveClocks {n : ℕ} (F : ClockFrame n) (omega : ClockArray n) : Prop :=
  ∀ c ∈ F.population.liveSlots, 0 < remainingClock F omega c

theorem relevantClockView_of_live {n : ℕ} (F : ClockFrame n) (omega : ClockArray n)
    {c : ClockSlot n} (hc : c ∈ F.population.liveSlots) :
    relevantClockView F omega c = remainingClock F omega c := by
  have ha := (Finset.mem_product.mp hc).1
  simp [relevantClockView, ha]

theorem relevantClockView_of_unused {n : ℕ} {F : ClockFrame n}
    (hf : F.population.Valid) (omega : ClockArray n)
    {c : ClockSlot n} (hc : c ∈ F.population.unusedSlots) :
    relevantClockView F omega c = omega c := by
  have hS := (mem_unusedSlots F.population c).mp hc
  have hA : c.1 ∉ F.population.active :=
    fun h => Finset.disjoint_left.mp hf.disjoint hS h
  simp [relevantClockView, hA]

theorem clockFrameStep_future {n : ℕ} {F : ClockFrame n}
    (hf : F.population.Valid) {omega : ClockArray n} (hp : ∀ c, 0 < omega c)
    (hfuture : FutureLiveClocks F omega) : FutureLiveClocks (clockFrameStep F omega) omega := by
  cases hs : firstLiveClock F.population (remainingClock F omega) with
  | none => simpa only [clockFrameStep, hs] using hfuture
  | some winner =>
    have hw := (firstLiveClock_some_iff _ _ _).mp hs
    rw [clockFrameStep, hs]
    change FutureLiveClocks (advanceClockFrame F omega winner) omega
    intro c hc
    have hR : c ∈ (advanceClockFrame F omega winner).population.relevantSlots :=
      Finset.mem_union_left _ hc
    rw [← relevantClockView_of_live _ _ hc, relevantClockView_advance hf omega hw.1 hR]
    unfold agedClockView
    by_cases hL : c ∈ F.population.liveSlots
    · rw [ite_eq_left hL, relevantClockView_of_live _ _ hL]
      have hpop : (advanceClockFrame F omega winner).population =
          populationStep F.population winner := rfl
      have hnext : c ∈ (populationStep F.population winner).relevantSlots := hpop ▸ hR
      have hne := (Finset.mem_erase.mp (hf.step_relevant_subset hw.1 hnext)).1
      exact sub_pos.mpr (hw.2 c hL hne)
    · rw [ite_eq_right hL]
      have hpop : (advanceClockFrame F omega winner).population =
          populationStep F.population winner := rfl
      have hnext : c ∈ (populationStep F.population winner).relevantSlots := hpop ▸ hR
      have hold := (Finset.mem_erase.mp (hf.step_relevant_subset hw.1 hnext)).2
      have hU := (Finset.mem_union.mp hold).resolve_left hL
      rw [relevantClockView_of_unused hf omega hU]
      exact hp c

theorem preassignedRun_future (n : ℕ) {omega : ClockArray n}
    (hp : ∀ c, 0 < omega c) (k : ℕ) : FutureLiveClocks (preassignedRun n omega k) omega := by
  induction k with
  | zero =>
    intro c _
    simpa only [preassignedRun, initialClockFrame, remainingClock,
      ClockFrame.time, ClockFrame.birthTime, sub_self, sub_zero] using hp c
  | succ k ih =>
    exact clockFrameStep_future (preassignedRun_population_valid n omega k) hp ih

theorem clockFrameStep_time_le {n : ℕ} {F : ClockFrame n} {omega : ClockArray n}
    (hf : FutureLiveClocks F omega) : F.time ≤ (clockFrameStep F omega).time := by
  cases hs : firstLiveClock F.population (remainingClock F omega) with
  | none => simp [clockFrameStep, hs]
  | some c =>
    have hc := (firstLiveClock_some_iff _ _ _).mp hs
    rw [clockFrameStep, hs]
    change F.time ≤ F.time + remainingClock F omega c
    linarith [hf c hc.1]

theorem clockFrameStep_time_lt_of_some {n : ℕ} {F : ClockFrame n} {omega : ClockArray n}
    (hf : FutureLiveClocks F omega) {c : ClockSlot n}
    (hc : firstLiveClock F.population (remainingClock F omega) = some c) :
    F.time < (clockFrameStep F omega).time := by
  have hw := (firstLiveClock_some_iff _ _ _).mp hc
  rw [clockFrameStep, hc]
  change F.time < F.time + remainingClock F omega c
  linarith [hf c hw.1]

theorem preassignedRun_time_monotone (n : ℕ) {omega : ClockArray n}
    (hp : ∀ c, 0 < omega c) : Monotone (fun k => (preassignedRun n omega k).time) := by
  apply monotone_nat_of_le_succ
  intro k
  exact clockFrameStep_time_le (preassignedRun_future n hp k)

theorem preassignedClockLaw_time_monotone {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ∀ᵐ omega ∂preassignedClockLaw r n,
      Monotone (fun k => (preassignedRun n omega k).time) :=
  (preassignedClockLaw_positive hr n).mono fun _ hp => preassignedRun_time_monotone n hp

end Freezing1.SIR
