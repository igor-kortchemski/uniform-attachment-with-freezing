module

public import Freezing1.SIRPoissonClockArray
public import Freezing1.SIRPreassignedChronology

/-!
# The actual next-point protocol of the entire contact processes

At each live directed pair the next contact is recomputed from the whole
arrival sequence after the source's current infection age. The same paths
are retained at all steps. On positive arrays this protocol agrees,
pointwise for its entire history, with the static first-contact epidemic.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory Set
open scoped Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def PoissonContact.nextArrival (a : PoissonContact.ArrivalPath) (t : ℝ) : ℝ :=
  a.1 (PoissonContact.count a t)

theorem PoissonContact.nextArrival_gt (a : PoissonContact.ArrivalPath) (t : ℝ) :
    t < nextArrival a t := Nat.find_spec (PoissonContact.exists_later a t)

theorem PoissonContact.nextArrival_eq_first {a : PoissonContact.ArrivalPath} {t : ℝ}
    (ht : t < PoissonContact.first a) : nextArrival a t = PoissonContact.first a := by
  rw [nextArrival, (PoissonContact.count_eq_zero_iff a t).mpr ht]
  rfl

noncomputable def nextContactDelayArray {n : ℕ} (F : ClockFrame n) (data : PoissonClockData n) :
    ClockArray n :=
  fun c => match c with
  | (v, none) => data (v, none)
  | (v, some w) => PoissonContact.nextArrival (data (v, some w)) (F.time - F.birthTime v)

theorem firstLiveClock_congr_on_live {n : ℕ} (z : PopulationState n) (s t : ClockArray n)
    (he : ∀ c ∈ z.liveSlots, s c = t c) : firstLiveClock z s = firstLiveClock z t := by
  have hw : ∀ c, StrictLiveWinner z s c ↔ StrictLiveWinner z t c := by
    intro c
    constructor
    · rintro ⟨hc, hh⟩
      refine ⟨hc, ?_⟩
      intro d hd hdc
      rw [← he c hc, ← he d hd]
      exact hh d hd hdc
    · rintro ⟨hc, hh⟩
      refine ⟨hc, ?_⟩
      intro d hd hdc
      rw [he c hc, he d hd]
      exact hh d hd hdc
  cases hs : firstLiveClock z s with
  | none =>
    apply Eq.symm
    apply (firstLiveClock_none_iff z t).mpr
    intro ht
    obtain ⟨c, hc⟩ := ht
    exact ((firstLiveClock_none_iff z s).mp hs) ⟨c, (hw c).mpr hc⟩
  | some c =>
    apply Eq.symm
    exact (firstLiveClock_some_iff z t c).mpr ((hw c).mp ((firstLiveClock_some_iff z s c).mp hs))

theorem clockFrameStep_congr_on_live {n : ℕ} (F : ClockFrame n) (s t : ClockArray n)
    (he : ∀ c ∈ F.population.liveSlots, s c = t c) :
    clockFrameStep F s = clockFrameStep F t := by
  have hrem : ∀ c ∈ F.population.liveSlots, remainingClock F s c = remainingClock F t c := by
    intro c hc
    rw [remainingClock, remainingClock, he c hc]
  have hchoice := firstLiveClock_congr_on_live F.population (remainingClock F s) (remainingClock F t) hrem
  cases hs : firstLiveClock F.population (remainingClock F s) with
  | none => simp only [clockFrameStep, hs, ← hchoice]
  | some c =>
    have hc := ((firstLiveClock_some_iff F.population (remainingClock F s) c).mp hs).1
    rw [clockFrameStep, hs, clockFrameStep, ← hchoice, hs]
    change advanceClockFrame F s c = advanceClockFrame F t c
    simp only [advanceClockFrame, hrem c hc]

/-- For a live pair the first point has not yet occurred. The next point
of its entire actual contact process is consequently still that first point. -/
theorem nextContactDelayArray_eq_on_live {n : ℕ} (F : ClockFrame n) (data : PoissonClockData n)
    (hf : FutureLiveClocks F (firstArrivalArray data)) :
    ∀ c ∈ F.population.liveSlots, nextContactDelayArray F data c = firstArrivalArray data c := by
  rintro ⟨v, w⟩ hc
  cases w with
  | none => rfl
  | some w =>
    have hh := hf (v, some w) hc
    change 0 < PoissonContact.first (data (v, some w)) - (F.time - F.birthTime v) at hh
    exact PoissonContact.nextArrival_eq_first (by linarith)

/-- A full contact-process step uses the next actual point after the
current infection age in each live contact path. It never resamples a path. -/
noncomputable def poissonFullContactStep {n : ℕ} (F : ClockFrame n) (data : PoissonClockData n) :
    ClockFrame n := clockFrameStep F (nextContactDelayArray F data)

noncomputable def poissonFullContactRun (n : ℕ) (data : PoissonClockData n) : ℕ → ClockFrame n
  | 0 => initialClockFrame n
  | k + 1 => poissonFullContactStep (poissonFullContactRun n data k) data

theorem poissonFullContactRun_eq_preassigned (n : ℕ) (data : PoissonClockData n)
    (hpositive : ∀ c, 0 < firstArrivalArray data c) :
    poissonFullContactRun n data = preassignedRun n (firstArrivalArray data) := by
  funext k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [poissonFullContactRun, ih]
    change clockFrameStep (preassignedRun n (firstArrivalArray data) k)
        (nextContactDelayArray (preassignedRun n (firstArrivalArray data) k) data) =
      clockFrameStep (preassignedRun n (firstArrivalArray data) k) (firstArrivalArray data)
    exact clockFrameStep_congr_on_live _ _ _
      (nextContactDelayArray_eq_on_live _ data (preassignedRun_future n hpositive k))

end Freezing1.SIR
