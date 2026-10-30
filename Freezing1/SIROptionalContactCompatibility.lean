module

public import Freezing1.SIROptionalContactProtocol

/-! The optional next-point protocol agrees with the positive-path protocol. -/

@[expose] public section

namespace Freezing1.SIR

open scoped Classical

set_option backward.isDefEq.respectTransparency false

def recoveryContactData {n : ℕ} (recovery : Individual n → ℝ)
    (contacts : Individual n → Individual n → PoissonContact.ArrivalPath) : PoissonClockData n :=
  fun c => match c with
    | (v, none) => recovery v
    | (v, some w) => contacts v w

theorem optionalEventTime_arrivals {n : ℕ} (F : ClockFrame n)
    (recovery : Individual n → ℝ)
    (contacts : Individual n → Individual n → PoissonContact.ArrivalPath) (c : ClockSlot n) :
    optionalEventTime F recovery (fun v w => Sum.inr (contacts v w)) c =
      some (F.time + remainingClock F
        (nextContactDelayArray F (recoveryContactData recovery contacts)) c) := by
  rcases c with ⟨v, w⟩
  cases w <;>
    simp only [optionalEventTime, nextContactDelayArray, recoveryContactData, remainingClock]
  all_goals congr 1; ring

theorem finiteOptionalWinner_arrivals_iff {n : ℕ} (F : ClockFrame n)
    (recovery : Individual n → ℝ)
    (contacts : Individual n → Individual n → PoissonContact.ArrivalPath)
    (c : ClockSlot n) (t : ℝ) :
    FiniteOptionalWinner F recovery (fun v w => Sum.inr (contacts v w)) (c, t) ↔
      StrictLiveWinner F.population
        (remainingClock F (nextContactDelayArray F (recoveryContactData recovery contacts))) c ∧
      t = F.time + remainingClock F
        (nextContactDelayArray F (recoveryContactData recovery contacts)) c := by
  constructor
  · rintro ⟨hc, ht, hall⟩
    have he : F.time + remainingClock F
        (nextContactDelayArray F (recoveryContactData recovery contacts)) c = t :=
      Option.some.inj ((optionalEventTime_arrivals F recovery contacts c).symm.trans ht)
    refine ⟨⟨hc, ?_⟩, he.symm⟩
    intro d hd hdc
    have hh := hall d hd hdc _ (optionalEventTime_arrivals F recovery contacts d)
    linarith
  · rintro ⟨⟨hc, hall⟩, rfl⟩
    refine ⟨hc, optionalEventTime_arrivals F recovery contacts c, ?_⟩
    intro d hd hdc s hs
    have he := Option.some.inj ((optionalEventTime_arrivals F recovery contacts d).symm.trans hs)
    linarith [hall d hd hdc]

theorem optionalContactFrameStep_arrivals {n : ℕ} (F : ClockFrame n)
    (recovery : Individual n → ℝ)
    (contacts : Individual n → Individual n → PoissonContact.ArrivalPath) :
    optionalContactFrameStep F recovery (fun v w => Sum.inr (contacts v w)) =
      poissonFullContactStep F (recoveryContactData recovery contacts) := by
  let a := nextContactDelayArray F (recoveryContactData recovery contacts)
  cases hs : firstLiveClock F.population (remainingClock F a) with
  | none =>
    have hn : firstOptionalEvent F recovery (fun v w => Sum.inr (contacts v w)) = none := by
      unfold firstOptionalEvent
      have he : ¬∃ q, FiniteOptionalWinner F recovery (fun v w => Sum.inr (contacts v w)) q := by
        rintro ⟨⟨c, t⟩, hq⟩
        exact (firstLiveClock_none_iff _ _).mp hs
          ⟨c, ((finiteOptionalWinner_arrivals_iff F recovery contacts c t).mp hq).1⟩
      rw [dite_eq_right he]
    rw [optionalContactFrameStep, hn]
    change F = clockFrameStep F a
    rw [clockFrameStep, hs]
  | some c =>
    have hw := (firstLiveClock_some_iff _ _ _).mp hs
    have hq := (finiteOptionalWinner_arrivals_iff F recovery contacts c
      (F.time + remainingClock F a c)).mpr ⟨hw, rfl⟩
    rw [optionalContactFrameStep_of_winner _ _ _ _ _ hq]
    change _ = clockFrameStep F a
    rw [clockFrameStep, hs]
    rfl

theorem optionalContactRun_arrivals (n : ℕ) (recovery : Individual n → ℝ)
    (contacts : Individual n → Individual n → PoissonContact.ArrivalPath) :
    optionalContactRun n recovery (fun v w => Sum.inr (contacts v w)) =
      poissonFullContactRun n (recoveryContactData recovery contacts) := by
  funext k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [optionalContactRun, poissonFullContactRun, ih, optionalContactFrameStep_arrivals]

end Freezing1.SIR
