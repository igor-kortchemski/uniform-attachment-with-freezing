module

public import Freezing1.PoissonContactOptional
public import Freezing1.SIRPoissonFullContacts

/-!
# Next-point SIR protocol with absent contact points

`none` is the absence of any next contact. Recovery events remain finite.
The protocol chooses a strict finite earliest event among the live slots;
it holds at absorption or a tie, as does the original full-contact protocol.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory
open scoped Classical

abbrev OptionalContactData (n : ℕ) := Individual n → Individual n → PoissonContact.OptionalPath

noncomputable def optionalEventTime {n : ℕ} (F : ClockFrame n)
    (recovery : Individual n → ℝ) (contacts : OptionalContactData n)
    (c : ClockSlot n) : Option ℝ :=
  match c with
  | (v, none) => some (F.birthTime v + recovery v)
  | (v, some w) => match contacts v w with
    | Sum.inl _ => none
    | Sum.inr a => some (F.birthTime v + PoissonContact.nextArrival a (F.time - F.birthTime v))

def FiniteOptionalWinner {n : ℕ} (F : ClockFrame n)
    (recovery : Individual n → ℝ) (contacts : OptionalContactData n)
    (q : ClockSlot n × ℝ) : Prop :=
  q.1 ∈ F.population.liveSlots ∧ optionalEventTime F recovery contacts q.1 = some q.2 ∧
    ∀ d ∈ F.population.liveSlots, d ≠ q.1 → ∀ t : ℝ,
      optionalEventTime F recovery contacts d = some t → q.2 < t

theorem FiniteOptionalWinner.unique {n : ℕ} {F : ClockFrame n}
    {recovery : Individual n → ℝ} {contacts : OptionalContactData n}
    {q r : ClockSlot n × ℝ} (hq : FiniteOptionalWinner F recovery contacts q)
    (hr : FiniteOptionalWinner F recovery contacts r) : q = r := by
  have hc : q.1 = r.1 := by
    by_contra hne
    exact (hq.2.2 r.1 hr.1 (Ne.symm hne) r.2 hr.2.1).not_gt
      (hr.2.2 q.1 hq.1 hne q.2 hq.2.1)
  apply Prod.ext hc
  exact Option.some.inj (hq.2.1.symm.trans (hc ▸ hr.2.1))

noncomputable def firstOptionalEvent {n : ℕ} (F : ClockFrame n)
    (recovery : Individual n → ℝ) (contacts : OptionalContactData n) :
    Option (ClockSlot n × ℝ) :=
  if h : ∃ q, FiniteOptionalWinner F recovery contacts q then some h.choose else none

theorem firstOptionalEvent_some_iff {n : ℕ} (F : ClockFrame n)
    (recovery : Individual n → ℝ) (contacts : OptionalContactData n) (q : ClockSlot n × ℝ) :
    firstOptionalEvent F recovery contacts = some q ↔ FiniteOptionalWinner F recovery contacts q := by
  unfold firstOptionalEvent
  split_ifs with h
  · rw [Option.some.injEq]
    exact ⟨fun he => he ▸ h.choose_spec, fun hq => h.choose_spec.unique hq⟩
  · constructor
    · intro he
      cases he
    · intro hq
      exact (h ⟨q, hq⟩).elim

noncomputable def optionalContactFrameStep {n : ℕ} (F : ClockFrame n)
    (recovery : Individual n → ℝ) (contacts : OptionalContactData n) : ClockFrame n :=
  match firstOptionalEvent F recovery contacts with
  | none => F
  | some (c, t) =>
      (populationStep F.population c, t,
        match c.2 with
        | none => F.birthTime
        | some w => Function.update F.birthTime w t)

theorem optionalContactFrameStep_of_winner {n : ℕ} (F : ClockFrame n)
    (recovery : Individual n → ℝ) (contacts : OptionalContactData n) (c : ClockSlot n) (t : ℝ)
    (hw : FiniteOptionalWinner F recovery contacts (c, t)) :
    optionalContactFrameStep F recovery contacts =
      (populationStep F.population c, t,
        match c.2 with
        | none => F.birthTime
        | some w => Function.update F.birthTime w t) := by
  rw [optionalContactFrameStep, (firstOptionalEvent_some_iff _ _ _ _).mpr hw]

theorem optionalContactFrameStep_of_absorbed {n : ℕ} (F : ClockFrame n)
    (recovery : Individual n → ℝ) (contacts : OptionalContactData n)
    (h : F.population.active = ∅) : optionalContactFrameStep F recovery contacts = F := by
  have hn : firstOptionalEvent F recovery contacts = none := by
    unfold firstOptionalEvent
    have he : ¬∃ q, FiniteOptionalWinner F recovery contacts q := by
      rintro ⟨q, hq⟩
      have := hq.1
      simp [PopulationState.liveSlots, h] at this
    rw [dite_eq_right he]
  rw [optionalContactFrameStep, hn]

noncomputable def optionalContactRun (n : ℕ) (recovery : Individual n → ℝ)
    (contacts : OptionalContactData n) : ℕ → ClockFrame n
  | 0 => initialClockFrame n
  | k + 1 => optionalContactFrameStep (optionalContactRun n recovery contacts k) recovery contacts

theorem initial_optional_winner_of_empty_contacts (n : ℕ)
    (recovery : Individual n → ℝ) (contacts : OptionalContactData n)
    (he : ∀ v w, contacts v w = PoissonContact.emptyPath) :
    FiniteOptionalWinner (initialClockFrame n) recovery contacts ((0, none), recovery 0) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [initialClockFrame, ClockFrame.population, initialPopulation]
  · simp [optionalEventTime, initialClockFrame, ClockFrame.birthTime]
  · rintro ⟨v, w⟩ hd hne t ht
    have hv : v = 0 := by
      have hh := (Finset.mem_product.mp hd).1
      simpa [initialClockFrame, ClockFrame.population, initialPopulation] using hh
    subst v
    cases w with
    | none => exact (hne rfl).elim
    | some w => simp [optionalEventTime, he, PoissonContact.emptyPath] at ht

def recoveredRootFrame (n : ℕ) (recovery : Individual n → ℝ) : ClockFrame n :=
  (recoverPopulation (initialPopulation n) 0, recovery 0, fun _ => 0)

theorem optionalContactRun_succ_of_empty_contacts (n : ℕ)
    (recovery : Individual n → ℝ) (contacts : OptionalContactData n)
    (he : ∀ v w, contacts v w = PoissonContact.emptyPath) (k : ℕ) :
    optionalContactRun n recovery contacts (k + 1) = recoveredRootFrame n recovery := by
  induction k with
  | zero =>
    rw [optionalContactRun, optionalContactRun,
      optionalContactFrameStep_of_winner _ _ _ _ _
        (initial_optional_winner_of_empty_contacts n recovery contacts he)]
    simp [populationStep, initialClockFrame, ClockFrame.population, ClockFrame.birthTime,
      initialPopulation, recoveredRootFrame]
  | succ k ih =>
    rw [optionalContactRun, ih]
    exact optionalContactFrameStep_of_absorbed _ _ _ (by
      simp [recoveredRootFrame, ClockFrame.population, recoverPopulation, initialPopulation])

end Freezing1.SIR
