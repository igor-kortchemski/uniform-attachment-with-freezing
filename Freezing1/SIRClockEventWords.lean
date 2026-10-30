module

public import Freezing1.SIRRelevantClockChoice

/-!
# Finite event words of the actual static-array epidemic

Words store the newest event first. Their population replay and the actual
run therefore satisfy definitionally aligned one-event recursions. No path
law identity is assumed in this representation.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

abbrev ClockChoice (n : ℕ) := Option (ClockSlot n)
abbrev ClockWord (n : ℕ) := List (ClockChoice n)

instance (n : ℕ) : MeasurableSpace (ClockWord n) := ⊤
instance (n : ℕ) : DiscreteMeasurableSpace (ClockWord n) := ⟨fun _ => trivial⟩

noncomputable def optionPopulationStep {n : ℕ} (z : PopulationState n)
    (choice : ClockChoice n) : PopulationState n := choice.elim z (populationStep z)

noncomputable def replayPopulation (n : ℕ) : ClockWord n → PopulationState n
  | [] => initialPopulation n
  | c :: w => optionPopulationStep (replayPopulation n w) c

theorem replayPopulation_valid (n : ℕ) (w : ClockWord n) : (replayPopulation n w).Valid := by
  induction w with
  | nil => exact initialPopulation_valid n
  | cons c w ih =>
    cases c with
    | none => exact ih
    | some c => exact ih.step c

noncomputable def preassignedEvent (n : ℕ) (omega : ClockArray n) (k : ℕ) : ClockChoice n :=
  firstLiveClock (preassignedRun n omega k).population
    (remainingClock (preassignedRun n omega k) omega)

noncomputable def preassignedWord (n : ℕ) (omega : ClockArray n) : ℕ → ClockWord n
  | 0 => []
  | k + 1 => preassignedEvent n omega k :: preassignedWord n omega k

theorem preassignedWord_length (n : ℕ) (omega : ClockArray n) (k : ℕ) :
    (preassignedWord n omega k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [preassignedWord, ih]

theorem preassignedRun_population_replay (n : ℕ) (omega : ClockArray n) (k : ℕ) :
    (preassignedRun n omega k).population = replayPopulation n (preassignedWord n omega k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [preassignedWord, replayPopulation, preassignedRun]
    unfold preassignedEvent clockFrameStep
    cases hs : firstLiveClock (preassignedRun n omega k).population
        (remainingClock (preassignedRun n omega k) omega) with
    | none => simpa only [hs, optionPopulationStep, Option.elim_none] using ih
    | some c =>
      simp only [optionPopulationStep, Option.elim_some, advanceClockFrame_population, ih]

theorem measurable_preassignedEvent (n k : ℕ) : Measurable (fun omega => preassignedEvent n omega k) := by
  have hframe : Measurable (fun omega => preassignedRun n omega k) :=
    (measurable_pi_apply k).comp (measurable_preassignedRun n)
  have hpop : Measurable (fun p : ClockFrame n × ClockArray n => p.1.population) :=
    measurable_fst.comp measurable_fst
  have hargs : Measurable (fun p : ClockFrame n × ClockArray n =>
      (p.1.population, remainingClock p.1 p.2)) :=
    hpop.prodMk (measurable_remainingClock_joint n)
  have hchoice := (measurable_firstLiveClock_joint n).comp hargs
  change Measurable (((fun p : PopulationState n × ClockArray n => firstLiveClock p.1 p.2) ∘
    (fun p : ClockFrame n × ClockArray n => (p.1.population, remainingClock p.1 p.2))) ∘
      (fun omega : ClockArray n => (preassignedRun n omega k, omega)))
  exact hchoice.comp (hframe.prodMk measurable_id)

theorem measurable_preassignedWord (n k : ℕ) : Measurable (fun omega => preassignedWord n omega k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hcons : Measurable (fun p : ClockChoice n × ClockWord n => p.1 :: p.2) :=
      measurable_of_countable _
    exact hcons.comp ((measurable_preassignedEvent n k).prodMk ih)

def clockPrefixEvent (n : ℕ) (w : ClockWord n) : Set (ClockArray n) :=
  {omega | preassignedWord n omega w.length = w}

theorem measurableSet_clockPrefixEvent (n : ℕ) (w : ClockWord n) :
    MeasurableSet (clockPrefixEvent n w) :=
  (measurableSet_singleton w).preimage (measurable_preassignedWord n w.length)

theorem clockPrefixEvent_nil (n : ℕ) : clockPrefixEvent n [] = univ := by
  ext omega
  simp [clockPrefixEvent, preassignedWord]

theorem clockPrefixEvent_cons (n : ℕ) (c : ClockChoice n) (w : ClockWord n) :
    clockPrefixEvent n (c :: w) = clockPrefixEvent n w ∩
      {omega | preassignedEvent n omega w.length = c} := by
  ext omega
  simp only [clockPrefixEvent, Set.mem_ofPred_eq, List.length_cons, preassignedWord,
    List.cons.injEq, Set.mem_inter_iff]
  tauto

theorem population_eq_replay_of_prefix {n : ℕ} {omega : ClockArray n} {w : ClockWord n}
    (hw : omega ∈ clockPrefixEvent n w) :
    (preassignedRun n omega w.length).population = replayPopulation n w := by
  have hh := preassignedRun_population_replay n omega w.length
  rw [hw] at hh
  exact hh

theorem measurable_relevantClockView_joint (n : ℕ) :
    Measurable (fun p : ClockFrame n × ClockArray n => relevantClockView p.1 p.2) := by
  apply Measurable.of_eval
  intro c
  have hp : Measurable (fun p : ClockFrame n × ClockArray n => c.1 ∈ p.1.population.active) :=
    (measurable_of_countable (fun z : PopulationState n => c.1 ∈ z.active)).comp
      (measurable_fst.comp measurable_fst)
  have hremain : Measurable (fun p : ClockFrame n × ClockArray n => remainingClock p.1 p.2 c) :=
    (measurable_pi_apply c).comp (measurable_remainingClock_joint n)
  have hraw : Measurable (fun p : ClockFrame n × ClockArray n => p.2 c) :=
    (measurable_pi_apply c).comp measurable_snd
  exact Measurable.ite hp.setOf hremain hraw

noncomputable def clockPrefixResidual (n : ℕ) (w : ClockWord n) (omega : ClockArray n) :
    RelevantCoordinate (replayPopulation n w) → ℝ :=
  fun c => relevantClockView (preassignedRun n omega w.length) omega c.val

theorem measurable_clockPrefixResidual (n : ℕ) (w : ClockWord n) :
    Measurable (clockPrefixResidual n w) := by
  have hframe : Measurable (fun omega => preassignedRun n omega w.length) :=
    (measurable_pi_apply w.length).comp (measurable_preassignedRun n)
  have hview : Measurable (fun omega =>
      relevantClockView (preassignedRun n omega w.length) omega) :=
    (measurable_relevantClockView_joint n).comp (hframe.prodMk measurable_id)
  exact Measurable.of_eval fun c => (measurable_pi_apply c.val).comp hview

noncomputable def clockChoiceWeight {n : ℕ} (r : ℝ) (z : PopulationState n) : ClockChoice n → ℝ≥0∞
  | none => if z.active = ∅ then 1 else 0
  | some c => if c ∈ z.liveSlots then ENNReal.ofReal
      (clockSlotRate r c / ((z.active.card : ℝ) * (1 + r * z.susceptible.card))) else 0

noncomputable def clockWordWeight (r : ℝ) (n : ℕ) : ClockWord n → ℝ≥0∞
  | [] => 1
  | c :: w => clockWordWeight r n w * clockChoiceWeight r (replayPopulation n w) c

end Freezing1.SIR
