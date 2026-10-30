module

public import Freezing1.SIRClockPopulationUpdates
public import Freezing1.SIRExponentialMemoryless

/-!
# A deterministic epidemic driven by one preassigned clock array

The array is sampled once. A slot stores a delay relative to its source's
infection time. Advancing the process never resamples any coordinate.
When a live minimum is not strict the totalized process holds; this includes
the absorbing state and null race-tie cases. Positive-rate finite races are
proved separately to have a strict winner almost surely.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

abbrev ClockArray (n : ℕ) := ClockSlot n → ℝ

instance (n : ℕ) : MeasurableSpace (Option (ClockSlot n)) := ⊤
instance (n : ℕ) : DiscreteMeasurableSpace (Option (ClockSlot n)) := ⟨fun _ => trivial⟩

def StrictLiveWinner {n : ℕ} (z : PopulationState n) (t : ClockArray n)
    (c : ClockSlot n) : Prop :=
  c ∈ z.liveSlots ∧ ∀ d ∈ z.liveSlots, d ≠ c → t c < t d

theorem StrictLiveWinner.unique {n : ℕ} {z : PopulationState n} {t : ClockArray n}
    {c d : ClockSlot n} (hc : StrictLiveWinner z t c) (hd : StrictLiveWinner z t d) :
    c = d := by
  by_contra hcd
  exact (hc.2 d hd.1 (fun h => hcd h.symm)).not_gt (hd.2 c hc.1 hcd)

noncomputable def firstLiveClock {n : ℕ} (z : PopulationState n)
    (t : ClockArray n) : Option (ClockSlot n) :=
  if h : ∃ c, StrictLiveWinner z t c then some h.choose else none

theorem firstLiveClock_some_iff {n : ℕ} (z : PopulationState n) (t : ClockArray n)
    (c : ClockSlot n) : firstLiveClock z t = some c ↔ StrictLiveWinner z t c := by
  unfold firstLiveClock
  split_ifs with h
  · rw [Option.some.injEq]
    constructor
    · intro he
      exact he ▸ h.choose_spec
    · intro hc
      exact h.choose_spec.unique hc
  · constructor
    · intro he; cases he
    · intro hc; exact (h ⟨c, hc⟩).elim

theorem firstLiveClock_none_iff {n : ℕ} (z : PopulationState n) (t : ClockArray n) :
    firstLiveClock z t = none ↔ ¬∃ c, StrictLiveWinner z t c := by
  unfold firstLiveClock
  split_ifs <;> simp_all

theorem measurableSet_strictLiveWinner {n : ℕ} (z : PopulationState n) (c : ClockSlot n) :
    MeasurableSet {t : ClockArray n | StrictLiveWinner z t c} := by
  by_cases hc : c ∈ z.liveSlots
  · have he : {t : ClockArray n | StrictLiveWinner z t c} =
        ⋂ d : ClockSlot n, {t : ClockArray n | d ∈ z.liveSlots → d ≠ c → t c < t d} := by
      ext t
      simp [StrictLiveWinner, hc]
    rw [he]
    apply MeasurableSet.iInter
    intro d
    by_cases hd : d ∈ z.liveSlots <;> by_cases hdc : d = c
    · simp [hdc]
    · simpa [hd, hdc] using measurableSet_lt (measurable_pi_apply c) (measurable_pi_apply d)
    · simp [hd]
    · simp [hd]
  · have he : {t : ClockArray n | StrictLiveWinner z t c} = ∅ := by
      ext t
      simp [StrictLiveWinner, hc]
    rw [he]
    exact MeasurableSet.empty

theorem measurable_firstLiveClock {n : ℕ} (z : PopulationState n) :
    Measurable (firstLiveClock z) := by
  apply measurable_to_countable'
  intro c
  cases c with
  | none =>
    have he : firstLiveClock z ⁻¹' {none} =
        (⋃ d : ClockSlot n, {t : ClockArray n | StrictLiveWinner z t d})ᶜ := by
      ext t
      simp [firstLiveClock_none_iff]
    rw [he]
    exact (MeasurableSet.iUnion (measurableSet_strictLiveWinner z)).compl
  | some c =>
    have he : firstLiveClock z ⁻¹' {some c} =
        {t : ClockArray n | StrictLiveWinner z t c} := by
      ext t
      simp [firstLiveClock_some_iff]
    rw [he]
    exact measurableSet_strictLiveWinner z c

abbrev ClockFrame (n : ℕ) := PopulationState n × ℝ × (Individual n → ℝ)

def ClockFrame.population {n : ℕ} (F : ClockFrame n) : PopulationState n := F.1
def ClockFrame.time {n : ℕ} (F : ClockFrame n) : ℝ := F.2.1
def ClockFrame.birthTime {n : ℕ} (F : ClockFrame n) : Individual n → ℝ := F.2.2

def initialClockFrame (n : ℕ) : ClockFrame n := (initialPopulation n, 0, fun _ => 0)

def absoluteClock {n : ℕ} (F : ClockFrame n) (omega : ClockArray n) (c : ClockSlot n) : ℝ :=
  F.birthTime c.1 + omega c

def remainingClock {n : ℕ} (F : ClockFrame n) (omega : ClockArray n) (c : ClockSlot n) : ℝ :=
  omega c - (F.time - F.birthTime c.1)

theorem time_add_remainingClock {n : ℕ} (F : ClockFrame n) (omega : ClockArray n)
    (c : ClockSlot n) : F.time + remainingClock F omega c = absoluteClock F omega c := by
  unfold remainingClock absoluteClock
  ring

def relevantClockView {n : ℕ} (F : ClockFrame n) (omega : ClockArray n)
    (c : ClockSlot n) : ℝ :=
  if c.1 ∈ F.population.active then remainingClock F omega c else omega c

noncomputable def advanceClockFrame {n : ℕ} (F : ClockFrame n) (omega : ClockArray n)
    (c : ClockSlot n) : ClockFrame n :=
  let time := F.time + remainingClock F omega c
  let births := match c.2 with
    | none => F.birthTime
    | some w => Function.update F.birthTime w time
  (populationStep F.population c, time, births)

noncomputable def clockFrameStep {n : ℕ} (F : ClockFrame n) (omega : ClockArray n) :
    ClockFrame n :=
  match firstLiveClock F.population (remainingClock F omega) with
  | none => F
  | some c => advanceClockFrame F omega c

noncomputable def preassignedRun (n : ℕ) (omega : ClockArray n) : ℕ → ClockFrame n
  | 0 => initialClockFrame n
  | k + 1 => clockFrameStep (preassignedRun n omega k) omega

theorem advanceClockFrame_time {n : ℕ} (F : ClockFrame n) (omega : ClockArray n)
    (c : ClockSlot n) : (advanceClockFrame F omega c).time = absoluteClock F omega c :=
  time_add_remainingClock F omega c

theorem advanceClockFrame_population {n : ℕ} (F : ClockFrame n) (omega : ClockArray n)
    (c : ClockSlot n) :
    (advanceClockFrame F omega c).population = populationStep F.population c := rfl

theorem preassignedRun_population_valid (n : ℕ) (omega : ClockArray n) (k : ℕ) :
    (preassignedRun n omega k).population.Valid := by
  induction k with
  | zero => exact initialPopulation_valid n
  | succ k ih =>
    change (clockFrameStep (preassignedRun n omega k) omega).population.Valid
    unfold clockFrameStep
    split
    · exact ih
    · exact ih.step _

noncomputable def preassignedClockLaw (r : ℝ) (n : ℕ) : Measure (ClockArray n) :=
  Measure.pi (fun c => expMeasure (clockSlotRate r c))

theorem preassignedClockLaw_probability {r : ℝ} (hr : 0 < r) (n : ℕ) :
    IsProbabilityMeasure (preassignedClockLaw r n) := by
  have : ∀ c : ClockSlot n, IsProbabilityMeasure (expMeasure (clockSlotRate r c)) :=
    fun c => isProbabilityMeasure_expMeasure (clockSlotRate_pos hr c)
  unfold preassignedClockLaw
  infer_instance

theorem measurable_firstLiveClock_joint (n : ℕ) :
    Measurable (fun p : PopulationState n × ClockArray n => firstLiveClock p.1 p.2) :=
  measurable_from_prod_countable_right (fun z => measurable_firstLiveClock z)

theorem measurable_remainingClock_joint (n : ℕ) :
    Measurable (fun p : ClockFrame n × ClockArray n => remainingClock p.1 p.2) := by
  unfold remainingClock ClockFrame.time ClockFrame.birthTime
  fun_prop

theorem measurable_advanceClockFrame {n : ℕ} (c : ClockSlot n) :
    Measurable (fun p : ClockFrame n × ClockArray n => advanceClockFrame p.1 p.2 c) := by
  have hpop : Measurable (fun p : ClockFrame n × ClockArray n =>
      populationStep p.1.population c) :=
    (measurable_of_countable (fun z : PopulationState n => populationStep z c)).comp
      (measurable_fst.comp measurable_fst)
  have htime : Measurable (fun p : ClockFrame n × ClockArray n =>
      p.1.time + remainingClock p.1 p.2 c) := by
    unfold remainingClock ClockFrame.time ClockFrame.birthTime
    fun_prop
  have hbirth : Measurable (fun p : ClockFrame n × ClockArray n => p.1.birthTime) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  unfold advanceClockFrame
  apply hpop.prodMk
  apply htime.prodMk
  cases hc : c.2 with
  | none => exact hbirth
  | some w =>
    apply Measurable.of_eval
    intro j
    by_cases hj : j = w
    · simpa [hj] using htime
    · simpa [hj, Function.comp_def] using (measurable_pi_apply j).comp hbirth

theorem measurable_clockFrameStep (n : ℕ) :
    Measurable (fun p : ClockFrame n × ClockArray n => clockFrameStep p.1 p.2) := by
  have hpop : Measurable (fun p : ClockFrame n × ClockArray n => p.1.population) :=
    measurable_fst.comp measurable_fst
  have hargs : Measurable (fun p : ClockFrame n × ClockArray n =>
      (p.1.population, remainingClock p.1 p.2)) :=
    hpop.prodMk (measurable_remainingClock_joint n)
  have hchoice : Measurable (fun p : ClockFrame n × ClockArray n =>
      firstLiveClock p.1.population (remainingClock p.1 p.2)) := by
    change Measurable ((fun q : PopulationState n × ClockArray n =>
      firstLiveClock q.1 q.2) ∘ (fun p : ClockFrame n × ClockArray n =>
        (p.1.population, remainingClock p.1 p.2)))
    exact (measurable_firstLiveClock_joint n).comp hargs
  have hpiece : Measurable (fun p : (ClockFrame n × ClockArray n) × Option (ClockSlot n) =>
      match p.2 with
      | none => p.1.1
      | some c => advanceClockFrame p.1.1 p.1.2 c) := by
    apply measurable_from_prod_countable_left
    intro c
    cases c with
    | none => exact measurable_fst
    | some c => exact measurable_advanceClockFrame c
  exact hpiece.comp (measurable_id.prodMk hchoice)

theorem measurable_preassignedRun (n : ℕ) : Measurable (preassignedRun n) := by
  apply Measurable.of_eval
  intro k
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    change Measurable (fun omega : ClockArray n =>
      clockFrameStep (preassignedRun n omega k) omega)
    change Measurable ((fun p : ClockFrame n × ClockArray n => clockFrameStep p.1 p.2) ∘
      (fun omega : ClockArray n => (preassignedRun n omega k, omega)))
    exact (measurable_clockFrameStep n).comp (ih.prodMk measurable_id)

theorem preassignedClockLaw_positive {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ∀ᵐ omega ∂preassignedClockLaw r n, ∀ c, 0 < omega c := by
  have : IsProbabilityMeasure (preassignedClockLaw r n) := preassignedClockLaw_probability hr n
  have : ∀ c : ClockSlot n, IsProbabilityMeasure (expMeasure (clockSlotRate r c)) :=
    fun c => isProbabilityMeasure_expMeasure (clockSlotRate_pos hr c)
  have hmeas : MeasurableSet {omega : ClockArray n | ∀ c, 0 < omega c} := by
    apply measurableSet_setOfPred.mpr
    exact Measurable.forall fun c => measurableSet_setOfPred.mp
      (measurableSet_lt measurable_const (measurable_pi_apply c))
  apply (mem_ae_iff_prob_eq_one hmeas).mpr
  have he : {omega : ClockArray n | ∀ c, 0 < omega c} =
      Set.pi univ (fun _ => Ioi (0 : ℝ)) := by
    ext omega
    simp [Set.mem_pi]
  rw [he, preassignedClockLaw, Measure.pi_pi]
  simp_rw [expMeasure_Ioi_of_nonneg (clockSlotRate_pos hr _) (show (0 : ℝ) ≤ 0 by rfl)]
  simp

end Freezing1.SIR
