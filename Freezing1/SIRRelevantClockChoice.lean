module

public import Freezing1.SIRClockRelevantProduct
public import Freezing1.SIRPreassignedChronology

/-!
# The event choice is determined by the relevant residual coordinates

These lemmas connect the static-array event selector to the actual current
relevant product. A nonempty live family chooses an event almost surely;
holding is certain for an empty active population.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def fullRelevantClockArray {n : ℕ} (z : PopulationState n)
    (x : RelevantCoordinate z → ℝ) (c : ClockSlot n) : ℝ :=
  if hc : c ∈ z.relevantSlots then x ⟨c, hc⟩ else 0

theorem fullRelevantClockArray_live {n : ℕ} (z : PopulationState n)
    (x : RelevantCoordinate z → ℝ) {c : ClockSlot n} (hc : c ∈ z.liveSlots) :
    fullRelevantClockArray z x c = x ⟨c, Finset.mem_union_left _ hc⟩ := by
  have hR : c ∈ z.relevantSlots := Finset.mem_union_left _ hc
  rw [fullRelevantClockArray, dite_eq_left hR]

theorem measurable_fullRelevantClockArray {n : ℕ} (z : PopulationState n) :
    Measurable (fullRelevantClockArray z) := by
  apply Measurable.of_eval
  intro c
  by_cases hc : c ∈ z.relevantSlots
  · simpa only [fullRelevantClockArray, dite_eq_left hc] using
      (measurable_pi_apply (⟨c, hc⟩ : RelevantCoordinate z))
  · simpa only [fullRelevantClockArray, dite_eq_right hc] using
      (measurable_const : Measurable (fun _ : RelevantCoordinate z → ℝ => (0 : ℝ)))

noncomputable def relevantFirstLive {n : ℕ} (z : PopulationState n)
    (x : RelevantCoordinate z → ℝ) : Option (ClockSlot n) :=
  firstLiveClock z (fullRelevantClockArray z x)

theorem measurable_relevantFirstLive {n : ℕ} (z : PopulationState n) :
    Measurable (relevantFirstLive z) :=
  (measurable_firstLiveClock z).comp (measurable_fullRelevantClockArray z)

theorem relevantFirstLive_some_iff {n : ℕ} (z : PopulationState n)
    (x : RelevantCoordinate z → ℝ) {winner : ClockSlot n} (hw : winner ∈ z.liveSlots) :
    relevantFirstLive z x = some winner ↔ x ∈ populationRelevantWinner z hw := by
  rw [relevantFirstLive, firstLiveClock_some_iff]
  constructor
  · intro hs
    change (∀ d : LiveCoordinate z, d ≠ (⟨winner, hw⟩ : LiveCoordinate z) →
      (splitRelevantClocks z x).1 ⟨winner, hw⟩ < (splitRelevantClocks z x).1 d) ∧ True
    refine ⟨?_, trivial⟩
    intro d hd
    have hne : d.val ≠ winner := fun he => hd (Subtype.ext he)
    have hh := hs.2 d.val d.property hne
    simpa only [fullRelevantClockArray_live z x hw,
      fullRelevantClockArray_live z x d.property, splitRelevantClocks] using hh
  · intro hs
    refine ⟨hw, ?_⟩
    intro d hd hne
    have hdi : (⟨d, hd⟩ : LiveCoordinate z) ≠ ⟨winner, hw⟩ :=
      fun he => hne (congrArg Subtype.val he)
    have hh := hs.1 ⟨d, hd⟩ hdi
    simpa only [fullRelevantClockArray_live z x hw,
      fullRelevantClockArray_live z x hd, splitRelevantClocks] using hh

theorem firstLiveClock_congr {n : ℕ} (z : PopulationState n) (t u : ClockArray n)
    (h : ∀ c ∈ z.liveSlots, t c = u c) : firstLiveClock z t = firstLiveClock z u := by
  have hs : ∀ c, StrictLiveWinner z t c ↔ StrictLiveWinner z u c := by
    intro c
    constructor
    · intro hc
      refine ⟨hc.1, ?_⟩
      intro d hd hdc
      rw [← h c hc.1, ← h d hd]
      exact hc.2 d hd hdc
    · intro hc
      refine ⟨hc.1, ?_⟩
      intro d hd hdc
      rw [h c hc.1, h d hd]
      exact hc.2 d hd hdc
  cases ht : firstLiveClock z t with
  | none =>
    cases hu : firstLiveClock z u with
    | none => rfl
    | some c =>
      have hc := (firstLiveClock_some_iff z t c).mpr
        ((hs c).mpr ((firstLiveClock_some_iff z u c).mp hu))
      rw [ht] at hc
      cases hc
  | some c =>
    have hu := (firstLiveClock_some_iff z u c).mpr
      ((hs c).mp ((firstLiveClock_some_iff z t c).mp ht))
    exact hu.symm

theorem relevantFirstLive_static {n : ℕ} (F : ClockFrame n) (omega : ClockArray n) :
    relevantFirstLive F.population
      (fun c : RelevantCoordinate F.population => relevantClockView F omega c.val) =
      firstLiveClock F.population (remainingClock F omega) := by
  unfold relevantFirstLive
  apply firstLiveClock_congr
  intro c hc
  rw [fullRelevantClockArray_live _ _ hc]
  exact relevantClockView_of_live F omega hc

theorem relevant_live_clock_law {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {r : ℝ} (hr : 0 < r) :
    (Measure.pi (fun c : RelevantCoordinate z => expMeasure (clockSlotRate (n := n) r c.val))).map
      (fun x => (splitRelevantClocks z x).1) =
      Measure.pi (fun c : LiveCoordinate z => expMeasure (clockSlotRate (n := n) r c.val)) := by
  have : ∀ c : LiveCoordinate z, IsProbabilityMeasure (expMeasure (clockSlotRate (n := n) r c.val)) :=
    fun c => isProbabilityMeasure_expMeasure (clockSlotRate_pos hr c.val)
  have : ∀ c : UnusedCoordinate z, IsProbabilityMeasure (expMeasure (clockSlotRate (n := n) r c.val)) :=
    fun c => isProbabilityMeasure_expMeasure (clockSlotRate_pos hr c.val)
  change Measure.map (Prod.fst ∘ splitRelevantClocks z) _ = _
  rw [← Measure.map_map measurable_fst (measurable_splitRelevantClocks z),
    split_relevant_clock_product hz hr, Measure.map_fst_prod, measure_univ, one_smul]

theorem relevantFirstLive_some_ae {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {r : ℝ} (hr : 0 < r) (ha : z.active.Nonempty) :
    ∀ᵐ x ∂Measure.pi (fun c : RelevantCoordinate z => expMeasure (clockSlotRate (n := n) r c.val)),
      ∃ c, relevantFirstLive z x = some c := by
  obtain ⟨v, hv⟩ := ha
  have : Nonempty (LiveCoordinate z) := ⟨⟨(v, none), (recovery_mem_liveSlots z v).mpr hv⟩⟩
  have hh := independent_exponential_has_winner
    (fun c : LiveCoordinate z => clockSlotRate (n := n) r c.val)
    (fun c => clockSlotRate_pos hr c.val)
  rw [← relevant_live_clock_law hz hr] at hh
  have hmap := ae_of_ae_map
    (measurable_fst.comp (measurable_splitRelevantClocks z)).aemeasurable hh
  filter_upwards [hmap] with x hx
  obtain ⟨c, hc⟩ := hx
  refine ⟨c.val, (relevantFirstLive_some_iff z x c.property).mpr ?_⟩
  exact ⟨hc, Set.mem_univ _⟩

theorem relevantFirstLive_none_null {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {r : ℝ} (hr : 0 < r) (ha : z.active.Nonempty) :
    (Measure.pi (fun c : RelevantCoordinate z => expMeasure (clockSlotRate (n := n) r c.val)))
      {x | relevantFirstLive z x = none} = 0 := by
  have hh : ∀ᵐ x ∂Measure.pi
      (fun c : RelevantCoordinate z => expMeasure (clockSlotRate (n := n) r c.val)),
      relevantFirstLive z x ≠ none :=
    (relevantFirstLive_some_ae hz hr ha).mono fun _ ⟨c, hc⟩ => by rw [hc]; simp
  simpa only [not_not] using ae_iff.mp hh

theorem relevantFirstLive_none_of_active_empty {n : ℕ} {z : PopulationState n}
    (ha : z.active = ∅) (x : RelevantCoordinate z → ℝ) : relevantFirstLive z x = none := by
  apply (firstLiveClock_none_iff z _).mpr
  rintro ⟨c, hc⟩
  have hh := hc.1
  simp [PopulationState.liveSlots, ha] at hh

theorem relevantFirstLive_not_invalid {n : ℕ} (z : PopulationState n)
    (x : RelevantCoordinate z → ℝ) {c : ClockSlot n} (hc : c ∉ z.liveSlots) :
    relevantFirstLive z x ≠ some c := by
  intro he
  exact hc ((firstLiveClock_some_iff z _ c).mp he).1

end Freezing1.SIR
