module

public import Freezing1.SIRClockRaceStep

/-!
# The actual relevant product gives the next relevant product

The live and unused coordinates are projected jointly from the current
independent relevant clock family. The concrete one-event law therefore
requires no additional independence premise.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

def combinedRelevantCoordinate {n : ℕ} (z : PopulationState n) :
    (LiveCoordinate z ⊕ UnusedCoordinate z) → RelevantCoordinate z :=
  Sum.elim (fun c => ⟨c.val, Finset.mem_union_left _ c.property⟩)
    (fun c => ⟨c.val, Finset.mem_union_right _ c.property⟩)

theorem combinedRelevantCoordinate_injective {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) : Function.Injective (combinedRelevantCoordinate z) := by
  intro c d he
  cases c with
  | inl c =>
    cases d with
    | inl d =>
      congr 1
      exact Subtype.ext (congrArg (fun x : RelevantCoordinate z => x.val) he)
    | inr d =>
      have hv := congrArg Subtype.val he
      exact (Finset.disjoint_left.mp hz.live_disjoint_unused c.property
        (hv.symm ▸ d.property)).elim
  | inr c =>
    cases d with
    | inl d =>
      have hv := congrArg Subtype.val he
      exact (Finset.disjoint_left.mp hz.live_disjoint_unused
        (hv.symm ▸ d.property) c.property).elim
    | inr d =>
      congr 1
      exact Subtype.ext (congrArg (fun x : RelevantCoordinate z => x.val) he)

def splitRelevantClocks {n : ℕ} (z : PopulationState n)
    (x : RelevantCoordinate z → ℝ) : (LiveCoordinate z → ℝ) × (UnusedCoordinate z → ℝ) :=
  (fun c => x ⟨c.val, Finset.mem_union_left _ c.property⟩,
    fun c => x ⟨c.val, Finset.mem_union_right _ c.property⟩)

theorem measurable_splitRelevantClocks {n : ℕ} (z : PopulationState n) :
    Measurable (splitRelevantClocks z) :=
  (Measurable.of_eval fun c => measurable_pi_apply
    (⟨c.val, Finset.mem_union_left _ c.property⟩ : RelevantCoordinate z)).prodMk
      (Measurable.of_eval fun c => measurable_pi_apply
        (⟨c.val, Finset.mem_union_right _ c.property⟩ : RelevantCoordinate z))

theorem split_relevant_clock_product {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {r : ℝ} (hr : 0 < r) :
    (Measure.pi (fun c : RelevantCoordinate z => expMeasure (clockSlotRate (n := n) r c.val))).map
      (splitRelevantClocks z) =
      (Measure.pi (fun c : LiveCoordinate z => expMeasure (clockSlotRate (n := n) r c.val))).prod
        (Measure.pi (fun c : UnusedCoordinate z => expMeasure (clockSlotRate (n := n) r c.val))) := by
  let rate : (LiveCoordinate z ⊕ UnusedCoordinate z) → ℝ :=
    fun c => clockSlotRate (n := n) r (combinedRelevantCoordinate z c).val
  have : ∀ c, IsProbabilityMeasure (expMeasure (rate c)) :=
    fun c => isProbabilityMeasure_expMeasure (clockSlotRate_pos hr _)
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : LiveCoordinate z ⊕ UnusedCoordinate z => ℝ)
  have hprod : (Measure.pi (fun c => expMeasure (rate c))).map e =
      (Measure.pi (fun c : LiveCoordinate z => expMeasure (clockSlotRate (n := n) r c.val))).prod
        (Measure.pi (fun c : UnusedCoordinate z => expMeasure (clockSlotRate (n := n) r c.val))) :=
    (measurePreserving_sumPiEquivProdPi (fun c => expMeasure (rate c))).map_eq
  have hm : Measurable (fun x : RelevantCoordinate z → ℝ =>
      fun c : LiveCoordinate z ⊕ UnusedCoordinate z => x (combinedRelevantCoordinate z c)) :=
    Measurable.of_eval fun c => measurable_pi_apply (combinedRelevantCoordinate z c)
  calc
    _ = ((Measure.pi (fun c : RelevantCoordinate z =>
        expMeasure (clockSlotRate (n := n) r c.val))).map
        (fun x : RelevantCoordinate z → ℝ => fun c => x (combinedRelevantCoordinate z c))).map e := by
      rw [Measure.map_map e.measurable hm]
      rfl
    _ = _ := by
      rw [independent_clock_coordinate_projection _
        (fun c : RelevantCoordinate z => clockSlotRate_pos hr c.val)
        (combinedRelevantCoordinate z) (combinedRelevantCoordinate_injective hz)]
      exact hprod

theorem measurable_designatedRaceWithUnused {L U J : Type*} (i : L)
    (pick : J → ({j : L // j ≠ i} ⊕ U)) : Measurable (designatedRaceWithUnused i pick) := by
  have hres : Measurable (fun z : (L → ℝ) × (U → ℝ) =>
      (fun j : {j : L // j ≠ i} => z.1 j - z.1 i, z.2)) := by fun_prop
  exact ((measurable_pi_apply i).comp measurable_fst).prodMk
    ((measurable_untouchedClockProject i pick).comp hres)

theorem measurable_populationNextClockView {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {winner : ClockSlot n} (hw : winner ∈ z.liveSlots) :
    Measurable (populationNextClockView hz hw) :=
  measurable_designatedRaceWithUnused (⟨winner, hw⟩ : LiveCoordinate z) (nextClockCoordinate hz hw)

def populationRelevantWinner {n : ℕ} (z : PopulationState n)
    {winner : ClockSlot n} (hw : winner ∈ z.liveSlots) : Set (RelevantCoordinate z → ℝ) :=
  splitRelevantClocks z ⁻¹' (clockWins (⟨winner, hw⟩ : LiveCoordinate z) ×ˢ univ)

noncomputable def populationNextRelevantView {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {winner : ClockSlot n} (hw : winner ∈ z.liveSlots) :
    (RelevantCoordinate z → ℝ) → ℝ × (RelevantCoordinate (populationStep z winner) → ℝ) :=
  populationNextClockView hz hw ∘ splitRelevantClocks z

theorem measurableSet_populationRelevantWinner {n : ℕ} (z : PopulationState n)
    {winner : ClockSlot n} (hw : winner ∈ z.liveSlots) :
    MeasurableSet (populationRelevantWinner z hw) :=
  ((measurableSet_clockWins (⟨winner, hw⟩ : LiveCoordinate z)).prod MeasurableSet.univ).preimage
    (measurable_splitRelevantClocks z)

theorem measurable_populationNextRelevantView {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {winner : ClockSlot n} (hw : winner ∈ z.liveSlots) :
    Measurable (populationNextRelevantView hz hw) :=
  (measurable_populationNextClockView hz hw).comp (measurable_splitRelevantClocks z)

/-- The next clock law follows from the current relevant product itself;
live/unused independence is a conclusion of its coordinate projection. -/
theorem population_relevant_winner_next_clock_law {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {r : ℝ} (hr : 0 < r) {winner : ClockSlot n}
    (hw : winner ∈ z.liveSlots) :
    ((Measure.pi (fun c : RelevantCoordinate z =>
      expMeasure (clockSlotRate (n := n) r c.val))).restrict (populationRelevantWinner z hw)).map
        (populationNextRelevantView hz hw) =
      ENNReal.ofReal (clockSlotRate r winner /
        ((z.active.card : ℝ) * (1 + r * z.susceptible.card))) •
        ((expMeasure ((z.active.card : ℝ) * (1 + r * z.susceptible.card))).prod
          (Measure.pi (fun c : RelevantCoordinate (populationStep z winner) =>
            expMeasure (clockSlotRate (n := n) r c.val)))) := by
  unfold populationRelevantWinner populationNextRelevantView
  rw [← Measure.map_map (measurable_populationNextClockView hz hw) (measurable_splitRelevantClocks z),
    ← Measure.restrict_map (measurable_splitRelevantClocks z)
      ((measurableSet_clockWins (⟨winner, hw⟩ : LiveCoordinate z)).prod MeasurableSet.univ),
    split_relevant_clock_product hz hr]
  exact population_winner_next_clock_law hz hr hw

theorem population_relevant_winner_residual_law {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {r : ℝ} (hr : 0 < r) {winner : ClockSlot n}
    (hw : winner ∈ z.liveSlots) :
    ((Measure.pi (fun c : RelevantCoordinate z =>
      expMeasure (clockSlotRate (n := n) r c.val))).restrict (populationRelevantWinner z hw)).map
        (fun x => (populationNextRelevantView hz hw x).2) =
      ENNReal.ofReal (clockSlotRate r winner /
        ((z.active.card : ℝ) * (1 + r * z.susceptible.card))) •
          Measure.pi (fun c : RelevantCoordinate (populationStep z winner) =>
            expMeasure (clockSlotRate (n := n) r c.val)) := by
  have ha : z.active.Nonempty := ⟨winner.1, (Finset.mem_product.mp hw).1⟩
  have hR := sum_clockSlotRate_live_pos hr z ha
  rw [sum_clockSlotRate_live] at hR
  have : IsProbabilityMeasure (expMeasure
      ((z.active.card : ℝ) * (1 + r * z.susceptible.card))) := isProbabilityMeasure_expMeasure hR
  have : ∀ c : RelevantCoordinate (populationStep z winner),
      IsProbabilityMeasure (expMeasure (clockSlotRate (n := n) r c.val)) :=
    fun c => isProbabilityMeasure_expMeasure (clockSlotRate_pos hr c.val)
  change Measure.map (Prod.snd ∘ populationNextRelevantView hz hw) _ = _
  rw [← Measure.map_map measurable_snd (measurable_populationNextRelevantView hz hw),
    population_relevant_winner_next_clock_law hz hr hw,
    Measure.map_smul _ measurable_snd.aemeasurable, Measure.map_snd_prod,
    measure_univ, one_smul]

end Freezing1.SIR
