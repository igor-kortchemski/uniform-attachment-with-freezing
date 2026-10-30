module

public import Freezing1.SIRPreassignedClocks
public import Mathlib.Probability.Independence.Basic

/-!
# Residual views of the static preassigned epidemic arrays

At an event, surviving old live clocks lose the elapsed time. Previously
unused outgoing arrays retain their original delays, including the newly
activated infective's array. These are deterministic identities for the
single static array used by `preassignedRun`.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open scoped Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def agedClockView {n : ℕ} (z : PopulationState n) (elapsed : ℝ)
    (x : ClockArray n) (c : ClockSlot n) : ℝ :=
  if c ∈ z.liveSlots then x c - elapsed else x c

theorem relevantClockView_initial (n : ℕ) (omega : ClockArray n) :
    relevantClockView (initialClockFrame n) omega = omega := by
  funext c
  simp [relevantClockView, remainingClock, initialClockFrame,
    ClockFrame.population, ClockFrame.time, ClockFrame.birthTime]

theorem availableTargets_infect_subset {n : ℕ} (z : PopulationState n)
    (v w : Individual n) :
    (infectPopulation z v w).availableTargets ⊆ z.availableTargets := by
  intro q hq
  rcases Finset.mem_insert.mp hq with rfl | hq
  · exact Finset.mem_insert_self _ _
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_of_mem_erase hb))

theorem relevantClockView_advance_recovery {n : ℕ} {F : ClockFrame n}
    (hf : F.population.Valid) (omega : ClockArray n) {v : Individual n}
    (hv : v ∈ F.population.active) {c : ClockSlot n}
    (hc : c ∈ (recoverPopulation F.population v).relevantSlots) :
    relevantClockView (advanceClockFrame F omega (v, none)) omega c =
      agedClockView F.population (remainingClock F omega (v, none))
        (relevantClockView F omega) c := by
  rcases F with ⟨z, time, births⟩
  rcases c with ⟨a, q⟩
  have hlegal : (v, none) ∈ z.liveSlots := (recovery_mem_liveSlots z v).mpr hv
  by_cases ha : a ∈ z.active
  · have hLnew : (a, q) ∈ (recoverPopulation z v).liveSlots := by
      rcases Finset.mem_union.mp hc with hL | hU
      · exact hL
      · have hS := (mem_unusedSlots (recoverPopulation z v) (a, q)).mp hU
        exact (Finset.disjoint_left.mp hf.disjoint hS ha).elim
    have haNew : a ∈ z.active.erase v := (Finset.mem_product.mp hLnew).1
    have hLold : (a, q) ∈ z.liveSlots :=
      Finset.mem_product.mpr ⟨ha, (Finset.mem_product.mp hLnew).2⟩
    simp [agedClockView, relevantClockView, remainingClock, advanceClockFrame,
      populationStep, ClockFrame.population, ClockFrame.time, ClockFrame.birthTime,
      recoverPopulation, hlegal, ha, haNew, hLold]
    ring
  · have haNew : a ∉ z.active.erase v := fun h => ha (Finset.mem_of_mem_erase h)
    have hLold : (a, q) ∉ z.liveSlots := fun h => ha (Finset.mem_product.mp h).1
    simp [agedClockView, relevantClockView, remainingClock, advanceClockFrame,
      populationStep, ClockFrame.population, ClockFrame.time, ClockFrame.birthTime,
      recoverPopulation, hlegal, ha, haNew, hLold]

theorem relevantClockView_advance_infection {n : ℕ} {F : ClockFrame n}
    (hf : F.population.Valid) (omega : ClockArray n) {v w : Individual n}
    (hv : v ∈ F.population.active) (hw : w ∈ F.population.susceptible) {c : ClockSlot n}
    (hc : c ∈ (infectPopulation F.population v w).relevantSlots) :
    relevantClockView (advanceClockFrame F omega (v, some w)) omega c =
      agedClockView F.population (remainingClock F omega (v, some w))
        (relevantClockView F omega) c := by
  rcases F with ⟨z, time, births⟩
  rcases c with ⟨a, q⟩
  have hlegal : (v, some w) ∈ z.liveSlots := (contact_mem_liveSlots z v w).mpr ⟨hv, hw⟩
  by_cases haw : a = w
  · subst a
    have ha : w ∉ z.active := fun h => Finset.disjoint_left.mp hf.disjoint hw h
    have hLold : (w, q) ∉ z.liveSlots := fun h => ha (Finset.mem_product.mp h).1
    simp [agedClockView, relevantClockView, remainingClock, advanceClockFrame,
      populationStep, ClockFrame.population, ClockFrame.time, ClockFrame.birthTime,
      infectPopulation, hlegal, ha, hLold]
  · by_cases ha : a ∈ z.active
    · have hLnew : (a, q) ∈ (infectPopulation z v w).liveSlots := by
        rcases Finset.mem_union.mp hc with hL | hU
        · exact hL
        · have hS := (mem_unusedSlots (infectPopulation z v w) (a, q)).mp hU
          exact (Finset.disjoint_left.mp hf.disjoint (Finset.mem_of_mem_erase hS) ha).elim
      have hLold : (a, q) ∈ z.liveSlots := Finset.mem_product.mpr
        ⟨ha, availableTargets_infect_subset z v w (Finset.mem_product.mp hLnew).2⟩
      simp [agedClockView, relevantClockView, remainingClock, advanceClockFrame,
        populationStep, ClockFrame.population, ClockFrame.time, ClockFrame.birthTime,
        infectPopulation, hlegal, ha, hLold, haw]
      ring
    · have hLold : (a, q) ∉ z.liveSlots := fun h => ha (Finset.mem_product.mp h).1
      simp [agedClockView, relevantClockView, remainingClock, advanceClockFrame,
        populationStep, ClockFrame.population, ClockFrame.time, ClockFrame.birthTime,
        infectPopulation, hlegal, ha, hLold, haw]

theorem relevantClockView_advance {n : ℕ} {F : ClockFrame n}
    (hf : F.population.Valid) (omega : ClockArray n) {winner c : ClockSlot n}
    (hw : winner ∈ F.population.liveSlots)
    (hc : c ∈ (advanceClockFrame F omega winner).population.relevantSlots) :
    relevantClockView (advanceClockFrame F omega winner) omega c =
      agedClockView F.population (remainingClock F omega winner)
        (relevantClockView F omega) c := by
  rcases winner with ⟨v, _ | w⟩
  · have hv := (recovery_mem_liveSlots F.population v).mp hw
    apply relevantClockView_advance_recovery hf omega hv
    simpa only [advanceClockFrame_population, populationStep, ite_eq_left hw] using hc
  · obtain ⟨hv, hws⟩ := (contact_mem_liveSlots F.population v w).mp hw
    apply relevantClockView_advance_infection hf omega hv hws
    simpa only [advanceClockFrame_population, populationStep, ite_eq_left hw] using hc

/-- An injective projection of the actual independent clock product retains
the corresponding independent exponential law. -/
theorem independent_clock_coordinate_projection {ι κ : Type*} [Fintype ι] [Fintype κ]
    (rate : ι → ℝ) (hr : ∀ j, 0 < rate j) (pick : κ → ι)
    (hpick : Function.Injective pick) :
    (Measure.pi (fun j => expMeasure (rate j))).map
      (fun t : ι → ℝ => fun k => t (pick k)) =
        Measure.pi (fun k => expMeasure (rate (pick k))) := by
  have : ∀ j, IsProbabilityMeasure (expMeasure (rate j)) :=
    fun j => isProbabilityMeasure_expMeasure (hr j)
  have hi : iIndepFun (fun j (t : ι → ℝ) => t j)
      (Measure.pi (fun j => expMeasure (rate j))) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hs := iIndepFun.precomp hpick hi
  rw [iIndepFun.map_fun_eq_pi_map
    (fun k => (measurable_pi_apply (pick k)).aemeasurable) hs]
  congr 1
  funext k
  exact (measurePreserving_eval (fun j => expMeasure (rate j)) (pick k)).map_eq

theorem preassigned_initial_relevant_law {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (preassignedClockLaw r n).map (fun omega : ClockArray n =>
      fun c : {c // c ∈ (initialPopulation n).relevantSlots} =>
        relevantClockView (initialClockFrame n) omega c) =
      Measure.pi (fun c : {c // c ∈ (initialPopulation n).relevantSlots} =>
        expMeasure (clockSlotRate (n := n) r c.val)) := by
  simp only [relevantClockView_initial, preassignedClockLaw]
  exact independent_clock_coordinate_projection (clockSlotRate (n := n) r) (clockSlotRate_pos hr)
    Subtype.val Subtype.val_injective

end Freezing1.SIR
