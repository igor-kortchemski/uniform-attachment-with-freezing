module

public import Freezing1.SIRPoissonFirstArrival
public import Freezing1.SIRPreassignedClocks
public import Mathlib.Probability.Independence.Basic

/-!
# Independent Poisson contact paths give the actual preassigned clock array

The input coordinates are entire contact arrival paths and recovery periods.
Their independence and Poisson counting marginals give the exact joint law
of all first-contact and recovery delays used by the static epidemic.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

def ClockDatum {n : ℕ} (c : ClockSlot n) : Type :=
  match c.2 with
  | none => ℝ
  | some _ => PoissonContact.ArrivalPath

instance clockDatum_measurableSpace {n : ℕ} (c : ClockSlot n) : MeasurableSpace (ClockDatum c) := by
  rcases c with ⟨v, w⟩
  cases w <;> simp only [ClockDatum] <;> infer_instance

def firstClockDelay {n : ℕ} (c : ClockSlot n) : ClockDatum c → ℝ :=
  match c with
  | (_, none) => id
  | (_, some _) => PoissonContact.first

theorem measurable_firstClockDelay {n : ℕ} (c : ClockSlot n) : Measurable (firstClockDelay c) := by
  rcases c with ⟨v, w⟩
  cases w
  · exact measurable_id
  · exact PoissonContact.measurable_first

abbrev PoissonClockData (n : ℕ) := (c : ClockSlot n) → ClockDatum c

def firstArrivalArray {n : ℕ} (data : PoissonClockData n) : ClockArray n :=
  fun c => firstClockDelay c (data c)

theorem measurable_firstArrivalArray (n : ℕ) : Measurable (@firstArrivalArray n) :=
  Measurable.of_eval fun c => (measurable_firstClockDelay c).comp (measurable_pi_apply c)

/-- Recovery lifetimes have the source's exponential rate one. Directed
contact coordinates are entire actual arrival paths with Poisson count
marginals. Their exponential first-delay laws are proved inside this theorem. -/
theorem independent_firstArrivalArray_law {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (n : ℕ) (r : ℝ≥0) (hr : 0 < r)
    (X : (c : ClockSlot n) → Ω → ClockDatum c)
    (hX : ∀ c, Measurable (X c)) (hindep : iIndepFun X mu)
    (hrecovery : ∀ v : Individual n, mu.map (X (v, none)) = expMeasure 1)
    (hcontact : ∀ v w : Individual n,
      PoissonContact.HasPoissonCounts (mu.map (X (v, some w))) r) :
    mu.map (fun omega => firstArrivalArray (fun c => X c omega)) = preassignedClockLaw (r : ℝ) n := by
  have hsingle : ∀ c : ClockSlot n,
      mu.map (firstClockDelay c ∘ X c) = expMeasure (clockSlotRate (r : ℝ) c) := by
    rintro ⟨v, w⟩
    cases w with
    | none =>
      change mu.map (id ∘ X (v, none)) = expMeasure 1
      simpa only [Function.id_comp] using hrecovery v
    | some w =>
      change mu.map (PoissonContact.first ∘ X (v, some w)) = expMeasure (r : ℝ)
      rw [← Measure.map_map PoissonContact.measurable_first (hX (v, some w))]
      exact PoissonContact.first_law _ r hr (hcontact v w)
  have hdelay := hindep.comp firstClockDelay measurable_firstClockDelay
  have hmap := iIndepFun.map_fun_eq_pi_map
    (fun c => ((measurable_firstClockDelay c).comp (hX c)).aemeasurable) hdelay
  change mu.map (fun omega c => firstClockDelay c (X c omega)) =
    Measure.pi (fun c => expMeasure (clockSlotRate (r : ℝ) c))
  calc
    _ = Measure.pi (fun c => mu.map (firstClockDelay c ∘ X c)) := hmap
    _ = _ := by
      congr 1
      funext c
      exact hsingle c

end Freezing1.SIR
