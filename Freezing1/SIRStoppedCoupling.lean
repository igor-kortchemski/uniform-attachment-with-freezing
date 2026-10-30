module

public import Freezing1.SIRCountLaw
public import Freezing1.SIRSusceptibleLaw
public import Freezing1.PlaneGraftHistory

/-!
# A genuine coupling of stopped and unstopped SIR populations

One fresh sign updates both populations until extinction. Afterwards the
stopped population holds and the auxiliary susceptible chain continues.
Both complete marginal path laws are proved to be the previously constructed
Markov laws. In particular, agreement before extinction is a conclusion of
the construction, rather than an additional coupling hypothesis.
-/

@[expose] public section

namespace Freezing1.SIR.StoppedCoupling

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

abbrev State := Counts × ℕ

def initial (n : ℕ) : State := (initialCounts n, n)

def step (z : State) (sign : Bool) : State :=
  (countsStep z.1 sign, if sign then z.2 - 1 else z.2)

def Compatible (z : State) : Prop := 0 < z.1.infectious → z.1.susceptible = z.2

theorem compatible_initial (n : ℕ) : Compatible (initial n) := by
  simp [Compatible, initial, initialCounts]

theorem compatible_step {z : State} (hz : Compatible z) (sign : Bool) :
    Compatible (step z sign) := by
  intro hi
  have hp : 0 < z.1.infectious := by
    by_contra hn
    have he : z.1.infectious = 0 := by omega
    simp [step, countsStep, he] at hi
  have hu := hz hp
  cases sign
  · simpa [step, countsStep, hp.ne', recoverCounts] using hu
  · by_cases hu0 : z.1.susceptible = 0
    · simp [step, countsStep, hp.ne', hu0, ← hu]
    · have hu0' : z.2 ≠ 0 := by omega
      simp [step, countsStep, hp.ne', hu0', infectCounts, hu]

noncomputable def transition (rate : ℝ≥0) : Kernel State State where
  toFun z := (bernoulliMeasure true false (infectionProbability rate z.2)).map (step z)
  measurable' := measurable_of_countable _

instance transition_markov (rate : ℝ≥0) : IsMarkovKernel (transition rate) := by
  constructor
  intro z
  change IsProbabilityMeasure ((bernoulliMeasure true false
    (infectionProbability rate z.2)).map (step z))
  infer_instance

theorem transition_support (rate : ℝ≥0) (z : State) :
    ∀ᵐ w ∂transition rate z, ∃ sign, w = step z sign := by
  apply (ae_map_iff (measurable_of_countable _).aemeasurable
    (Set.to_countable _).measurableSet).mpr
  exact Filter.Eventually.of_forall fun sign => ⟨sign, rfl⟩

theorem transition_counts (rate : ℝ≥0) {z : State} (hz : Compatible z) :
    (transition rate z).map Prod.fst = countsKernel rate z.1 := by
  change ((bernoulliMeasure true false (infectionProbability rate z.2)).map
    (step z)).map Prod.fst = _
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  by_cases hi : z.1.infectious = 0
  · rw [countsKernel_absorbed rate hi]
    have he : Prod.fst ∘ step z = fun _ => z.1 := by
      funext sign
      exact countsStep_of_absorbed hi sign
    rw [he, Measure.map_const]
    simp
  · have he := hz (by omega)
    rw [← he]
    rfl

theorem transition_unstopped (rate : ℝ≥0) (z : State) :
    (transition rate z).map Prod.snd = Susceptible.transition rate z.2 := by
  change ((bernoulliMeasure true false (infectionProbability rate z.2)).map
    (step z)).map Prod.snd = _
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    map_bernoulliMeasure]
  rfl

noncomputable def fullLaw (rate : ℝ≥0) (n : ℕ) : Measure (ℕ → State) :=
  CountableMarkovChain.fullLaw (transition rate) (initial n)

instance fullLaw_probability (rate : ℝ≥0) (n : ℕ) : IsProbabilityMeasure (fullLaw rate n) := by
  unfold fullLaw
  infer_instance

theorem fullLaw_initial (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂fullLaw rate n, H 0 = initial n :=
  CountableMarkovChain.fullLaw_initial (transition rate) (initial n)

theorem fullLaw_steps (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂fullLaw rate n, ∀ k, ∃ sign, H (k + 1) = step (H k) sign :=
  CountableMarkovChain.fullLaw_steps (transition rate) (initial n) _
    (transition_support rate)

theorem fullLaw_compatible (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂fullLaw rate n, ∀ k, Compatible (H k) := by
  filter_upwards [fullLaw_initial rate n, fullLaw_steps rate n] with H h0 hs
  intro k
  induction k with
  | zero => rw [h0]; exact compatible_initial n
  | succ k ih =>
    obtain ⟨sign, he⟩ := hs k
    rw [he]
    exact compatible_step ih sign

theorem map_fullLaw_counts (rate : ℝ≥0) (n : ℕ) :
    (fullLaw rate n).map (fun H k => (H k).1) = countsFullLaw rate n := by
  change (CountableMarkovChain.fullLaw (transition rate) (initial n)).map
    (fun H k => Prod.fst (H k)) = _
  apply CountableMarkovChain.map_fullLaw_of_ae_intertwining
  intro k
  filter_upwards [fullLaw_compatible rate n] with H hH
  exact transition_counts rate (hH k)

theorem map_fullLaw_unstopped (rate : ℝ≥0) (n : ℕ) :
    (fullLaw rate n).map (fun H k => (H k).2) = Susceptible.fullLaw rate n := by
  change (CountableMarkovChain.fullLaw (transition rate) (initial n)).map
    (fun H k => Prod.snd (H k)) = _
  apply CountableMarkovChain.map_fullLaw_of_ae_intertwining
  exact fun _ => Filter.Eventually.of_forall fun H => transition_unstopped rate _

theorem fullLaw_counts_legal (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂fullLaw rate n, ∀ k, (H k).1.LegalNext (H (k + 1)).1 := by
  have hh := countsFullLaw_legal rate n
  rw [← map_fullLaw_counts rate n] at hh
  have hm : Measurable (fun H : ℕ → State => fun k => (H k).1) :=
    measurable_pi_iff.mpr fun k => measurable_fst.comp (measurable_pi_apply k)
  exact ae_of_ae_map hm.aemeasurable hh

theorem step_susceptible {z : State} (hi : 0 < z.1.infectious)
    (hu : z.1.susceptible = z.2) (sign : Bool) :
    (step z sign).1.susceptible = (step z sign).2 := by
  cases sign
  · simpa [step, countsStep, hi.ne', recoverCounts] using hu
  · by_cases hu0 : z.1.susceptible = 0
    · simp [step, countsStep, hi.ne', hu0, ← hu]
    · have hu0' : z.2 ≠ 0 := by omega
      simp [step, countsStep, hi.ne', hu0', infectCounts, hu]

/-- Agreement includes the first extinct state, not only strictly earlier
times. The auxiliary integer count can subsequently become negative. -/
theorem fullLaw_agree_until_extinction (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂fullLaw rate n, ∀ k,
      (∀ j < k, 0 < (H j).1.infectious) →
        (H k).1.susceptible = (H k).2 ∧
          ((H k).1.infectious : ℤ) = Susceptible.infectious n k (fun j => (H j).2) := by
  filter_upwards [fullLaw_initial rate n, fullLaw_steps rate n,
    fullLaw_counts_legal rate n] with H h0 hs hl
  have hu : ∀ k, (∀ j < k, 0 < (H j).1.infectious) →
      (H k).1.susceptible = (H k).2 := by
    intro k
    induction k with
    | zero => simp [h0, initial, initialCounts]
    | succ k ih =>
      intro hp
      have hk := hp k (by omega)
      have he := ih (fun j hj => hp j (by omega))
      obtain ⟨sign, hh⟩ := hs k
      rw [hh]
      exact step_susceptible hk he sign
  have hid : ∀ k, (∀ j < k, 0 < (H j).1.infectious) →
      (H k).1.infectious + 2 * (H k).1.susceptible + k = 2 * n + 1 := by
    intro k
    induction k with
    | zero => simp [h0, initial, initialCounts, Nat.add_comm]
    | succ k ih =>
      intro hp
      have hk := hp k (by omega)
      have he := ih (fun j hj => hp j (by omega))
      have hs' := (hl k).potential_succ hk
      simp only [Counts.potential] at hs'
      omega
  intro k hp
  refine ⟨hu k hp, ?_⟩
  have he := hid k hp
  have he' : ((H k).1.infectious : ℤ) + 2 * (H k).1.susceptible + k = 2 * (n : ℤ) + 1 := by
    exact_mod_cast he
  simp only [Susceptible.infectious]
  rw [← hu k hp]
  omega

end Freezing1.SIR.StoppedCoupling
