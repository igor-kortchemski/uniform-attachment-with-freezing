module

public import Freezing1.SIRPoissonFirstArrival
public import Freezing1.SIRClockEventWords

/-!
# Why later directed contacts cannot create an additional infection

Susceptibility never returns after it is lost. Recovery likewise removes
an individual permanently. On a chronological contact path, failure of the
first contact therefore implies failure of every later contact; acceptance
of the first contact removes the recipient from susceptibility.
-/

@[expose] public section

namespace Freezing1.SIR

open Set
open scoped Classical

set_option backward.isDefEq.respectTransparency false

theorem populationStep_susceptible_subset {n : ℕ} (z : PopulationState n) (c : ClockSlot n) :
    (populationStep z c).susceptible ⊆ z.susceptible := by
  unfold populationStep
  split_ifs with hc
  · rcases c with ⟨v, _ | w⟩
    · exact Finset.Subset.refl _
    · exact Finset.erase_subset _ _
  · exact Finset.Subset.refl _

theorem optionPopulationStep_susceptible_subset {n : ℕ} (z : PopulationState n)
    (c : ClockChoice n) : (optionPopulationStep z c).susceptible ⊆ z.susceptible := by
  cases c
  · exact Finset.Subset.refl _
  · exact populationStep_susceptible_subset _ _

theorem preassignedRun_susceptible_antitone (n : ℕ) (omega : ClockArray n) :
    Antitone (fun k => (preassignedRun n omega k).population.susceptible) := by
  apply antitone_nat_of_succ_le
  intro k
  rw [preassignedRun_population_replay n omega (k + 1), preassignedWord, replayPopulation,
    preassignedRun_population_replay n omega k]
  exact optionPopulationStep_susceptible_subset _ _

/-- If the source is active, processing its first contact either infects
the recipient immediately or finds that it was already nonsusceptible.
In both cases the recipient is nonsusceptible afterwards. -/
theorem contactStep_recipient_not_susceptible {n : ℕ} {z : PopulationState n}
    {v w : Individual n} (hv : v ∈ z.active) :
    w ∉ (populationStep z (v, some w)).susceptible := by
  by_cases hw : w ∈ z.susceptible
  · have hc := (contact_mem_liveSlots z v w).mpr ⟨hv, hw⟩
    simp [populationStep, hc, infectPopulation]
  · have hc : (v, some w) ∉ z.liveSlots := by
      intro hh
      exact hw ((contact_mem_liveSlots z v w).mp hh).2
    simpa only [populationStep, ite_eq_right hc] using hw

def PopulationState.Removed {n : ℕ} (z : PopulationState n) (v : Individual n) : Prop :=
  v ∉ z.susceptible ∧ v ∉ z.active

theorem PopulationState.Removed.step {n : ℕ} {z : PopulationState n} {v : Individual n}
    (hv : z.Removed v) (c : ClockSlot n) : (populationStep z c).Removed v := by
  refine ⟨fun h => hv.1 (populationStep_susceptible_subset z c h), ?_⟩
  unfold populationStep
  split_ifs with hc
  · rcases c with ⟨u, _ | w⟩
    · exact fun h => hv.2 (Finset.mem_of_mem_erase h)
    · intro h
      rcases Finset.mem_insert.mp h with he | he
      · have hw := ((contact_mem_liveSlots z u w).mp hc).2
        exact hv.1 (he ▸ hw)
      · exact hv.2 he
  · exact hv.2

theorem recoverPopulation_source_removed {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {v : Individual n} (hv : v ∈ z.active) :
    (recoverPopulation z v).Removed v := by
  refine ⟨?_, by simp [recoverPopulation]⟩
  exact fun h => Finset.disjoint_left.mp hz.disjoint h hv

namespace PoissonContact

/-- The two conditions for a contact at infection age `t` to be effective:
the source has not recovered and the recipient is still susceptible. -/
def EffectiveContact (susceptible : ℝ → Prop) (recovery t : ℝ) : Prop :=
  t < recovery ∧ susceptible t

theorem effectiveContact_at_earlier {susceptible : ℝ → Prop}
    (hs : ∀ s t : ℝ, s ≤ t → susceptible t → susceptible s)
    {recovery s t : ℝ} (hst : s ≤ t) :
    EffectiveContact susceptible recovery t → EffectiveContact susceptible recovery s := by
  rintro ⟨hr, ht⟩
  exact ⟨hst.trans_lt hr, hs s t hst ht⟩

/-- If the first directed contact is ineffective, every later point of
that same actual contact process is ineffective as well. This includes
recovery before the first point. -/
theorem later_contacts_ineffective_of_first (a : ArrivalPath)
    {susceptible : ℝ → Prop} (hs : ∀ s t : ℝ, s ≤ t → susceptible t → susceptible s)
    {recovery : ℝ} (hfirst : ¬EffectiveContact susceptible recovery (first a)) :
    ∀ j : ℕ, ¬EffectiveContact susceptible recovery (a.1 j) := by
  intro j hj
  exact hfirst (effectiveContact_at_earlier hs (a.2.2.1.monotone (Nat.zero_le j)) hj)

theorem no_contacts_before_first (a : ArrivalPath) {t : ℝ} (ht : t < first a) : count a t = 0 :=
  (count_eq_zero_iff a t).mpr ht

end PoissonContact

end Freezing1.SIR
