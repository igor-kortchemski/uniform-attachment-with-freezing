module

public import Freezing1.SIRClockPopulation
public import Freezing1.SIRTreeLaw
public import Freezing1.CanonicalUniformSampling

/-!
# Uniform labelled infectives are uniform active genealogical vertices

The valid population stores an injective map from infected labels to the
actual chronological plane-tree addresses. Uniform source choice therefore
has exactly the actor distribution used by the existing tree kernel.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem PopulationState.Valid.uniform_active_address {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) :
    (Measure.uniformOfFinset z.active).map z.address = Measure.uniformOfFinset z.tree.active := by
  rw [← hz.active_eq]
  apply map_uniformOfFinset_of_injOn z.active z.address (measurable_of_countable _)
  intro v hv w hw he
  exact hz.address_injective (hz.active_infected hv) (hz.active_infected hw) he

theorem signedTreeLaw_population_actor {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) (ha : z.active.Nonempty) (sign : Bool) :
    signedTreeLaw z.project sign = (Measure.uniformOfFinset z.active).map
      (fun v => treeStep z.project sign (z.address v)) := by
  have ht : z.project.tree.active.Nonempty := by
    obtain ⟨v, hv⟩ := ha
    exact ⟨z.address v, hz.address_active hv⟩
  rw [signedTreeLaw, ite_eq_left ht]
  change (Measure.uniformOfFinset z.tree.active).map (treeStep z.project sign) = _
  rw [← hz.uniform_active_address,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

theorem signedTreeLaw_population_sum {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) (ha : z.active.Nonempty) (sign : Bool) :
    signedTreeLaw z.project sign =
      ∑ v ∈ z.active, (z.active.card : ℝ≥0∞)⁻¹ •
        Measure.dirac (treeStep z.project sign (z.address v)) := by
  rw [signedTreeLaw_population_actor hz ha sign, Measure.uniformOfFinset,
    Measure.map_finset_sum (measurable_of_countable _).aemeasurable]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Measure.map_smul _ (measurable_of_countable _).aemeasurable,
    Measure.map_dirac' (measurable_of_countable _)]

end Freezing1.SIR
