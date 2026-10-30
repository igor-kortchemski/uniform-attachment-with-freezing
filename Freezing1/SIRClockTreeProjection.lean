module

public import Freezing1.SIRClockWordKernel
public import Freezing1.SIRTreeLaw
public import Freezing1.SIRPopulationUniformActor
public import Freezing1.SIRAbsorption

/-!
# Forgetting individual labels in a genuine clock race

Each live recovery slot has weight one and each live directed infection
slot has weight `r`. Summing over susceptible recipients leaves a uniform
infectious actor and the source infection/recovery probability.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Classical BigOperators

set_option backward.isDefEq.respectTransparency false

theorem clockChoiceLaw_eq_sum {n : ℕ} {r : ℝ} (hr : 0 < r)
    {z : PopulationState n} (hz : z.Valid) :
    clockChoiceLaw r z = ∑ c : ClockChoice n, clockChoiceWeight r z c • Measure.dirac c := by
  have hh := (Measure.ae_mem_finset_iff (μ := clockChoiceLaw r z) (s := Finset.univ)).mp
    (Filter.Eventually.of_forall fun c => Finset.mem_univ c)
  simpa only [clockChoiceLaw_singleton hr hz] using hh

theorem clockChoiceLaw_project_eq_sum {n : ℕ} {r : ℝ} (hr : 0 < r)
    {z : PopulationState n} (hz : z.Valid) :
    (clockChoiceLaw r z).map (fun c => (optionPopulationStep z c).project) =
      ∑ c : ClockChoice n, clockChoiceWeight r z c •
        Measure.dirac (optionPopulationStep z c).project := by
  rw [clockChoiceLaw_eq_sum hr hz, Measure.map_finset_sum' (measurable_of_countable _).aemeasurable]
  apply Finset.sum_congr rfl
  intro c _
  rw [Measure.map_smul _ (measurable_of_countable _).aemeasurable,
    Measure.map_dirac' (measurable_of_countable _)]

theorem clockChoiceLaw_project_live_sum {n : ℕ} {r : ℝ} (hr : 0 < r)
    {z : PopulationState n} (hz : z.Valid) (ha : z.active ≠ ∅) :
    (clockChoiceLaw r z).map (fun c => (optionPopulationStep z c).project) =
      ∑ c ∈ z.liveSlots, ENNReal.ofReal
        (clockSlotRate r c / ((z.active.card : ℝ) * (1 + r * z.susceptible.card))) •
          Measure.dirac (treeStep z.project c.2.isSome (z.address c.1)) := by
  rw [clockChoiceLaw_project_eq_sum hr hz, Fintype.sum_option]
  simp only [clockChoiceWeight, ite_eq_right ha, zero_smul, zero_add]
  calc
    _ = ∑ c ∈ z.liveSlots, ENNReal.ofReal
        (clockSlotRate r c / ((z.active.card : ℝ) * (1 + r * z.susceptible.card))) •
          Measure.dirac (populationStep z c).project := by
      simp only [optionPopulationStep, Option.elim_some]
      simp only [ite_smul, zero_smul]
      rw [← Finset.sum_filter]
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [hz.step_project hc]

theorem clockChoiceLaw_project_actor_sum {n : ℕ} {r : ℝ} (hr : 0 < r)
    {z : PopulationState n} (hz : z.Valid) (ha : z.active ≠ ∅) :
    (clockChoiceLaw r z).map (fun c => (optionPopulationStep z c).project) =
      ∑ v ∈ z.active,
        (ENNReal.ofReal (1 / ((z.active.card : ℝ) * (1 + r * z.susceptible.card))) •
          Measure.dirac (treeStep z.project false (z.address v)) +
        ((z.susceptible.card : ℝ≥0∞) *
          ENNReal.ofReal (r / ((z.active.card : ℝ) * (1 + r * z.susceptible.card)))) •
          Measure.dirac (treeStep z.project true (z.address v))) := by
  rw [clockChoiceLaw_project_live_sum hr hz ha, PopulationState.liveSlots, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro v hv
  rw [PopulationState.availableTargets, Finset.sum_insert (by simp)]
  rw [Finset.sum_image (by intro a _ b _ h; exact Option.some.inj h)]
  simp only [clockSlotRate, Option.elim_none, Option.elim_some, Option.isSome_none,
    Option.isSome_some]
  rw [← Finset.sum_smul, Finset.sum_const, nsmul_eq_mul]

theorem treeKernel_signed_split (rate : ℝ≥0) (z : TreeState) :
    treeKernel rate z = unitInterval.toNNReal (infectionProbability rate z.susceptible) •
        signedTreeLaw z true +
      unitInterval.toNNReal (unitInterval.symm (infectionProbability rate z.susceptible)) •
        signedTreeLaw z false := by
  ext A hA
  rw [treeKernel_apply, bernoulliMeasure_def]
  simp only [lintegral_add_measure, lintegral_smul_measure, lintegral_dirac,
    Measure.add_apply, Measure.smul_apply]

theorem clock_projection_coefficients {r : ℝ} (hr : 0 < r) {A U : ℕ} (hA : 0 < A) :
    let p := infectionProbability (⟨r, hr.le⟩ : ℝ≥0) U
    (unitInterval.toNNReal p) • ((A : ℝ≥0∞)⁻¹) =
      (U : ℝ≥0∞) * ENNReal.ofReal (r / ((A : ℝ) * (1 + r * U))) ∧
    (unitInterval.toNNReal (unitInterval.symm p)) • ((A : ℝ≥0∞)⁻¹) =
      ENNReal.ofReal (1 / ((A : ℝ) * (1 + r * U))) := by
  dsimp only
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hden : 0 < 1 + r * U := by positivity
  have hcoe (p : unitInterval) :
      ((unitInterval.toNNReal p : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (p : ℝ) := by
    exact (ENNReal.ofReal_coe_nnreal).symm
  constructor
  · change ((unitInterval.toNNReal _ : ℝ≥0) : ℝ≥0∞) * (A : ℝ≥0∞)⁻¹ = _
    rw [hcoe, show (A : ℝ≥0∞) = ENNReal.ofReal (A : ℝ) by simp,
      ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos hAR,
      show (U : ℝ≥0∞) = ENNReal.ofReal (U : ℝ) by simp,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg U)]
    congr 1
    change (r * U / (1 + r * U)) / A = (U : ℝ) * (r / ((A : ℝ) * (1 + r * U)))
    field_simp
  · change ((unitInterval.toNNReal _ : ℝ≥0) : ℝ≥0∞) * (A : ℝ≥0∞)⁻¹ = _
    rw [hcoe, unitInterval.coe_symm_eq, infectionProbability_complement,
      show (A : ℝ≥0∞) = ENNReal.ofReal (A : ℝ) by simp,
      ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos hAR]
    congr 1
    change (1 / (1 + r * U)) / A = 1 / ((A : ℝ) * (1 + r * U))
    field_simp

/-- The genuine labelled clock event has exactly the previously constructed
infection-tree kernel after individual labels are forgotten. -/
theorem clockChoiceLaw_project {n : ℕ} {r : ℝ} (hr : 0 < r)
    {z : PopulationState n} (hz : z.Valid) :
    (clockChoiceLaw r z).map (fun c => (optionPopulationStep z c).project) =
      treeKernel (⟨r, hr.le⟩ : ℝ≥0) z.project := by
  by_cases ha : z.active = ∅
  · have ht : z.project.tree.active = ∅ := by
      change z.tree.active = ∅
      rw [← hz.active_eq, ha]
      simp
    rw [treeKernel_absorbed _ ht, clockChoiceLaw_project_eq_sum hr hz, Fintype.sum_option]
    simp [clockChoiceWeight, ha, PopulationState.liveSlots, optionPopulationStep]
  · have hane : z.active.Nonempty := Finset.nonempty_iff_ne_empty.mpr ha
    have hcoeff := clock_projection_coefficients hr (U := z.susceptible.card) hane.card_pos
    have hinfect :
        unitInterval.toNNReal (infectionProbability (⟨r, hr.le⟩ : ℝ≥0) z.project.susceptible) •
          (z.active.card : ℝ≥0∞)⁻¹ =
        (z.susceptible.card : ℝ≥0∞) * ENNReal.ofReal
          (r / ((z.active.card : ℝ) * (1 + r * z.susceptible.card))) := hcoeff.1
    have hrecover :
        unitInterval.toNNReal (unitInterval.symm
          (infectionProbability (⟨r, hr.le⟩ : ℝ≥0) z.project.susceptible)) •
          (z.active.card : ℝ≥0∞)⁻¹ =
        ENNReal.ofReal (1 / ((z.active.card : ℝ) * (1 + r * z.susceptible.card))) := hcoeff.2
    rw [clockChoiceLaw_project_actor_sum hr hz ha, treeKernel_signed_split,
      signedTreeLaw_population_sum hz hane true, signedTreeLaw_population_sum hz hane false,
      Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    rw [← smul_assoc, ← smul_assoc, hinfect, hrecover]
    exact add_comm _ _

end Freezing1.SIR
