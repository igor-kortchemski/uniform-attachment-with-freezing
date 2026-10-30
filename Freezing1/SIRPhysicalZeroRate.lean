module

public import Freezing1.SIROptionalContactProtocol
public import Freezing1.SIRZeroRateLaw

/-!
# The physical zero-contact-intensity epidemic

Zero Poisson counting marginals force every directed path to be empty.
The actual next-point protocol therefore recovers its sole root and holds.
Its entire tree and count path laws are the zero-rate embedded laws.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

noncomputable def optionalContactTreePath (n : ℕ) (recovery : Individual n → ℝ)
    (contacts : OptionalContactData n) : ℕ → TreeState :=
  fun k => (optionalContactRun n recovery contacts k).population.project

theorem optionalContactTreePath_of_empty_contacts (n : ℕ) (recovery : Individual n → ℝ)
    (contacts : OptionalContactData n)
    (he : ∀ v w, contacts v w = PoissonContact.emptyPath) :
    optionalContactTreePath n recovery contacts = zeroRateTreePath n := by
  funext k
  cases k with
  | zero => exact project_initialPopulation n
  | succ k =>
    change (optionalContactRun n recovery contacts (k + 1)).population.project = _
    rw [optionalContactRun_succ_of_empty_contacts n recovery contacts he k]
    change (recoverPopulation (initialPopulation n) 0).project = frozenRootState n
    rw [recoverPopulation_project, project_initialPopulation]
    rfl

variable {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]

theorem zero_contacts_empty_ae (n : ℕ)
    (contacts : Individual n → Individual n → Ω → PoissonContact.OptionalPath)
    (hC : ∀ v w, Measurable (contacts v w))
    (hcounts : ∀ v w, PoissonContact.HasOptionalPoissonCounts (mu.map (contacts v w)) 0) :
    ∀ᵐ omega ∂mu, ∀ v w, contacts v w omega = PoissonContact.emptyPath := by
  apply ae_all_iff.mpr
  intro v
  apply ae_all_iff.mpr
  intro w
  have : IsProbabilityMeasure (mu.map (contacts v w)) :=
    Measure.isProbabilityMeasure_map_iff (hC v w).aemeasurable |>.mpr inferInstance
  exact ae_of_ae_map (hC v w).aemeasurable (hcounts v w).empty_ae

/-- No independence or waiting-time premise is needed at zero contact rate:
the contact counting marginals already force the whole discrete history. -/
theorem zeroRate_physical_tree_fullLaw (n : ℕ)
    (recovery : Individual n → Ω → ℝ)
    (contacts : Individual n → Individual n → Ω → PoissonContact.OptionalPath)
    (hC : ∀ v w, Measurable (contacts v w))
    (hcounts : ∀ v w, PoissonContact.HasOptionalPoissonCounts (mu.map (contacts v w)) 0) :
    mu.map (fun omega => optionalContactTreePath n (fun v => recovery v omega)
      (fun v w => contacts v w omega)) = treeFullLaw 0 n := by
  rw [treeFullLaw_zero_eq_dirac]
  calc
    _ = mu.map (fun _ => zeroRateTreePath n) := by
      apply Measure.map_congr
      filter_upwards [zero_contacts_empty_ae mu n contacts hC hcounts] with omega hzero
      exact optionalContactTreePath_of_empty_contacts n _ _ hzero
    _ = _ := by simp

theorem zeroRate_physical_counts_fullLaw (n : ℕ)
    (recovery : Individual n → Ω → ℝ)
    (contacts : Individual n → Individual n → Ω → PoissonContact.OptionalPath)
    (hC : ∀ v w, Measurable (contacts v w))
    (hcounts : ∀ v w, PoissonContact.HasOptionalPoissonCounts (mu.map (contacts v w)) 0) :
    mu.map (fun omega k =>
      (optionalContactTreePath n (fun v => recovery v omega) (fun v w => contacts v w omega) k).counts) =
        countsFullLaw 0 n := by
  have hm : AEMeasurable (fun omega => optionalContactTreePath n (fun v => recovery v omega)
      (fun v w => contacts v w omega)) mu := by
    apply aemeasurable_const.congr
    filter_upwards [zero_contacts_empty_ae mu n contacts hC hcounts] with omega hzero
    exact (optionalContactTreePath_of_empty_contacts n _ _ hzero).symm
  have hc : Measurable (fun H : ℕ → TreeState => fun k => (H k).counts) :=
    Measurable.of_eval fun k => (measurable_of_countable TreeState.counts).comp (measurable_pi_apply k)
  rw [← map_treeFullLaw_counts 0 n, ← zeroRate_physical_tree_fullLaw mu n recovery contacts hC hcounts,
    AEMeasurable.map_map_of_aemeasurable hc.aemeasurable hm]
  rfl

/-- The sole recovery occurs at its actual positive exponential lifetime;
all later event states are the same absorbed frame. -/
theorem zeroRate_physical_absorption (n : ℕ)
    (recovery : Individual n → Ω → ℝ)
    (contacts : Individual n → Individual n → Ω → PoissonContact.OptionalPath)
    (hC : ∀ v w, Measurable (contacts v w))
    (hcounts : ∀ v w, PoissonContact.HasOptionalPoissonCounts (mu.map (contacts v w)) 0)
    (hR : HasLaw (recovery 0) (expMeasure 1) mu) :
    ∀ᵐ omega ∂mu, 0 < recovery 0 omega ∧
      (optionalContactRun n (fun v => recovery v omega) (fun v w => contacts v w omega) 1).time =
        recovery 0 omega ∧
      ∀ k, optionalContactRun n (fun v => recovery v omega) (fun v w => contacts v w omega) (k + 1) =
        recoveredRootFrame n (fun v => recovery v omega) := by
  have : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have hp : ∀ᵐ r ∂expMeasure 1, 0 < r := by
    apply (mem_ae_iff_prob_eq_one measurableSet_Ioi).mpr
    rw [expMeasure_Ioi_of_nonneg (by norm_num) (by norm_num)]
    norm_num
  have hpos : ∀ᵐ omega ∂mu, 0 < recovery 0 omega := by
    apply ae_of_ae_map hR.aemeasurable
    rw [hR.map_eq]
    exact hp
  filter_upwards [zero_contacts_empty_ae mu n contacts hC hcounts, hpos] with omega he hpos
  have hh := optionalContactRun_succ_of_empty_contacts n (fun v => recovery v omega)
    (fun v w => contacts v w omega) he
  refine ⟨hpos, ?_, hh⟩
  rw [hh 0]
  rfl

end Freezing1.SIR
