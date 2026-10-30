module

public import Freezing1.SIRPhysicalZeroRate
public import Freezing1.SIRForwardPrefixBridge

/-! Independent zero-contact source-model and full-prefix statement probes. -/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory CountableMarkovChain
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

example (nu : Measure PoissonContact.OptionalPath) [IsProbabilityMeasure nu] :
    PoissonContact.HasOptionalPoissonCounts nu 0 ↔ nu = Measure.dirac PoissonContact.emptyPath :=
  PoissonContact.hasOptionalPoissonCounts_zero_iff nu

example {n : ℕ} (F : ClockFrame n) (R : Individual n → ℝ)
    (C : OptionalContactData n) (v w : Individual n) (h : C v w = PoissonContact.emptyPath) :
    optionalEventTime F R C (v, some w) = none := by
  simp [optionalEventTime, h, PoissonContact.emptyPath]

variable {Ω : Type*} [MeasurableSpace Ω]
  (mu : Measure Ω) [IsProbabilityMeasure mu] (n : ℕ)
  (recovery : Individual n → Ω → ℝ)
  (contacts : Individual n → Individual n → Ω → PoissonContact.OptionalPath)
  (hC : ∀ v w, Measurable (contacts v w))
  (hcounts : ∀ v w, PoissonContact.HasOptionalPoissonCounts (mu.map (contacts v w)) 0)

include hC hcounts

example :
    mu.map (fun omega => optionalContactTreePath n (fun v => recovery v omega)
      (fun v w => contacts v w omega)) = treeFullLaw 0 n :=
  zeroRate_physical_tree_fullLaw mu n recovery contacts hC hcounts

/-- The physical count theorem also holds for literal label cardinalities,
so its count projection is the source U/I process. -/
theorem literal_zero_counts_fullLaw :
    mu.map (fun omega k =>
      let z := (optionalContactRun n (fun v => recovery v omega) (fun v w => contacts v w omega) k).population
      (⟨z.susceptible.card, z.active.card⟩ : Counts)) = countsFullLaw 0 n := by
  calc
    _ = mu.map (fun omega k =>
        (optionalContactTreePath n (fun v => recovery v omega)
          (fun v w => contacts v w omega) k).counts) := by
      apply Measure.map_congr
      filter_upwards [zero_contacts_empty_ae mu n contacts hC hcounts] with omega he
      funext k
      have hv : (optionalContactRun n (fun v => recovery v omega)
          (fun v w => contacts v w omega) k).population.Valid := by
        cases k with
        | zero => exact initialPopulation_valid n
        | succ k =>
          rw [optionalContactRun_succ_of_empty_contacts n _ _ he k]
          exact (initialPopulation_valid n).recover (by simp [initialPopulation])
      simp only [optionalContactTreePath, PopulationState.project, TreeState.counts, hv.active_card]
    _ = _ := zeroRate_physical_counts_fullLaw mu n recovery contacts hC hcounts

/-- The already proved A66 adapter composes with the actual zero-rate
physical protocol as well, keeping the entire count/tree prefix jointly. -/
theorem zeroBranch_original_forward_prefix (k : ℕ) :
    (mu.map (fun omega => optionalContactTreePath n (fun v => recovery v omega)
      (fun v w => contacts v w omega))).map (fun H =>
        ((fun i : Finset.Iic k => (H i.val).counts),
          (fun i : Finset.Iic k => (H i.val).tree))) =
      (signWordLaw 0 n k).bind (fun w =>
        ((ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w)).map
          (Preorder.frestrictLe k)).map
            (fun P => (countsPrefixWord n w, ForwardAnnealed.planePrefix k P))) := by
  rw [zeroRate_physical_tree_fullLaw mu n recovery contacts hC hcounts]
  exact treeFullLaw_countsPrefix_original_treePrefix_word_mixture 0 n k

example (hR : HasLaw (recovery 0) (expMeasure 1) mu) :
    ∀ᵐ omega ∂mu, 0 < recovery 0 omega ∧
      (optionalContactRun n (fun v => recovery v omega) (fun v w => contacts v w omega) 1).time =
        recovery 0 omega ∧
      ∀ k, optionalContactRun n (fun v => recovery v omega) (fun v w => contacts v w omega) (k + 1) =
        recoveredRootFrame n (fun v => recovery v omega) :=
  zeroRate_physical_absorption mu n recovery contacts hC hcounts hR

#print axioms PoissonContact.hasOptionalPoissonCounts_zero_iff
#print axioms optionalContactRun_succ_of_empty_contacts
#print axioms zeroRate_physical_tree_fullLaw
#print axioms zeroRate_physical_counts_fullLaw
#print axioms zeroRate_physical_absorption
#print axioms literal_zero_counts_fullLaw
#print axioms zeroBranch_original_forward_prefix

end Freezing1.SIR
