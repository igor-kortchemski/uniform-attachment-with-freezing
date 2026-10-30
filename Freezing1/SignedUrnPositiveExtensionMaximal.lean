module

public import Freezing1.SignedUrnPositiveExtensionBounds
public import Freezing1.SignedUrnPositiveExtensionPath

/-! Source A63: apply the actual infinite urn to the original finite component. -/

@[expose] public section

namespace Freezing1.SignedUrn

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

/-- The constructed infinite urn really has nonnegative integer occupancies
bounded by its population, simultaneously at every time. -/
theorem positiveExtension_infinite_valid (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : PositiveThrough x b) :
    ∀ᵐ H ∂infiniteUrnLaw (positiveExtensionPopulation x a b) 1,
      ∀ i : ℕ, 0 ≤ H i ∧ H i ≤ positiveExtensionPopulation x a b i := by
  apply ae_all_iff.mpr
  intro i
  apply ae_of_ae_map (f := fun H : InfiniteUrnHistory => H i)
    (p := fun u : ℤ => 0 ≤ u ∧ u ≤ positiveExtensionPopulation x a b i) (measurable_pi_apply i).aemeasurable
  rw [infiniteUrnLaw_map_eval]
  have hpos := positiveExtensionPopulation_positive x (a := a) hb 0
  have hu : (1 : ℤ) ≤ positiveExtensionPopulation x a b 0 := by omega
  simpa only [Nat.zero_add] using continuationLaw_valid (positiveExtensionPopulation x a b)
    (a := 0) (k := i) (u := 1) (fun j _ => positiveExtensionPopulation_positive x hb j)
    (fun j _ => positiveExtensionPopulation_signed x hab j) (by norm_num) hu

theorem positiveExtension_infinite_maximal (x : SignSequence) {a b : ℕ}
    (hab : a < b) (hb : PositiveThrough x b) {t : ℝ} (ht : 0 ≤ t) :
    (infiniteUrnLaw (positiveExtensionPopulation x a b) 1).real {H |
      ∃ i : ℕ, 1 ≤ i ∧ t / (activeCount x a : ℝ) <
        |(H i : ℝ) / positiveExtensionPopulation x a b i - (activeCount x a : ℝ)⁻¹|} ≤
      2 * Real.exp (-((t ^ 2 / 4) * (activeCount x a : ℝ)⁻¹) /
        (infiniteSquareBudget (positiveExtensionPopulation x a b) + t *
          max (infiniteSquareBudget (positiveExtensionPopulation x a b)) (sourceEpsilon x a b hab))) := by
  have hs : Summable (fun i : ℕ => ((positiveExtensionPopulation x a b i : ℝ)⁻¹) ^ 2) :=
    (summable_nat_add_iff 1).mp (positiveExtension_square_summable x hab.le hb)
  have h := infinite_maximal_summable (μ := infiniteUrnLaw (positiveExtensionPopulation x a b) 1)
    (fun i (H : InfiniteUrnHistory) => H i) (positiveExtensionPopulation x a b)
    (infiniteUrnLaw_hasPathLaws _ 1) (positiveExtensionPopulation_positive x hb)
    (positiveExtensionPopulation_signed x hab.le) hs ht
  rwa [positiveExtensionPopulation_zero x hab.le,
    positiveExtension_maximum_eq_sourceEpsilon x hab hb] at h

theorem positiveExtension_original_urn_endpoint (x : SignSequence) {a b : ℕ} (hab : a ≤ b) :
    continuationLaw (activeCount x) a (b - a) 1 =
      (infiniteUrnLaw (positiveExtensionPopulation x a b) 1).map (fun H => H (b - a)) := by
  rw [infiniteUrnLaw_map_eval]
  change continuationLaw (activeCount x) a (b - a) 1 =
    continuationLaw (fun i => activeCount (positiveExtension x b) (a + i)) 0 (b - a) 1
  rw [continuationLaw_shift, Nat.add_zero]
  apply continuationLaw_congr_population
  intro i hi
  exact (activeCount_positiveExtension_prefix x b (by have := (Finset.mem_Icc.mp hi).2; omega)).symm

/-- The finite source urn endpoint is controlled by the verified infinite
extension, with exactly the source delta and epsilon. No finite path-law or
maximal concentration premise is introduced. -/
theorem positiveExtension_urn_endpoint_upper (x : SignSequence) {a b : ℕ}
    (hab : a < b) (hb : PositiveThrough x b) {t : ℝ} (ht : 0 ≤ t) :
    (continuationLaw (activeCount x) a (b - a) 1).real {u : ℤ |
      (1 + t) / (activeCount x a : ℝ) < (u : ℝ) / activeCount x b} ≤
      2 * Real.exp (-((t ^ 2 / 4) * (activeCount x a : ℝ)⁻¹) /
        (infiniteSquareBudget (positiveExtensionPopulation x a b) + t *
          max (infiniteSquareBudget (positiveExtensionPopulation x a b)) (sourceEpsilon x a b hab))) := by
  have hSa : 0 < (activeCount x a : ℝ) := by exact_mod_cast hb a hab.le
  have he : (1 + t) / (activeCount x a : ℝ) =
      (activeCount x a : ℝ)⁻¹ + t / (activeCount x a : ℝ) := by ring
  rw [positiveExtension_original_urn_endpoint x hab.le]
  change (((infiniteUrnLaw (positiveExtensionPopulation x a b) 1).map (fun H => H (b - a))) _).toReal ≤ _
  rw [Measure.map_apply (measurable_pi_apply _) (by trivial)]
  apply (measureReal_mono _ (measure_ne_top _ _)).trans (positiveExtension_infinite_maximal x hab hb ht)
  intro H hH
  refine ⟨b - a, by omega, ?_⟩
  have hZ : positiveExtensionPopulation x a b (b - a) = activeCount x b := by
    simpa only [Nat.add_zero, Int.natCast_zero, add_zero] using positiveExtensionPopulation_tail x hab.le 0
  rw [hZ]
  change (1 + t) / (activeCount x a : ℝ) < (H (b - a) : ℝ) / activeCount x b at hH
  rw [he] at hH
  have hd : t / (activeCount x a : ℝ) < (H (b - a) : ℝ) / activeCount x b - (activeCount x a : ℝ)⁻¹ := by
    linarith only [hH]
  exact hd.trans_le (le_abs_self _)

/-- A genuinely active lower-cut root has this endpoint bound in the
original attachment/freezing process itself. -/
theorem positiveExtension_component_endpoint_upper {x : SignSequence} {a b : ℕ}
    {s : Forward.State} (hd : Forward.PhaseData x a s) (hab : a < b) (hb : PositiveThrough x b)
    {r : ℕ} (hr : r ∈ s.active) {t : ℝ} (ht : 0 ≤ t) :
    (Forward.continuationLaw x a (b - a) s).real {q |
      (1 + t) / (activeCount x a : ℝ) < (Forward.componentPopulation q a r : ℝ) / activeCount x b} ≤
      2 * Real.exp (-((t ^ 2 / 4) * (activeCount x a : ℝ)⁻¹) /
        (infiniteSquareBudget (positiveExtensionPopulation x a b) + t *
          max (infiniteSquareBudget (positiveExtensionPopulation x a b)) (sourceEpsilon x a b hab))) := by
  have hlaw := Forward.continuationLaw_componentPopulation_of_root (k := b - a) hd
    (by simpa only [Nat.add_sub_of_le hab.le] using ((lt_extinctionTime_iff x b).mpr hb).le) hr
  have he := congrArg (fun μ : Measure ℤ => μ {u | (1 + t) / (activeCount x a : ℝ) < (u : ℝ) / activeCount x b}) hlaw
  rw [Measure.map_apply measurable_from_top (by trivial)] at he
  have heR := congrArg ENNReal.toReal he
  exact heR.le.trans (positiveExtension_urn_endpoint_upper x hab hb ht)

/-- The marked-root convention is retained in the final actual-process
bound: its cap is the true urn cap plus one, including later-frozen roots. -/
theorem positiveExtension_marked_component_endpoint_upper {x : SignSequence} {a b : ℕ}
    {s : Forward.State} (hd : Forward.PhaseData x a s) (hab : a < b) (hb : PositiveThrough x b)
    {r : ℕ} (hr : r ∈ s.active) {t : ℝ} (ht : 0 ≤ t) :
    (Forward.continuationLaw x a (b - a) s).real {q |
      1 + (1 + t) * (activeCount x b : ℝ) / activeCount x a <
        (Forward.componentPopulationWithRoot q a r : ℝ)} ≤
      2 * Real.exp (-((t ^ 2 / 4) * (activeCount x a : ℝ)⁻¹) /
        (infiniteSquareBudget (positiveExtensionPopulation x a b) + t *
          max (infiniteSquareBudget (positiveExtensionPopulation x a b)) (sourceEpsilon x a b hab))) := by
  have hSb : 0 < (activeCount x b : ℝ) := by exact_mod_cast hb b le_rfl
  apply (measureReal_mono _ (measure_ne_top _ _)).trans
    (positiveExtension_component_endpoint_upper hd hab hb hr ht)
  intro q hq
  change 1 + (1 + t) * (activeCount x b : ℝ) / activeCount x a <
    (Forward.componentPopulationWithRoot q a r : ℝ) at hq
  have hcap : (Forward.componentPopulationWithRoot q a r : ℝ) ≤
      (Forward.componentPopulation q a r : ℝ) + 1 := by
    exact_mod_cast Forward.componentPopulationWithRoot_le q a r
  apply (lt_div_iff₀ hSb).mpr
  have hU : (1 + t) * (activeCount x b : ℝ) / activeCount x a <
      (Forward.componentPopulation q a r : ℝ) := by linarith only [hq, hcap]
  convert hU using 1; ring

end Freezing1.SignedUrn
