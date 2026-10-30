module

import Freezing1.IidLinearConditionedRows
import Freezing1.IidLinearMaximumRatio

/-! Authored expanded source checks of the finite-conditioning coupling. -/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Classical Topology ENNReal
open Freezing1 Freezing1.ConditionalSurvival Freezing1.ForwardAnnealed

set_option backward.isDefEq.respectTransparency false

example {rows : ℕ → SignSequence} {A : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (nearOriginMaximum rows A c 1) atTop (𝓝 0))
    (hc : 0 < c) (hc1 : c ≤ 1) (hApos : ∀ n, 0 < A n)
    (hAlog : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hs : ∀ n, PositiveThrough (rows n) n) :
    Tendsto (fun ε : ℝ => limsup (nearOriginMaximum rows A c ε) atTop)
        (𝓝[>] 0) (𝓝 0) ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → 0 < liminf (bulkMinimum rows ε) atTop :=
  sourceAssumptions_of_uniformMaximum h hc hc1 hApos hAlog hs

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {s t : Set Ω} (ht : MeasurableSet t) (hts : t ⊆ s) (ht0 : μ t ≠ 0)
    (ν : Measure Ω) :
    μ[|s] = (μ t / μ s) • μ[|t] +
      (μ (s \ t) / μ s) • (if μ (s \ t) = 0 then ν else μ[|s \ t]) :=
  conditional_mixture μ ht hts ht0 ν

example {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    conditionalOr μ ∅ ν = ν ∧ IsProbabilityMeasure (conditionalOr μ ∅ ν) := by
  exact ⟨by simp [conditionalOr], inferInstance⟩

example {Ω : Type*} [MeasurableSpace Ω] (D : System Ω) :
    (∀ n, D.couplingLaw.map (D.row n) = D.law[|D.event n]) ∧
      D.couplingLaw.map D.survivor = D.law[|⋂ n, D.event n] ∧
      ∀ᵐ z ∂D.couplingLaw, ∃ N : ℕ, ∀ n, N ≤ n → D.row n z = D.survivor z := by
  refine ⟨D.map_row, D.map_survivor, ?_⟩
  exact D.eventually_row_eq_survivor.mono fun _ h => eventually_atTop.mp h

example (p : unitInterval) (hp : (1 : ℝ) / 2 < p) (n : ℕ) :
    (conditionedIidRowsLaw p hp).map (conditionedIidRow p hp n) =
      (iidSignLaw p)[|{x | (n : ℕ∞) < extinctionTime x}] :=
  (conditionedIidRow_hasLaw p hp n).map_eq

example (p : unitInterval) (hp : (1 : ℝ) / 2 < p) :
    (iidSignLaw p) {x | extinctionTime x = ⊤} ≠ 0 ∧
      (conditionedIidRowsLaw p hp).map (commonIidSurvivor p hp) =
        (iidSignLaw p)[|{x | extinctionTime x = ⊤}] := by
  exact ⟨by simpa only [iInter_survivesThrough] using iid_survival_positive p hp,
    (commonIidSurvivor_hasLaw p hp).map_eq⟩

example (p : unitInterval) (hp : (1 : ℝ) / 2 < p) (A : ℕ → ℝ)
    (hA : Tendsto A atTop atTop) :
    ∀ᵐ z ∂conditionedIidRowsLaw p hp,
      Tendsto (nearOriginMaximum (fun n => conditionedIidRow p hp n z) A (2 * (p : ℝ) - 1) 1)
        atTop (𝓝 0) :=
  (conditionedIidRows_uniformTailRatio p hp A hA).mono
    fun _ h => uniformTailRatio_iff_maximum_tendsto.mp h

example (p : unitInterval) (hp : (1 : ℝ) / 2 < p) (hp1 : (p : ℝ) < 1)
    (A : ℕ → ℝ) (hApos : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hAlog : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0)) :
    ∃ μ : Measure IidSurvivalSpace, IsProbabilityMeasure μ ∧
      ∃ rows : ℕ → IidSurvivalSpace → SignSequence,
        ∃ survivor : IidSurvivalSpace → SignSequence,
          (∀ n, HasLaw (rows n) ((iidSignLaw p)[|{x | (n : ℕ∞) < extinctionTime x}]) μ) ∧
          HasLaw survivor ((iidSignLaw p)[|{x | extinctionTime x = ⊤}]) μ ∧
          ∀ᵐ z ∂μ, (∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n z)) ∧
            (∃ N : ℕ, ∀ n, N ≤ n → rows n z = survivor z) ∧
            Tendsto (fun ε : ℝ => limsup
              (nearOriginMaximum (fun n => rows n z) A (2 * (p : ℝ) - 1) ε) atTop)
                (𝓝[>] 0) (𝓝 0) ∧
            ∀ ε : ℝ, 0 < ε → ε < 1 →
              0 < liminf (bulkMinimum (fun n => rows n z) ε) atTop := by
  obtain ⟨μ, hμ, rows, survivor, hr, hb, hrest⟩ :=
    exists_conditioned_iid_linear_coupling p hp hp1 A hApos hAinf hAlog
  refine ⟨μ, hμ, rows, survivor, hr, hb, ?_⟩
  exact hrest.mono fun _ h => ⟨h.1, eventually_atTop.mp h.2.1, h.2.2⟩

#print axioms UniformTailRatio.sourceAssumptions
#print axioms uniformTailRatio_of_eventually_eq_path
#print axioms uniformTailRatio_iff_maximum_tendsto
#print axioms sourceAssumptions_of_uniformMaximum
#print axioms conditional_mixture
#print axioms weight_tendsto_one
#print axioms map_chooseRow
#print axioms System.map_row
#print axioms System.eventually_row_eq_survivor
#print axioms System.rows_mem
#print axioms iid_survival_positive
#print axioms conditionedIidRow_hasLaw
#print axioms commonIidSurvivor_hasLaw
#print axioms conditionedIidRows_sourceAssumptions
#print axioms exists_conditioned_iid_linear_coupling
