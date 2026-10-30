module

public import Freezing1.IidLinearSurvivalSystem

/-!
# Source A04 for finite-survival-conditioned iid rows

This is an explicit existence coupling with exact conditional marginals.
It asserts neither independence between the rows nor almost sure linear
profiles for an arbitrarily chosen coupling of those marginals.
-/

@[expose] public section

namespace Freezing1.ForwardAnnealed

open Filter Set MeasureTheory ProbabilityTheory
open scoped Classical Topology ENNReal

set_option backward.isDefEq.respectTransparency false

abbrev IidSurvivalSpace := ConditionalSurvival.Space SignSequence

noncomputable def conditionedIidRowsLaw (p : unitInterval) (hp : (1 : ℝ) / 2 < p) :
    Measure IidSurvivalSpace := (iidSurvivalSystem p hp).couplingLaw

instance (p : unitInterval) (hp : (1 : ℝ) / 2 < p) :
    IsProbabilityMeasure (conditionedIidRowsLaw p hp) := by
  unfold conditionedIidRowsLaw
  infer_instance

noncomputable def conditionedIidRow (p : unitInterval) (hp : (1 : ℝ) / 2 < p)
    (n : ℕ) : IidSurvivalSpace → SignSequence := (iidSurvivalSystem p hp).row n

noncomputable def commonIidSurvivor (p : unitInterval) (hp : (1 : ℝ) / 2 < p) :
    IidSurvivalSpace → SignSequence := (iidSurvivalSystem p hp).survivor

theorem conditionedIidRow_hasLaw (p : unitInterval) (hp : (1 : ℝ) / 2 < p) (n : ℕ) :
    HasLaw (conditionedIidRow p hp n) ((iidSignLaw p)[|survivesThrough n])
      (conditionedIidRowsLaw p hp) :=
  ⟨((iidSurvivalSystem p hp).measurable_row n).aemeasurable, (iidSurvivalSystem p hp).map_row n⟩

theorem commonIidSurvivor_hasLaw (p : unitInterval) (hp : (1 : ℝ) / 2 < p) :
    HasLaw (commonIidSurvivor p hp) ((iidSignLaw p)[|{x | extinctionTime x = ⊤}])
      (conditionedIidRowsLaw p hp) := by
  refine ⟨(iidSurvivalSystem p hp).measurable_survivor.aemeasurable, ?_⟩
  have h := (iidSurvivalSystem p hp).map_survivor
  change (conditionedIidRowsLaw p hp).map (commonIidSurvivor p hp) =
    (iidSignLaw p)[|⋂ n, survivesThrough n] at h
  rwa [iInter_survivesThrough] at h

theorem conditionedIidRows_eventually_eq (p : unitInterval) (hp : (1 : ℝ) / 2 < p) :
    ∀ᵐ z ∂conditionedIidRowsLaw p hp, ∀ᶠ n in atTop,
      conditionedIidRow p hp n z = commonIidSurvivor p hp z :=
  (iidSurvivalSystem p hp).eventually_row_eq_survivor

theorem conditionedIidRows_survive (p : unitInterval) (hp : (1 : ℝ) / 2 < p) :
    ∀ᵐ z ∂conditionedIidRowsLaw p hp, ∀ n : ℕ,
      (n : ℕ∞) < extinctionTime (conditionedIidRow p hp n z) :=
  (iidSurvivalSystem p hp).rows_mem

theorem commonIidSurvivor_drift (p : unitInterval) (hp : (1 : ℝ) / 2 < p) :
    ∀ᵐ z ∂conditionedIidRowsLaw p hp,
      Tendsto (fun i : ℕ => (activeCount (commonIidSurvivor p hp z) i : ℝ) / i)
        atTop (𝓝 (2 * (p : ℝ) - 1)) :=
  (iidSurvivalSystem p hp).survivor_property (iid_activeCount_drift p)

theorem conditionedIidRows_uniformTailRatio (p : unitInterval) (hp : (1 : ℝ) / 2 < p)
    (A : ℕ → ℝ) (hA : Tendsto A atTop atTop) :
    ∀ᵐ z ∂conditionedIidRowsLaw p hp,
      UniformTailRatio (fun n => conditionedIidRow p hp n z) A (2 * (p : ℝ) - 1) := by
  filter_upwards [conditionedIidRows_eventually_eq p hp, commonIidSurvivor_drift p hp] with z hz hd
  exact uniformTailRatio_of_eventually_eq_path hz hd hA

/-- The exact two nested source assumptions hold almost surely for this
coupling of the finite-survival-conditioned iid rows. -/
theorem conditionedIidRows_sourceAssumptions (p : unitInterval)
    (hp : (1 : ℝ) / 2 < p) (hp1 : (p : ℝ) < 1)
    (A : ℕ → ℝ) (hApos : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hAlog : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0)) :
    ∀ᵐ z ∂conditionedIidRowsLaw p hp,
      NearOriginLimsup (fun n => conditionedIidRow p hp n z) A (2 * (p : ℝ) - 1) ∧
        BulkLiminf (fun n => conditionedIidRow p hp n z) := by
  filter_upwards [conditionedIidRows_uniformTailRatio p hp A hAinf,
    conditionedIidRows_survive p hp] with z hz hs
  exact hz.sourceAssumptions (by linarith only [hp]) (by linarith only [hp1]) hApos hAlog
    (fun n => (lt_extinctionTime_iff _ n).mp (hs n))

/-- Source-facing existence statement. The survivor law and every finite
conditional iid marginal are exact; positive survival was derived from the
actual iid walk and is not a new hypothesis. -/
theorem exists_conditioned_iid_linear_coupling (p : unitInterval)
    (hp : (1 : ℝ) / 2 < p) (hp1 : (p : ℝ) < 1)
    (A : ℕ → ℝ) (hApos : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hAlog : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0)) :
    ∃ μ : Measure IidSurvivalSpace, IsProbabilityMeasure μ ∧
      ∃ rows : ℕ → IidSurvivalSpace → SignSequence,
        ∃ survivor : IidSurvivalSpace → SignSequence,
          (∀ n, HasLaw (rows n) ((iidSignLaw p)[|survivesThrough n]) μ) ∧
          HasLaw survivor ((iidSignLaw p)[|{x | extinctionTime x = ⊤}]) μ ∧
          ∀ᵐ z ∂μ, (∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n z)) ∧
            (∀ᶠ n in atTop, rows n z = survivor z) ∧
            NearOriginLimsup (fun n => rows n z) A (2 * (p : ℝ) - 1) ∧
            BulkLiminf (fun n => rows n z) := by
  refine ⟨conditionedIidRowsLaw p hp, inferInstance, conditionedIidRow p hp,
    commonIidSurvivor p hp, conditionedIidRow_hasLaw p hp, commonIidSurvivor_hasLaw p hp, ?_⟩
  filter_upwards [conditionedIidRows_survive p hp, conditionedIidRows_eventually_eq p hp,
    conditionedIidRows_sourceAssumptions p hp hp1 A hApos hAinf hAlog] with z hs he hlinear
  exact ⟨hs, he, hlinear⟩

end Freezing1.ForwardAnnealed
