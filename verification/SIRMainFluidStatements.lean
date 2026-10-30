module

public import Freezing1.MainSIRFluid

/-! Independent source-statement probes for the entire SIR fluid path law. -/

@[expose] public section

namespace Freezing1.SIRMainFluidStatements

open Filter Set MeasureTheory ProbabilityTheory Freezing1.SIR
open scoped NNReal ENNReal Topology UniformConvergence Classical

theorem source_geometric_parameter (lam : ℝ≥0) :
    (unitInterval.symm (infectionProbability lam 1) : ℝ) = 1 / (1 + (lam : ℝ)) := by
  rw [unitInterval.coe_symm_eq, infectionProbability_complement]
  simp

theorem geometric_survival_is_arbitrarily_deep (T : PlaneTree.Tree) :
    ¬PlaneTree.FiniteVertices T ↔
      ∀ D : ℕ, ∃ u : PlaneTree.Address, PlaneTree.Present T u ∧ D < u.length := by
  rw [PlaneTree.finiteVertices_iff_heightBound]
  push Not
  rfl

theorem source_limit_path_one_shared_event (lam : ℝ≥0) (T : PlaneTree.Tree) :
    ∀ t : ℝ≥0, UniformOnFun.toFun timeWindows (geometricSurvivalPath lam T) t =
      (if ¬PlaneTree.FiniteVertices T then
        max (2 - 2 * fluidProfile lam (t : ℝ) - (t : ℝ)) 0 else 0) := by
  intro t
  by_cases hT : ¬PlaneTree.FiniteVertices T <;>
    simp [geometricSurvivalPath, positiveProfilePath, zeroPopulationPath,
      infectiousProfile, hT]

theorem source_limit_path_two_possibilities (lam : ℝ≥0) (T : PlaneTree.Tree) :
    (∀ t : ℝ≥0, UniformOnFun.toFun timeWindows (geometricSurvivalPath lam T) t =
      max (2 - 2 * fluidProfile lam (t : ℝ) - (t : ℝ)) 0) ∨
    (∀ t : ℝ≥0, UniformOnFun.toFun timeWindows (geometricSurvivalPath lam T) t = 0) := by
  by_cases hT : ¬PlaneTree.FiniteVertices T
  · left
    intro t
    simpa only [ite_eq_left hT] using source_limit_path_one_shared_event lam T t
  · right
    intro t
    simpa only [ite_eq_right hT] using source_limit_path_one_shared_event lam T t

theorem source_survival_probability (lam : ℝ≥0) (hlam : 1 < (lam : ℝ)) :
    (PlaneTree.geometricBienaymeLaw (infectionProbability lam 1)).real
      {T | ¬PlaneTree.FiniteVertices T} = 1 - 1 / (lam : ℝ) :=
  geometric_sir_survival_real lam hlam

theorem actual_stopped_path_values (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂countsFullLaw rate n, ∀ t : ℝ≥0,
      UniformOnFun.toFun timeWindows (scaledPopulationPath n H) t =
        ((H ⌊(n : ℝ) * (t : ℝ)⌋₊).infectious : ℝ) / n :=
  scaledPopulationPath_ae rate n

theorem source_topology_on_whole_paths {ι : Type*} {l : Filter ι}
    {F : ι → PopulationPath} {f : PopulationPath} :
    Tendsto F l (𝓝 f) ↔ ∀ K : Set ℝ≥0, IsCompact K →
      TendstoUniformlyOn (fun i t => UniformOnFun.toFun timeWindows (F i) t)
        (UniformOnFun.toFun timeWindows f) l K :=
  populationPath_tendsto_iff_on_compacts

theorem source_entire_path_limit (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ)))
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => populationPathLaw (rate n) n) atTop
      (𝓝 (geometricSurvivalPathLaw lam)) :=
  embedded_sir_fluid_limit_of_source_ratio rate lam hlam hratio

theorem scaled_rate_entire_path_limit (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ))) :
    Tendsto (fun n : ℕ => populationPathLaw (rate n) n) atTop
      (𝓝 (geometricSurvivalPathLaw lam)) :=
  embedded_sir_fluid_limit rate lam hlam hrate

theorem concrete_rate_two_over_n :
    Tendsto (fun n : ℕ => populationPathLaw ((2 : ℝ≥0) / n) n) atTop
      (𝓝 (geometricSurvivalPathLaw 2)) := by
  apply embedded_sir_fluid_limit (fun n => (2 : ℝ≥0) / n) 2 (by norm_num)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  change (2 : ℝ) = (n : ℝ) * (2 / (n : ℝ))
  field_simp [hn0]

end Freezing1.SIRMainFluidStatements
