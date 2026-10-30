module

public import Freezing1.SIRCountLaw
public import Freezing1.SIRFluidProfile
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# SIR paths with uniform convergence on compact time intervals

The carrier includes the actual step paths. Its topology is characterized
below by uniform convergence on every compact subset of nonnegative times.
The deterministic terminal bound makes the scaled stopped path a measurable
function of finitely many count observations.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory
open scoped Topology UniformConvergence NNReal ENNReal Classical

def timeWindow (m : ℕ) : Set ℝ≥0 := Icc 0 m

def timeWindows : Set (Set ℝ≥0) := Set.range timeWindow

theorem timeWindow_mono : Monotone timeWindow := by
  intro m n hmn
  exact Icc_subset_Icc le_rfl (by exact_mod_cast hmn)

theorem timeWindows_nonempty : timeWindows.Nonempty := ⟨timeWindow 0, ⟨0, rfl⟩⟩

theorem timeWindows_directed : DirectedOn (· ⊆ ·) timeWindows := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
  exact ⟨timeWindow (max m n), ⟨max m n, rfl⟩,
    timeWindow_mono (le_max_left _ _), timeWindow_mono (le_max_right _ _)⟩

theorem isCompact_subset_timeWindow {K : Set ℝ≥0} (hK : IsCompact K) :
    ∃ m : ℕ, K ⊆ timeWindow m := by
  obtain ⟨b, hb⟩ := hK.bddAbove
  obtain ⟨m, hm⟩ := exists_nat_ge (b : ℝ)
  refine ⟨m, fun t ht => ⟨bot_le, ?_⟩⟩
  have hh : (t : ℝ) ≤ m := (by exact_mod_cast hb ht : (t : ℝ) ≤ b).trans hm
  exact_mod_cast hh

theorem timeWindows_cover : ⋃₀ timeWindows = univ := by
  apply Set.eq_univ_of_forall
  intro t
  obtain ⟨m, hm⟩ := isCompact_subset_timeWindow (isCompact_singleton (x := t))
  exact Set.mem_sUnion.mpr ⟨timeWindow m, ⟨m, rfl⟩, hm (by simp)⟩

abbrev PopulationPath := ℝ≥0 →ᵤ[timeWindows] ℝ

instance : MeasurableSpace PopulationPath := borel PopulationPath
instance : BorelSpace PopulationPath := ⟨rfl⟩
instance : T2Space PopulationPath := UniformOnFun.t2Space_of_covering timeWindows_cover

theorem populationPath_tendsto_iff_on_compacts {ι : Type*} {l : Filter ι}
    {F : ι → PopulationPath} {f : PopulationPath} :
    Tendsto F l (𝓝 f) ↔ ∀ K : Set ℝ≥0, IsCompact K →
      TendstoUniformlyOn (fun i t => UniformOnFun.toFun timeWindows (F i) t)
        (UniformOnFun.toFun timeWindows f) l K := by
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn]
  constructor
  · intro h K hK
    obtain ⟨m, hm⟩ := isCompact_subset_timeWindow hK
    exact (h (timeWindow m) ⟨m, rfl⟩).mono hm
  · intro h K hK
    obtain ⟨m, rfl⟩ := hK
    exact h _ isCompact_Icc

theorem populationPath_nhds_control (f : PopulationPath) {U : Set PopulationPath}
    (hU : U ∈ 𝓝 f) :
    ∃ m : ℕ, ∃ eps : ℝ, 0 < eps ∧
      {g | ∀ t ∈ timeWindow m,
        |UniformOnFun.toFun timeWindows g t - UniformOnFun.toFun timeWindows f t| < eps} ⊆ U := by
  have hb := UniformOnFun.hasBasis_nhds_of_basis ℝ≥0 ℝ timeWindows f
    timeWindows_nonempty timeWindows_directed Metric.uniformity_basis_dist
  obtain ⟨⟨K, eps⟩, ⟨hK, heps⟩, hsub⟩ := hb.mem_iff.mp hU
  obtain ⟨m, rfl⟩ := hK
  refine ⟨m, eps, heps, ?_⟩
  intro g hg
  apply hsub
  intro t ht
  change dist (UniformOnFun.toFun timeWindows g t)
    (UniformOnFun.toFun timeWindows f t) < eps
  simpa only [Real.dist_eq] using hg t ht

noncomputable def populationPathOfWord (n : ℕ) (w : Fin (2 * n + 2) → ℕ) : PopulationPath :=
  UniformOnFun.ofFun timeWindows fun t =>
    (w ⟨min ⌊(n : ℝ) * (t : ℝ)⌋₊ (2 * n + 1), by omega⟩ : ℝ) / n

noncomputable def scaledPopulationPath (n : ℕ) (H : ℕ → Counts) : PopulationPath :=
  populationPathOfWord n (fun i => (H i).infectious)

theorem measurable_scaledPopulationPath (n : ℕ) : Measurable (scaledPopulationPath n) := by
  exact (measurable_of_countable (populationPathOfWord n)).comp
    (measurable_pi_iff.mpr fun i =>
      (measurable_of_countable Counts.infectious).comp (measurable_pi_apply (i : ℕ)))

theorem scaledPopulationPath_ae (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂countsFullLaw rate n, ∀ t : ℝ≥0,
      UniformOnFun.toFun timeWindows (scaledPopulationPath n H) t =
        ((H ⌊(n : ℝ) * (t : ℝ)⌋₊).infectious : ℝ) / n := by
  filter_upwards [countsFullLaw_absorbed_by rate n] with H hH
  intro t
  change ((H (min ⌊(n : ℝ) * (t : ℝ)⌋₊ (2 * n + 1))).infectious : ℝ) / n = _
  by_cases hk : ⌊(n : ℝ) * (t : ℝ)⌋₊ ≤ 2 * n + 1
  · rw [min_eq_left hk]
  · rw [min_eq_right (by omega), hH.2 ⌊(n : ℝ) * (t : ℝ)⌋₊ (by omega)]

noncomputable def populationPathLaw (rate : ℝ≥0) (n : ℕ) : ProbabilityMeasure PopulationPath :=
  ProbabilityMeasure.map (⟨countsFullLaw rate n, inferInstance⟩ : ProbabilityMeasure (ℕ → Counts))
    (scaledPopulationPath n)

noncomputable def positiveProfilePath (lam : ℝ) : PopulationPath :=
  UniformOnFun.ofFun timeWindows fun t => max (infectiousProfile lam t) 0

noncomputable def zeroPopulationPath : PopulationPath := UniformOnFun.ofFun timeWindows fun _ => 0

noncomputable def sirSurvivalParameter (lam : ℝ≥0) : unitInterval :=
  if h : 1 < (lam : ℝ) then
    ⟨1 - 1 / (lam : ℝ), by
      have hl : 0 < (lam : ℝ) := by linarith
      constructor
      · exact sub_nonneg.mpr ((div_le_one hl).mpr h.le)
      · linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hl.le]⟩
  else 0

theorem sirSurvivalParameter_coe {lam : ℝ≥0} (hlam : 1 < (lam : ℝ)) :
    (sirSurvivalParameter lam : ℝ) = 1 - 1 / (lam : ℝ) := by
  simp only [sirSurvivalParameter, dite_eq_left hlam]

noncomputable def fluidMixtureLaw (lam : ℝ≥0) : ProbabilityMeasure PopulationPath :=
  ProbabilityMeasure.map (⟨ProbabilityTheory.bernoulliMeasure true false (sirSurvivalParameter lam),
    inferInstance⟩ : ProbabilityMeasure Bool)
    (fun b : Bool => if b then positiveProfilePath lam else zeroPopulationPath)

end Freezing1.SIR
