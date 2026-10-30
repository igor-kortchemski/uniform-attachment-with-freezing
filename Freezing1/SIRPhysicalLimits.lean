module

public import Freezing1.SIRPhysicalLaws
public import Freezing1.MainSIREmbedded
public import Freezing1.MainSIRFluid
public import Freezing1.SIRStrongCounts
public import Freezing1.MainSIRUniformSamplesStrong
public import Freezing1.MainSIRStrongMaximum

/-!
# Source-facing infection-tree and fluid limits for the full contact protocol

Every law below is the pushforward of the actual entire-arrival-path SIR
protocol. The proved physical clock-history theorem supplies the embedded
identities. Source process assumptions are needed only eventually, and the
paper's rate asymptotics themselves imply eventual positive intensity.
Thus finitely many zero rates impose no additional asymptotic restriction.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (mu : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (mu n)]
  (X : (n : ℕ) → (c : ClockSlot n) → Ω n → ClockDatum c)

/-- T06.I for given independent source recovery/contact data, with exactly
the paper's rate ratio and its actual full terminal infection tree. -/
theorem physical_sir_geometric_local_limit_of_source_ratio (rate : ℕ → ℝ≥0)
    (lam : ℝ≥0) (hlam : 0 < lam)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1))
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n)) :
    Tendsto (fun n => physicalTerminalTreeLaw (mu n) n (X n)) atTop
      (𝓝 (geometricProbabilityLaw (infectionProbability lam 1))) := by
  have hscaled := scaled_rate_of_source_ratio rate lam hlam hratio
  have hp := eventually_rate_pos_of_scaled_limit rate (show (0 : ℝ) < lam by exact_mod_cast hlam)
    hscaled
  apply (embedded_sir_geometric_local_limit_of_source_ratio rate lam hlam hratio).congr'
  filter_upwards [hp, hdata] with n hpn hdn
  exact (hdn.terminalTreeLaw_eq hpn).symm

/-- The stronger bounded-root-degree escape underlying T06.II for the
actual terminal full-contact tree laws. -/
theorem physical_terminal_bounded_degree_tendsto_zero_of_source_ratio (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n)) (d : ℕ) :
    Tendsto (fun n => (physicalTerminalTreeLaw (mu n) n (X n) : Measure PlaneTree.Tree).real
      {T | PlaneTree.degree T ≤ d}) atTop (𝓝 0) := by
  have hscaled := scaled_rate_atTop_of_source_ratio rate hratio
  have hp := eventually_rate_pos_of_scaled_atTop rate hscaled
  apply (terminal_bounded_degree_tendsto_zero rate hscaled d).congr'
  filter_upwards [hp, hdata] with n hpn hdn
  rw [hdn.terminalTreeLaw_eq hpn]

/-- T06.II for actual full-contact terminal trees. No uniform positivity,
monotone rate, survival or fairness hypothesis is added. -/
theorem physical_sir_not_tight_of_source_ratio (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n)) :
    ¬IsTightMeasureSet (Set.range fun n =>
      (physicalTerminalTreeLaw (mu n) n (X n) : Measure PlaneTree.Tree)) :=
  PlaneTree.not_tight_of_bounded_degree_tendsto_zero _
    (physical_terminal_bounded_degree_tendsto_zero_of_source_ratio mu X rate hratio hdata)

/-- T07.I.a on the whole stopped physical count path, uniformly on compact
nonnegative time sets. The limit uses one shared geometric-tree survival event. -/
theorem physical_sir_fluid_limit_of_source_ratio (rate : ℕ → ℝ≥0)
    (lam : ℝ≥0) (hlam : 1 < (lam : ℝ))
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1))
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n)) :
    Tendsto (fun n => physicalPopulationPathLaw (mu n) n (X n)) atTop
      (𝓝 (geometricSurvivalPathLaw lam)) := by
  have hl0 : (0 : ℝ) < lam := lt_trans (by norm_num) hlam
  have hscaled := scaled_rate_of_source_ratio rate lam (by exact_mod_cast hl0) hratio
  have hp := eventually_rate_pos_of_scaled_limit rate hl0 hscaled
  apply (embedded_sir_fluid_limit_of_source_ratio rate lam hlam hratio).congr'
  filter_upwards [hp, hdata] with n hpn hdn
  exact (hdn.populationPathLaw_eq hpn).symm

/-- T07.II.a for the literal physical susceptible/infectious count law,
uniformly over the complete real time interval `[0,2]`. -/
theorem physical_sir_strong_uniform_fluid_limit_of_source_ratio (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n))
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => (physicalCountsPathLaw (mu n) n (X n) : Measure (ℕ → Counts)).real
      {H | ∃ t ∈ Set.Icc (0 : ℝ) 2, eps ≤
        |((H ⌊(n : ℝ) * t⌋₊).infectious : ℝ) / n - min t (2 - t)|}) atTop (𝓝 0) := by
  have hscaled := scaled_rate_atTop_of_source_ratio rate hratio
  have hp := eventually_rate_pos_of_scaled_atTop rate hscaled
  apply (countsFullLaw_strong_uniform_tendsto rate hscaled heps).congr'
  filter_upwards [hp, hdata] with n hpn hdn
  rw [hdn.countsPathLaw_eq hpn]

/-- T07.II.b.height: a conditionally uniform vertex of the actual full terminal
infection tree has height asymptotic to `log n`. -/
theorem physical_sir_strong_terminal_uniform_height_of_source_ratio (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n))
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => physicalUniformHeightLaw (mu n) n (X n) (2 * n + 1)
      {h | eps ≤ |(h : ℝ) / Real.log (n : ℝ) - 1|}) atTop (𝓝 0) := by
  have hscaled := scaled_rate_atTop_of_source_ratio rate hratio
  have hp := eventually_rate_pos_of_scaled_atTop rate hscaled
  apply (sir_terminal_uniform_height_tendsto rate hscaled heps).congr'
  filter_upwards [hp, hdata] with n hpn hdn
  rw [hdn.uniformHeightLaw_eq hpn]

/-- T07.II.b.distance: two conditionally independent uniform vertices of the actual
full tree have distance asymptotic to `2 * log n`, including the diagonal. -/
theorem physical_sir_strong_terminal_uniform_distance_of_source_ratio (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n))
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => physicalPairDataLaw (mu n) n (X n) (2 * n + 1)
      {z | eps ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - 2|}) atTop (𝓝 0) := by
  have hscaled := scaled_rate_atTop_of_source_ratio rate hratio
  have hp := eventually_rate_pos_of_scaled_atTop rate hscaled
  apply (sir_terminal_uniform_distance_tendsto rate hscaled heps).congr'
  filter_upwards [hp, hdata] with n hpn hdn
  rw [hdn.pairDataLaw_eq hpn]

/-- T07.II.b.maximum: the maximum height of the complete physical terminal tree is
asymptotic to `exp 1 * log n`. -/
theorem physical_sir_strong_terminal_maximum_of_source_ratio (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n))
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => (physicalTreePathLaw (mu n) n (X n) : Measure (ℕ → TreeState))
      {H | eps ≤ |(((H (2 * n + 1)).tree.vertices.sup List.length : ℕ) : ℝ) /
        Real.log (n : ℝ) - Real.exp 1|}) atTop (𝓝 0) := by
  have hscaled := scaled_rate_atTop_of_source_ratio rate hratio
  have hp := eventually_rate_pos_of_scaled_atTop rate hscaled
  apply (sir_terminal_maximum_tendsto rate hscaled heps).congr'
  filter_upwards [hp, hdata] with n hpn hdn
  rw [hdn.treePathLaw_eq hpn]

end Freezing1.SIR
