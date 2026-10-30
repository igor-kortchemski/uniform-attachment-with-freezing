module

public import Freezing1.SIRPoissonFullContactLaw
public import Freezing1.SIRPathSpace
public import Freezing1.MainSIRUniformDistanceStrong

/-!
# Source data and observable laws for the physical SIR protocol

The laws below use the actual next-point protocol on entire independent
contact paths. Their identities with embedded laws are conclusions of the
proved clock-history theorem. Definitions are total on arbitrary data;
asymptotic results need the source data assumptions only eventually.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

/-- Exactly the source's independent recovery periods and directed contact
processes, indexed by the source's infection age. Positivity of the rate is
kept separate, so that asymptotic wrappers can derive it eventually. -/
structure PoissonSIRData {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (n : ℕ) (rate : ℝ≥0)
    (X : (c : ClockSlot n) → Ω → ClockDatum c) : Prop where
  measurable : ∀ c, Measurable (X c)
  independent : iIndepFun X mu
  recovery_law : ∀ v : Individual n, mu.map (X (v, none)) = expMeasure 1
  contact_counts : ∀ v w : Individual n,
    PoissonContact.HasPoissonCounts (mu.map (X (v, some w))) rate

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def physicalTreePathLaw (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) : ProbabilityMeasure (ℕ → TreeState) :=
  ProbabilityMeasure.map (⟨mu, inferInstance⟩ : ProbabilityMeasure Ω)
    (fun omega => poissonFullContactTreePath n (fun c => X c omega))

noncomputable def physicalCountsPathLaw (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) : ProbabilityMeasure (ℕ → Counts) :=
  ProbabilityMeasure.map (⟨mu, inferInstance⟩ : ProbabilityMeasure Ω) (fun omega k =>
    let z := (poissonFullContactRun n (fun c => X c omega) k).population
    (⟨z.susceptible.card, z.active.card⟩ : Counts))

noncomputable def physicalTerminalTreeLaw (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) : ProbabilityMeasure PlaneTree.Tree :=
  ProbabilityMeasure.map (⟨mu, inferInstance⟩ : ProbabilityMeasure Ω) (fun omega => PlaneForward.shape
    (poissonFullContactRun n (fun c => X c omega) (2 * n + 1)).population.tree)

noncomputable def physicalPopulationPathLaw (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) : ProbabilityMeasure PopulationPath :=
  ProbabilityMeasure.map (physicalCountsPathLaw mu n X) (scaledPopulationPath n)

/-- A uniformly sampled vertex of the actual tree, including frozen vertices. -/
noncomputable def physicalUniformHeightLaw (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) (k : ℕ) : Measure ℕ :=
  ((physicalTreePathLaw mu n X : Measure (ℕ → TreeState)).map
    (fun H => (H k).tree)).bind PlaneForward.vertexHeightKernel

/-- The two vertices are conditionally independent given the same actual
whole tree. The equality/diagonal cases remain part of this law. -/
noncomputable def physicalPairDataLaw (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) (k : ℕ) : Measure (ℕ × ℕ × ℕ) :=
  ((physicalTreePathLaw mu n X : Measure (ℕ → TreeState)).map
    (fun H => (H k).tree)).bind PlaneForward.pairDataKernel

variable {mu : Measure Ω} [IsProbabilityMeasure mu] {n : ℕ} {rate : ℝ≥0}
  {X : (c : ClockSlot n) → Ω → ClockDatum c}

theorem PoissonSIRData.treePathLaw_eq (h : PoissonSIRData mu n rate X) (hr : 0 < rate) :
    (physicalTreePathLaw mu n X : Measure (ℕ → TreeState)) = treeFullLaw rate n :=
  independent_poisson_fullContact_tree_fullLaw mu n rate hr X h.measurable h.independent
    h.recovery_law h.contact_counts

theorem PoissonSIRData.countsPathLaw_eq (h : PoissonSIRData mu n rate X) (hr : 0 < rate) :
    (physicalCountsPathLaw mu n X : Measure (ℕ → Counts)) = countsFullLaw rate n :=
  independent_poisson_fullContact_counts_fullLaw mu n rate hr X h.measurable h.independent
    h.recovery_law h.contact_counts

theorem PoissonSIRData.terminalTreeLaw_eq (h : PoissonSIRData mu n rate X) (hr : 0 < rate) :
    physicalTerminalTreeLaw mu n X = embeddedTerminalTreeLaw rate n := by
  apply Subtype.ext
  exact independent_poisson_fullContact_terminal_tree_law mu n rate hr X h.measurable
    h.independent h.recovery_law h.contact_counts

theorem PoissonSIRData.populationPathLaw_eq (h : PoissonSIRData mu n rate X) (hr : 0 < rate) :
    physicalPopulationPathLaw mu n X = populationPathLaw rate n := by
  apply Subtype.ext
  change ((physicalCountsPathLaw mu n X : Measure (ℕ → Counts)).map
    (scaledPopulationPath n)) = _
  rw [h.countsPathLaw_eq hr]
  rfl

theorem PoissonSIRData.uniformHeightLaw_eq (h : PoissonSIRData mu n rate X) (hr : 0 < rate)
    (k : ℕ) : physicalUniformHeightLaw mu n X k = sirUniformHeightLaw rate n k := by
  unfold physicalUniformHeightLaw sirUniformHeightLaw
  rw [h.treePathLaw_eq hr]

theorem PoissonSIRData.pairDataLaw_eq (h : PoissonSIRData mu n rate X) (hr : 0 < rate)
    (k : ℕ) : physicalPairDataLaw mu n X k = sirPairDataLaw rate n k := by
  unfold physicalPairDataLaw sirPairDataLaw
  rw [h.treePathLaw_eq hr]

/-- The finite-word carrier is exactly the stopped physical path,
simultaneously at all nonnegative real observation times. -/
theorem PoissonSIRData.scaledPopulationPath_ae (h : PoissonSIRData mu n rate X)
    (hr : 0 < rate) :
    ∀ᵐ H ∂(physicalCountsPathLaw mu n X : Measure (ℕ → Counts)), ∀ t : ℝ≥0,
      UniformOnFun.toFun timeWindows (scaledPopulationPath n H) t =
        ((H ⌊(n : ℝ) * (t : ℝ)⌋₊).infectious : ℝ) / n := by
  rw [h.countsPathLaw_eq hr]
  exact Freezing1.SIR.scaledPopulationPath_ae rate n

omit [MeasurableSpace Ω] in
theorem eventually_rate_pos_of_scaled_limit (rates : ℕ → ℝ≥0) {lam : ℝ}
    (hlam : 0 < lam)
    (h : Tendsto (fun n : ℕ => (n : ℝ) * rates n) atTop (𝓝 lam)) :
    ∀ᶠ n in atTop, 0 < rates n := by
  filter_upwards [h.eventually (eventually_gt_nhds hlam)] with n hn
  exact_mod_cast pos_of_mul_pos_right hn (Nat.cast_nonneg n)

omit [MeasurableSpace Ω] in
theorem eventually_rate_pos_of_scaled_atTop (rates : ℕ → ℝ≥0)
    (h : Tendsto (fun n : ℕ => (n : ℝ) * rates n) atTop atTop) :
    ∀ᶠ n in atTop, 0 < rates n := by
  filter_upwards [h.eventually_gt_atTop 0] with n hn
  exact_mod_cast pos_of_mul_pos_right hn (Nat.cast_nonneg n)

end Freezing1.SIR
