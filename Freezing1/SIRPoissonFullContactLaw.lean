module

public import Freezing1.SIRPoissonFullContacts
public import Freezing1.SIRClockTreeFullLaw

/-!
# The full Poisson-contact protocol has the embedded tree history law

This consumer starts with whole directed contact arrival paths. At each event
the protocol inspects their next point after the source's current infection
age. Its complete clock-frame path agrees almost surely with the proved
static-array run. Thus the embedded genealogy and actual terminal tree have
exactly the existing laws, without an embedded-law or memorylessness premise.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def poissonFullContactTreePath (n : ℕ) (data : PoissonClockData n)
    (k : ℕ) : TreeState := (poissonFullContactRun n data k).population.project

theorem independent_poisson_fullContactRun_eq_preassigned
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (n : ℕ) (r : ℝ≥0) (hr : 0 < r)
    (X : (c : ClockSlot n) → Ω → ClockDatum c)
    (hX : ∀ c, Measurable (X c)) (hindep : iIndepFun X mu)
    (hrecovery : ∀ v : Individual n, mu.map (X (v, none)) = expMeasure 1)
    (hcontact : ∀ v w : Individual n,
      PoissonContact.HasPoissonCounts (mu.map (X (v, some w))) r) :
    ∀ᵐ omega ∂mu, poissonFullContactRun n (fun c => X c omega) =
      preassignedRun n (firstArrivalArray (fun c => X c omega)) := by
  have hh := preassignedClockLaw_positive (show (0 : ℝ) < r by exact_mod_cast hr) n
  rw [← independent_firstArrivalArray_law mu n r hr X hX hindep hrecovery hcontact] at hh
  have hp := ae_of_ae_map
    ((measurable_firstArrivalArray n).comp (Measurable.of_eval hX)).aemeasurable hh
  filter_upwards [hp] with omega homega
  exact poissonFullContactRun_eq_preassigned n (fun c => X c omega) homega

theorem aemeasurable_poissonFullContactTreePath
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (n : ℕ) (r : ℝ≥0) (hr : 0 < r)
    (X : (c : ClockSlot n) → Ω → ClockDatum c)
    (hX : ∀ c, Measurable (X c)) (hindep : iIndepFun X mu)
    (hrecovery : ∀ v : Individual n, mu.map (X (v, none)) = expMeasure 1)
    (hcontact : ∀ v w : Individual n,
      PoissonContact.HasPoissonCounts (mu.map (X (v, some w))) r) :
    AEMeasurable (fun omega => poissonFullContactTreePath n (fun c => X c omega)) mu := by
  have hm : Measurable (fun omega => preassignedTreePath n
      (firstArrivalArray (fun c => X c omega))) :=
    (measurable_preassignedTreePath n).comp
      ((measurable_firstArrivalArray n).comp (Measurable.of_eval hX))
  apply hm.aemeasurable.congr
  filter_upwards [independent_poisson_fullContactRun_eq_preassigned
    mu n r hr X hX hindep hrecovery hcontact] with omega homega
  funext k
  exact (congrArg (fun H : ℕ → ClockFrame n => (H k).population.project) homega).symm

/-- Full equality of infinite genealogical path measures for the actual
next-contact protocol, with source-level independence and marginal laws. -/
theorem independent_poisson_fullContact_tree_fullLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (n : ℕ) (r : ℝ≥0) (hr : 0 < r)
    (X : (c : ClockSlot n) → Ω → ClockDatum c)
    (hX : ∀ c, Measurable (X c)) (hindep : iIndepFun X mu)
    (hrecovery : ∀ v : Individual n, mu.map (X (v, none)) = expMeasure 1)
    (hcontact : ∀ v w : Individual n,
      PoissonContact.HasPoissonCounts (mu.map (X (v, some w))) r) :
    mu.map (fun omega => poissonFullContactTreePath n (fun c => X c omega)) =
      treeFullLaw r n := by
  calc
    _ = mu.map (fun omega => preassignedTreePath n
        (firstArrivalArray (fun c => X c omega))) := by
      apply Measure.map_congr
      filter_upwards [independent_poisson_fullContactRun_eq_preassigned
        mu n r hr X hX hindep hrecovery hcontact] with omega homega
      funext k
      exact congrArg (fun H : ℕ → ClockFrame n => (H k).population.project) homega
    _ = _ := independent_poisson_tree_fullLaw mu n r hr X hX hindep hrecovery hcontact

/-- The literal susceptible and infectious label counts of the full
contact protocol have the complete stopped count-chain law in the paper. -/
theorem independent_poisson_fullContact_counts_fullLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (n : ℕ) (r : ℝ≥0) (hr : 0 < r)
    (X : (c : ClockSlot n) → Ω → ClockDatum c)
    (hX : ∀ c, Measurable (X c)) (hindep : iIndepFun X mu)
    (hrecovery : ∀ v : Individual n, mu.map (X (v, none)) = expMeasure 1)
    (hcontact : ∀ v w : Individual n,
      PoissonContact.HasPoissonCounts (mu.map (X (v, some w))) r) :
    mu.map (fun omega k =>
      let z := (poissonFullContactRun n (fun c => X c omega) k).population
      (⟨z.susceptible.card, z.active.card⟩ : Counts)) = countsFullLaw r n := by
  have hcount : Measurable (fun H : ℕ → TreeState => fun k => (H k).counts) :=
    Measurable.of_eval fun k => (measurable_of_countable TreeState.counts).comp
      (measurable_pi_apply k)
  have hpath : Measurable (fun omega => preassignedTreePath n
      (firstArrivalArray (fun c => X c omega))) :=
    (measurable_preassignedTreePath n).comp
      ((measurable_firstArrivalArray n).comp (Measurable.of_eval hX))
  calc
    _ = mu.map (fun omega k =>
        (preassignedTreePath n (firstArrivalArray (fun c => X c omega)) k).counts) := by
      apply Measure.map_congr
      filter_upwards [independent_poisson_fullContactRun_eq_preassigned
        mu n r hr X hX hindep hrecovery hcontact] with omega homega
      funext k
      rw [congrFun homega k]
      have hv := (preassignedRun_population_valid n
        (firstArrivalArray (fun c => X c omega)) k).active_card
      simp only [preassignedTreePath, PopulationState.project, TreeState.counts, hv]
    _ = (treeFullLaw r n).map (fun H k => (H k).counts) := by
      rw [← independent_poisson_tree_fullLaw mu n r hr X hX hindep hrecovery hcontact,
        Measure.map_map hcount hpath]
      rfl
    _ = countsFullLaw r n := map_treeFullLaw_counts r n

/-- Finite absorption of the entire physical clock frame, proved for the
whole-arrival-path protocol rather than just its tree projection. -/
theorem independent_poisson_fullContact_absorbed_by
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (n : ℕ) (r : ℝ≥0) (hr : 0 < r)
    (X : (c : ClockSlot n) → Ω → ClockDatum c)
    (hX : ∀ c, Measurable (X c)) (hindep : iIndepFun X mu)
    (hrecovery : ∀ v : Individual n, mu.map (X (v, none)) = expMeasure 1)
    (hcontact : ∀ v w : Individual n,
      PoissonContact.HasPoissonCounts (mu.map (X (v, some w))) r) :
    ∀ᵐ omega ∂mu,
      let H := poissonFullContactRun n (fun c => X c omega)
      (H (2 * n + 1)).population.active = ∅ ∧
        ∀ k ≥ 2 * n + 1, H k = H (2 * n + 1) := by
  filter_upwards [independent_poisson_fullContactRun_eq_preassigned
    mu n r hr X hX hindep hrecovery hcontact,
    independent_poisson_absorbed_by mu n r hr X hX hindep hrecovery hcontact]
      with omega heq habs
  simpa only [heq] using habs

/-- Actual terminal genealogies for the full contact protocol have exactly
the probability measure used by the main infection-tree limit statements. -/
theorem independent_poisson_fullContact_terminal_tree_law
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (n : ℕ) (r : ℝ≥0) (hr : 0 < r)
    (X : (c : ClockSlot n) → Ω → ClockDatum c)
    (hX : ∀ c, Measurable (X c)) (hindep : iIndepFun X mu)
    (hrecovery : ∀ v : Individual n, mu.map (X (v, none)) = expMeasure 1)
    (hcontact : ∀ v w : Individual n,
      PoissonContact.HasPoissonCounts (mu.map (X (v, some w))) r) :
    mu.map (fun omega => PlaneForward.shape
      (poissonFullContactRun n (fun c => X c omega) (2 * n + 1)).population.tree) =
      (embeddedTerminalTreeLaw r n : Measure PlaneTree.Tree) := by
  calc
    _ = mu.map (fun omega => PlaneForward.shape
        (preassignedRun n (firstArrivalArray (fun c => X c omega))
          (2 * n + 1)).population.tree) := by
      apply Measure.map_congr
      filter_upwards [independent_poisson_fullContactRun_eq_preassigned
        mu n r hr X hX hindep hrecovery hcontact] with omega homega
      exact congrArg (fun H : ℕ → ClockFrame n =>
        PlaneForward.shape (H (2 * n + 1)).population.tree) homega
    _ = _ := independent_poisson_terminal_tree_law mu n r hr X hX hindep hrecovery hcontact

end Freezing1.SIR
