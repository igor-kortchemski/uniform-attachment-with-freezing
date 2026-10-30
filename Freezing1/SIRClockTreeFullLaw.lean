module

public import Freezing1.SIRClockTreeProjection
public import Freezing1.SIRPoissonClockArray
public import Freezing1.SIRAbsorption

/-!
# The original independent clocks give the complete embedded SIR tree law

The actual run uses one fixed array of independent lifetimes and directed
first-contact delays. Its entire genealogical path has the already defined
embedded tree law. Independent Poisson arrival paths reduce to this same
array through their proved first-arrival distributions.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def preassignedTreePath (n : ℕ) (omega : ClockArray n) (k : ℕ) : TreeState :=
  (preassignedRun n omega k).population.project

theorem measurable_preassignedTreePath (n : ℕ) : Measurable (preassignedTreePath n) := by
  apply Measurable.of_eval
  intro k
  exact (measurable_of_countable (PopulationState.project (n := n))).comp
    (measurable_fst.comp
      ((measurable_pi_apply k).comp (measurable_preassignedRun n)))

noncomputable def replayTreeState (n : ℕ) (w : ClockWord n) : TreeState := (replayPopulation n w).project

theorem clockWordKernel_project (r : ℝ) (hr : 0 < r) (n : ℕ) (w : ClockWord n) :
    (clockWordKernel r hr n w).map (replayTreeState n) =
      treeKernel ⟨r, hr.le⟩ (replayTreeState n w) := by
  change ((clockChoiceLaw r (replayPopulation n w)).map (fun c => c :: w)).map
    (replayTreeState n) = _
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  exact clockChoiceLaw_project hr (replayPopulation_valid n w)

theorem clockWordFullLaw_project (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (clockWordFullLaw r hr n).map (fun H k => replayTreeState n (H k)) =
      treeFullLaw ⟨r, hr.le⟩ n := by
  have hzero : replayTreeState n [] = initialTreeState n := project_initialPopulation n
  change (CountableMarkovChain.fullLaw (clockWordKernel r hr n) []).map
    (fun H k => replayTreeState n (H k)) = _
  rw [show treeFullLaw ⟨r, hr.le⟩ n =
      CountableMarkovChain.fullLaw (treeKernel ⟨r, hr.le⟩) (replayTreeState n []) by
    rw [hzero]; rfl]
  apply CountableMarkovChain.map_fullLaw_of_ae_intertwining
  intro k
  exact Filter.Eventually.of_forall fun H => clockWordKernel_project r hr n (H k)

/-- A complete-path identity proved for the actual original static array,
including absorption; the array is never resampled. -/
theorem preassigned_clock_tree_fullLaw {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (preassignedClockLaw r n).map (preassignedTreePath n) = treeFullLaw ⟨r, hr.le⟩ n := by
  have hproject : Measurable (fun H : ℕ → ClockWord n =>
      fun k => replayTreeState n (H k)) :=
    Measurable.of_eval fun k => (measurable_of_countable (replayTreeState n)).comp
      (measurable_pi_apply k)
  calc
    _ = ((preassignedClockLaw r n).map (preassignedWord n)).map
        (fun H k => replayTreeState n (H k)) := by
      rw [Measure.map_map hproject
        (Measurable.of_eval (fun k => measurable_preassignedWord n k))]
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun omega => by
        funext k
        exact congrArg PopulationState.project (preassignedRun_population_replay n omega k)
    _ = _ := by rw [preassigned_clock_word_fullLaw hr n, clockWordFullLaw_project]

theorem clockFrameStep_of_active_empty {n : ℕ} (F : ClockFrame n) (omega : ClockArray n)
    (ha : F.population.active = ∅) : clockFrameStep F omega = F := by
  have hn : firstLiveClock F.population (remainingClock F omega) = none := by
    rw [firstLiveClock_none_iff]
    rintro ⟨c, hc⟩
    have hm := (Finset.mem_product.mp hc.1).1
    simp only [ha, Finset.notMem_empty] at hm
  simp only [clockFrameStep, hn]

/-- The actual clock frame, including its physical time and infection-time
record, is absorbed by the same proved finite event horizon. -/
theorem preassigned_clock_absorbed_by {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ∀ᵐ omega ∂preassignedClockLaw r n,
      (preassignedRun n omega (2 * n + 1)).population.active = ∅ ∧
        ∀ k ≥ 2 * n + 1,
          preassignedRun n omega k = preassignedRun n omega (2 * n + 1) := by
  have hh := treeFullLaw_absorbed_by ⟨r, hr.le⟩ n
  rw [← preassigned_clock_tree_fullLaw hr n] at hh
  have hactual := ae_of_ae_map (measurable_preassignedTreePath n).aemeasurable hh
  filter_upwards [hactual] with omega homega
  have hcard := (preassignedRun_population_valid n omega (2 * n + 1)).active_card
  have hactive : (preassignedRun n omega (2 * n + 1)).population.active = ∅ := by
    apply Finset.card_eq_zero.mp
    rw [← hcard]
    exact Finset.card_eq_zero.mpr homega.1
  refine ⟨hactive, ?_⟩
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [preassignedRun, ih, clockFrameStep_of_active_empty _ _ hactive]

/-- Source-level independent recovery periods and directed Poisson contact
arrival paths give the actual embedded tree process at every event, jointly
on the complete history. The first-arrival law is derived, not assumed. -/
theorem independent_poisson_tree_fullLaw {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (n : ℕ) (r : ℝ≥0) (hr : 0 < r)
    (X : (c : ClockSlot n) → Ω → ClockDatum c)
    (hX : ∀ c, Measurable (X c)) (hindep : iIndepFun X mu)
    (hrecovery : ∀ v : Individual n, mu.map (X (v, none)) = expMeasure 1)
    (hcontact : ∀ v w : Individual n,
      PoissonContact.HasPoissonCounts (mu.map (X (v, some w))) r) :
    mu.map (fun omega => preassignedTreePath n
      (firstArrivalArray (fun c => X c omega))) = treeFullLaw r n := by
  have harray : Measurable (fun omega => firstArrivalArray (fun c => X c omega)) :=
    (measurable_firstArrivalArray n).comp (Measurable.of_eval hX)
  change mu.map (preassignedTreePath n ∘
    (fun omega => firstArrivalArray (fun c => X c omega))) = treeFullLaw r n
  rw [← Measure.map_map (measurable_preassignedTreePath n) harray,
    independent_firstArrivalArray_law mu n r hr X hX hindep hrecovery hcontact]
  exact preassigned_clock_tree_fullLaw (show (0 : ℝ) < r by exact_mod_cast hr) n

/-- Almost-sure finite absorption for the actual source-level independent
Poisson-contact and recovery coordinates, including the whole clock frame. -/
theorem independent_poisson_absorbed_by {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (n : ℕ) (r : ℝ≥0) (hr : 0 < r)
    (X : (c : ClockSlot n) → Ω → ClockDatum c)
    (hX : ∀ c, Measurable (X c)) (hindep : iIndepFun X mu)
    (hrecovery : ∀ v : Individual n, mu.map (X (v, none)) = expMeasure 1)
    (hcontact : ∀ v w : Individual n,
      PoissonContact.HasPoissonCounts (mu.map (X (v, some w))) r) :
    ∀ᵐ omega ∂mu,
      let array := firstArrivalArray (fun c => X c omega)
      (preassignedRun n array (2 * n + 1)).population.active = ∅ ∧
        ∀ k ≥ 2 * n + 1, preassignedRun n array k = preassignedRun n array (2 * n + 1) := by
  have hh := preassigned_clock_absorbed_by (show (0 : ℝ) < r by exact_mod_cast hr) n
  rw [← independent_firstArrivalArray_law mu n r hr X hX hindep hrecovery hcontact] at hh
  exact ae_of_ae_map
    ((measurable_firstArrivalArray n).comp (Measurable.of_eval hX)).aemeasurable hh

/-- The genealogical tree at the actual end of the original contact process
has exactly the terminal law used in the main local-limit statements. -/
theorem independent_poisson_terminal_tree_law {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (n : ℕ) (r : ℝ≥0) (hr : 0 < r)
    (X : (c : ClockSlot n) → Ω → ClockDatum c)
    (hX : ∀ c, Measurable (X c)) (hindep : iIndepFun X mu)
    (hrecovery : ∀ v : Individual n, mu.map (X (v, none)) = expMeasure 1)
    (hcontact : ∀ v w : Individual n,
      PoissonContact.HasPoissonCounts (mu.map (X (v, some w))) r) :
    mu.map (fun omega => PlaneForward.shape
      (preassignedRun n (firstArrivalArray (fun c => X c omega))
        (2 * n + 1)).population.tree) =
      (embeddedTerminalTreeLaw r n : Measure PlaneTree.Tree) := by
  change _ = (treeFullLaw r n).map
    (fun H => PlaneForward.shape (H (2 * n + 1)).tree)
  have hterm : Measurable (fun H : ℕ → TreeState =>
      PlaneForward.shape (H (2 * n + 1)).tree) :=
    (measurable_of_countable (fun z : TreeState => PlaneForward.shape z.tree)).comp
      (measurable_pi_apply (2 * n + 1))
  have hpath : Measurable (fun omega => preassignedTreePath n
      (firstArrivalArray (fun c => X c omega))) :=
    (measurable_preassignedTreePath n).comp
      ((measurable_firstArrivalArray n).comp (Measurable.of_eval hX))
  rw [← independent_poisson_tree_fullLaw mu n r hr X hX hindep hrecovery hcontact,
    Measure.map_map hterm hpath]
  rfl

end Freezing1.SIR
