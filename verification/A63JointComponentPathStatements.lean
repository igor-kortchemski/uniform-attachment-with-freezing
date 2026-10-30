module

import Freezing1.ForwardComponentUrnPathMaximal

/-! Authored expanded checks of the new joint component-path bridge.
This is not the independent review of the earlier endpoint-only route. -/

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
open Freezing1 Freezing1.Forward Freezing1.ForwardInfiniteHistory

set_option backward.isDefEq.respectTransparency false

example {x : SignSequence} {a k cut : ℕ} {s : State}
    (hs : HasHistory x a s) (hcut : cut ≤ a)
    (hτ : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) (r : ℕ) :
    (Forward.continuationLaw x a k s).map
      (SignedUrn.record (fun i q => componentPopulation (truncateAt q i) cut r) a k) =
        SignedUrn.pathLaw (activeCount x) a k (componentPopulation s cut r) :=
  continuationLaw_componentPrefixRecord hs hcut hτ r

example {x : SignSequence} {a b : ℕ} {s : State}
    (hs : HasHistory x a s) (hab : a ≤ b) (hb : PositiveThrough x b)
    {r : ℕ} (hr : r ∈ s.active) :
    (Forward.continuationLaw x a (b - a) s).map
      (SignedUrn.record (fun i q => componentPopulation (truncateAt q i) a r) a (b - a)) =
        SignedUrn.pathLaw (SignedUrn.positiveExtensionPopulation x a b) 0 (b - a) 1 :=
  positiveExtension_componentPrefixRecord hs hab hb hr

example (x : SignSequence) (a : ℕ) :
    fullLaw x = ((fullLaw x).map (fun H (i : Finset.Iic a) => H i.val)).bind
      (fun past => Kernel.traj (X := fun _ => State) (historyKernel x) a past) :=
  fullLaw_bind_continuationHistoryLaw x a

example (x : SignSequence) (a k cut r : ℕ) (past : (i : Finset.Iic a) → State)
    (hs : HasHistory x a (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩))
    (hcut : cut ≤ a) (hτ : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) :
    (Kernel.traj (X := fun _ => State) (historyKernel x) a past).map
      (SignedUrn.record (fun i (H : History) => componentPopulation (H i) cut r) a k) =
        SignedUrn.pathLaw (activeCount x) a k
          (componentPopulation (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩) cut r) :=
  continuationHistoryLaw_component_record x a k cut r past hs hcut hτ

example (x : SignSequence) {a b : ℕ} (hab : a ≤ b) (hb : PositiveThrough x b)
    (past : (i : Finset.Iic a) → State)
    (hs : HasHistory (positiveExtension x b) a (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩))
    {r : ℕ} (hr : r ∈ (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩).active) :
    ∀ k : ℕ, (continuationHistoryLaw (positiveExtension x b) a past).map
      (SignedUrn.record (fun i (H : History) => componentPopulation (H (a + i)) a r) 0 k) =
        SignedUrn.pathLaw (SignedUrn.positiveExtensionPopulation x a b) 0 k 1 := by
  intro k
  exact (positiveExtension_actual_component_hasPathLaws x hab hb past hs hr k).map_eq

example (x : SignSequence) {a b : ℕ} (hab : a ≤ b) (hb : PositiveThrough x b) :
    ∀ᵐ past ∂(fullLaw x).map (fun H (i : Finset.Iic a) => H i.val),
      ∀ r ∈ (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩).active, ∀ k : ℕ,
        (continuationHistoryLaw (positiveExtension x b) a past).map
          (SignedUrn.record (fun i (H : History) => componentPopulation (H (a + i)) a r) 0 k) =
            SignedUrn.pathLaw (SignedUrn.positiveExtensionPopulation x a b) 0 k 1 := by
  exact (positiveExtension_original_component_pathLaws x hab hb).mono
    fun _ h r hr k => (h r hr k).map_eq

example (x : SignSequence) {a b : ℕ} (hab : a ≤ b) :
    fullLaw (positiveExtension x b) =
      ((fullLaw x).map (fun H (i : Finset.Iic a) => H i.val)).bind
        (fun past => Kernel.traj (X := fun _ => State)
          (historyKernel (positiveExtension x b)) a past) :=
  positiveExtension_bind_original_prefix x hab

example (x : SignSequence) {a b : ℕ} (hab : a < b) (hb : PositiveThrough x b)
    (past : (i : Finset.Iic a) → State)
    (hs : HasHistory (positiveExtension x b) a (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩))
    {r : ℕ} (hr : r ∈ (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩).active)
    {t : ℝ} (ht : 0 ≤ t) :
    (continuationHistoryLaw (positiveExtension x b) a past).real {H |
      ∃ i : ℕ, 1 ≤ i ∧ t / (activeCount x a : ℝ) <
        |(((H (a + i)).active.filter fun v => cutAncestor (H (a + i)) a v = r).card : ℝ) /
          SignedUrn.positiveExtensionPopulation x a b i - (activeCount x a : ℝ)⁻¹|} ≤
      2 * Real.exp (-((t ^ 2 / 4) * (activeCount x a : ℝ)⁻¹) /
        (SignedUrn.infiniteSquareBudget (SignedUrn.positiveExtensionPopulation x a b) + t *
          max (SignedUrn.infiniteSquareBudget (SignedUrn.positiveExtensionPopulation x a b))
            (SignedUrn.sourceEpsilon x a b hab))) := by
  simpa only [componentPopulation, componentActive, Int.cast_natCast] using
    positiveExtension_actual_component_infinite_maximal x hab hb past hs hr ht

#print axioms SignedUrn.pathLaw_shift
#print axioms SignedUrn.pathLaw_congr_population
#print axioms continuationLaw_componentPrefixRecord
#print axioms positiveExtension_componentPrefixRecord
#print axioms fullLaw_bind_continuationHistoryLaw
#print axioms measurable_actualComponentRecord
#print axioms continuationHistoryLaw_preserves_prefix
#print axioms actual_partial_map_next
#print axioms continuationHistoryLaw_component_record
#print axioms positiveExtension_bind_original_prefix
#print axioms positiveExtension_actual_component_hasPathLaws
#print axioms positiveExtension_original_component_pathLaws
#print axioms positiveExtension_actual_component_infinite_maximal
