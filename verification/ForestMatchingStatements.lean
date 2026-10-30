module

public import Freezing1.ForwardForestBareMatching
public import Freezing1.ForwardForestMaximumStatistics
public import Freezing1.ForwardForestPopulationLaw
public import Freezing1.ForwardForestRematchingAction
public import Freezing1.ForwardForestRootMatchingEquiv
public import Freezing1.ForwardBlockHeightAncestor
public import Freezing1.TaggedPopulationSlotMoments

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
open Freezing1 Freezing1.Forward

/- Authored exact-type and closure checks; independent review is separate. -/

example {x : SignSequence} {a k : ℕ} {s : State} (hs : PhaseData x a s)
    (hn : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) :
    (continuationLaw x a k s).map (fun t => forestCut t a) =
      continuationLaw x a k (forestInitial s.active) := continuationLaw_forestCut_at_cut hs hn

example (x : SignSequence) {a b : ℕ} (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) :
    (treeLaw x b).map (fun t => (truncateAt t a, slotForest t a)) =
      (treeLaw x a).prod (forestSlotLaw x a (b - a) (activeCount x a).toNat) :=
  treeLaw_prefix_slotForest x hab hb

example (x : SignSequence) {a b : ℕ} (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) :
    IndepFun (fun t => truncateAt t a)
      (fun t => bareSlotOrbit (activeCount x a).toNat (slotForest t a)) (treeLaw x b) :=
  indepFun_prefix_bareForest x hab hb

example {x : SignSequence} {a b : ℕ} {s t : State} (hs : HasHistory x b s)
    (ht : HasHistory x b t) (hb : (b : ℕ∞) ≤ extinctionTime x)
    (hp : truncateAt s a = truncateAt t a) (hF : forestCut s a = forestCut t a) :
    s = t := eq_of_prefix_forestCut hs ht hb hp hF

example (x : SignSequence) {a b : ℕ} (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x)
    (σ : Equiv.Perm (Fin (activeCount x a).toNat)) :
    MeasurePreserving (rematchState x a b σ) (treeLaw x b) (treeLaw x b) :=
  ⟨measurable_from_top, map_treeLaw_rematchState x hab hb σ⟩

example (x : SignSequence) {a b : ℕ} (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x)
    (σ : Equiv.Perm (Fin (activeCount x a).toNat)) :
    (fun q => (truncateAt (rematchState x a b σ q) a,
      bareSlotOrbit (activeCount x a).toNat (slotForest (rematchState x a b σ q) a))) =ᵐ[treeLaw x b]
      (fun q => (truncateAt q a, bareSlotOrbit (activeCount x a).toNat (slotForest q a))) :=
  pastBareForest_rematchState x hab hb σ

#print axioms Freezing1.Forward.continuationLaw_forestCut_at_cut
#print axioms Freezing1.Forward.treeLaw_prefix_forestCut
#print axioms Freezing1.exists_canonical_root_relabel
#print axioms Freezing1.Forward.treeLaw_prefix_slotForest
#print axioms Freezing1.Forward.indepFun_prefix_slotForest
#print axioms Freezing1.Forward.forestSlotLaw_uniform_matching_observation
#print axioms Freezing1.Forward.eq_of_prefix_forestCut
#print axioms Freezing1.Forward.rootMatchingParametrization
#print axioms Freezing1.Forward.treeLaw_uniform_root_matching
#print axioms Freezing1.Forward.star_activity_counterexample
#print axioms Freezing1.Forward.slotStarForest_actual
#print axioms Freezing1.Forward.indepFun_prefix_bareForest
#print axioms Freezing1.Forward.treeLaw_uniform_root_matching_bare
#print axioms Freezing1.Forward.blockHeight_eq_cutHeight_ancestor
#print axioms Freezing1.Forward.bareForestTallCount_actual
#print axioms Freezing1.Forward.bareForestComponentMaximum_actual
#print axioms Freezing1.Forward.forestSlotLaw_taggedPopulation
#print axioms Freezing1.Forward.rematchState_ae_spec
#print axioms Freezing1.Forward.map_treeLaw_rematchState
#print axioms Freezing1.Forward.pastBareForest_rematchState
#print axioms Freezing1.TaggedPopulation.integral_goodTall_slot
#print axioms Freezing1.TaggedPopulation.variance_goodTall_slot_le
