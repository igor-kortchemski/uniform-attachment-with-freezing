module

public import Freezing1.TaggedPopulationKernel
public import Freezing1.ForwardCutUpdates
public import Freezing1.ForwardComponentContinuation

/-!
# The tagged multiset is a pushforward of the actual forward tree

The root tag and height of each active vertex are computed from the true
time-cut parents. Uniform vertex sampling maps to uniform sampling of multiset
occurrences, so repeated tag-height pairs carry their correct multiplicity.
The equality holds conditionally on every valid starting tree, up to and
including the extinction endpoint.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped Classical ENNReal

noncomputable def taggedPopulation (s : State) (a : ℕ) : TaggedPopulation.State :=
  s.active.val.map (fun v => (cutAncestor s a v, cutHeight s a v))

theorem taggedPopulation_card (s : State) (a : ℕ) :
    (taggedPopulation s a).card = s.active.card := Multiset.card_map _ _

theorem taggedPopulation_at_cut {a : ℕ} {s : State} (hs : ValidAt a s) :
    taggedPopulation s a = TaggedPopulation.initial s.active := by
  apply Multiset.map_congr rfl
  intro v hv
  have hvle := hs.vertices_le v (hs.active_subset hv)
  rw [cutAncestor_of_le s a v hvle]
  exact congrArg (fun h => (v, h)) (cutHeightAux_eq_zero_of_le s a _ v hvle)

theorem taggedPopulation_step {n : ℕ} {s : State} (hs : ValidAt n s)
    {a p : ℕ} (ha : a ≤ n) (hp : p ∈ s.active) (sign : Bool) :
    taggedPopulation (step s (n + 1) sign p) a =
      TaggedPopulation.step (taggedPopulation s a) sign
        (cutAncestor s a p, cutHeight s a p) := by
  have hmap : s.active.val.map
      (fun v => (cutAncestor (attach s (n + 1) p) a v,
        cutHeight (attach s (n + 1) p) a v)) = taggedPopulation s a := by
    apply Multiset.map_congr rfl
    intro v hv
    rw [cutAncestor_attach_old hs a p (hs.active_subset hv),
      cutHeight_attach_old hs a p (hs.active_subset hv)]
  rw [step, ite_eq_left hp]
  cases sign
  · simp only [Bool.false_eq_true, ↓reduceIte]
    change ((s.active.erase p).val.map
      (fun v => (cutAncestor (freeze s (n + 1) p) a v,
        cutHeight (freeze s (n + 1) p) a v))) =
      (taggedPopulation s a).erase (cutAncestor s a p, cutHeight s a p)
    rw [Finset.erase_val]
    have hfreeze : (s.active.val.erase p).map
        (fun v => (cutAncestor (freeze s (n + 1) p) a v,
          cutHeight (freeze s (n + 1) p) a v)) =
        (s.active.val.erase p).map (fun v => (cutAncestor s a v, cutHeight s a v)) := by
      apply Multiset.map_congr rfl
      intro v _
      rw [cutAncestor_freeze, cutHeight_freeze]
    rw [hfreeze, Multiset.map_erase_of_mem _ _ hp]
    rfl
  · have hnew : n + 1 ∉ s.active := by
      intro hv
      have := hs.vertices_le _ (hs.active_subset hv)
      omega
    change ((insert (n + 1) s.active).val.map
      (fun v => (cutAncestor (attach s (n + 1) p) a v,
        cutHeight (attach s (n + 1) p) a v))) = _
    rw [Finset.insert_val_of_notMem hnew, Multiset.map_cons, hmap,
      cutAncestor_attach_new hs ha hp, cutHeight_attach_new hs ha hp]
    rfl

/-- The exact one-step law, retaining all active-vertex multiplicities. -/
theorem transitionLaw_taggedPopulation {n : ℕ} {s : State} (hs : ValidAt n s)
    {a : ℕ} (ha : a ≤ n) (sign : Bool) (hne : s.active.Nonempty) :
    (transitionLaw s (n + 1) sign).map (fun t => taggedPopulation t a) =
      TaggedPopulation.transitionLaw (taggedPopulation s a) sign := by
  have hnot : taggedPopulation s a ≠ 0 := by
    intro he
    have hc := taggedPopulation_card s a
    rw [he, Multiset.card_zero] at hc
    exact hne.card_pos.ne' hc.symm
  rw [transitionLaw, ite_eq_left hne, TaggedPopulation.transitionLaw, ite_eq_right hnot,
    Measure.map_map measurable_from_top (by fun_prop)]
  have hsamp := map_uniformFinset_eq_multisetUniform s.active
    (fun v => (cutAncestor s a v, cutHeight s a v)) (measurable_of_countable _)
  change (Measure.uniformOfFinset s.active).map
    (fun v => (cutAncestor s a v, cutHeight s a v)) = multisetUniform (taggedPopulation s a) at hsamp
  rw [← hsamp, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  apply Measure.map_congr
  have hmem : ∀ᵐ p ∂Measure.uniformOfFinset s.active, p ∈ s.active := by
    rw [← multisetUniform_finset]
    exact multisetUniform_ae_mem _
  filter_upwards [hmem] with p hp
  exact taggedPopulation_step hs ha hp sign

/-- Every genuine conditional future has exactly the abstract tagged
population law; no exchangeability or independence premise is inserted. -/
theorem continuationLaw_taggedPopulation {x : SignSequence} {b k a : ℕ} {s : State}
    (hd : PhaseData x b s) (ha : a ≤ b)
    (hτ : ((b + k : ℕ) : ℕ∞) ≤ extinctionTime x) :
    (continuationLaw x b k s).map (fun t => taggedPopulation t a) =
      TaggedPopulation.continuationLaw x b k (taggedPopulation s a) := by
  induction k generalizing b s with
  | zero => simp [continuationLaw, TaggedPopulation.continuationLaw]
  | succ k ih =>
    have hbτ : (b : ℕ∞) < extinctionTime x :=
      lt_of_lt_of_le (by exact_mod_cast (show b < b + (k + 1) by omega)) hτ
    have hpos := ((lt_extinctionTime_iff x b).mp hbτ) b le_rfl
    have hne : s.active.Nonempty := by
      apply Finset.card_pos.mp
      have hc := hd.count
      omega
    have hnext := transitionLaw_phaseData hd hne
    have hend : (((b + 1) + k : ℕ) : ℕ∞) ≤ extinctionTime x := by
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hτ
    rw [continuationLaw, Measure.map_bind measurable_from_top.aemeasurable
      measurable_from_top.aemeasurable]
    calc
      _ = (transitionLaw s (b + 1) (x (b + 1))).bind
          (fun t => TaggedPopulation.continuationLaw x (b + 1) k (taggedPopulation t a)) := by
        apply Measure.bind_congr_right
        filter_upwards [hnext] with t ht
        exact ih ht (ha.trans (Nat.le_succ b)) hend
      _ = ((transitionLaw s (b + 1) (x (b + 1))).map
          (fun t => taggedPopulation t a)).bind
          (TaggedPopulation.continuationLaw x (b + 1) k) := by
        rw [Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
      _ = _ := by
        rw [transitionLaw_taggedPopulation hd.valid ha _ hne, TaggedPopulation.continuationLaw]

theorem continuationLaw_taggedPopulation_at_cut {x : SignSequence} {a k : ℕ} {s : State}
    (hd : PhaseData x a s) (hτ : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) :
    (continuationLaw x a k s).map (fun t => taggedPopulation t a) =
      TaggedPopulation.continuationLaw x a k (TaggedPopulation.initial s.active) := by
  rw [continuationLaw_taggedPopulation hd le_rfl hτ, taggedPopulation_at_cut hd.valid]

end Freezing1.Forward
