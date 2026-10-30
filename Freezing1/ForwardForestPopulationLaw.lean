module

public import Freezing1.ForwardForestTaggedProjection
public import Freezing1.ForwardForestSlots
public import Freezing1.TaggedPopulationCounts
public import Freezing1.ForwardGoodChainPropagation

/-! The entire genuine tagged-population law is a projection of the full slot forest. -/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

theorem slotForest_active_card (s : State) (a : ℕ) : (slotForest s a).active.card = s.active.card := by
  change (s.active.image (rootNormalizer a (cutRoots s a))).card = s.active.card
  exact Finset.card_image_of_injective _ (rootNormalizer a (cutRoots s a)).injective

theorem forestSlotLaw_taggedPopulation_of_past {x : SignSequence} {a k : ℕ} {past : State}
    (hpast : HasHistory x a past) (hn : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) :
    (forestSlotLaw x a k past.active.card).map (fun F => taggedPopulation F a) =
      TaggedPopulation.continuationLaw x a k (TaggedPopulation.initial (Finset.range past.active.card)) := by
  let e := rootNormalizer a past.active
  have hroots : past.active.image e = Finset.range past.active.card :=
    rootNormalizer_image a past.active (fun r hr => hpast.current.valid.vertices_le r
      (hpast.current.valid.active_subset hr))
  rw [← continuationLaw_slotForest hpast hn, Measure.map_map measurable_from_top measurable_from_top]
  calc
    _ = (continuationLaw x a k past).map (fun q => TaggedPopulation.relabel e (taggedPopulation q a)) := by
      apply Measure.map_congr
      filter_upwards [continuationLaw_hasHistory hpast hn, continuationLaw_truncate_self hpast hn]
        with q hq hprefix
      have hr : cutRoots q a = past.active := congrArg State.active hprefix
      dsimp only [Function.comp_def]
      rw [slotForest, hr, taggedPopulation_relabel e _ a (rootNormalizer_future a past.active),
        taggedPopulation_forestCut hq hn a]
    _ = ((continuationLaw x a k past).map (fun q => taggedPopulation q a)).map (TaggedPopulation.relabel e) := by
      rw [Measure.map_map measurable_from_top measurable_from_top]
      rfl
    _ = _ := by
      rw [continuationLaw_taggedPopulation_at_cut hpast.current hn,
        TaggedPopulation.map_continuationLaw_relabel, TaggedPopulation.relabel_initial, hroots]

theorem forestSlotLaw_taggedPopulation (x : SignSequence) (a k : ℕ)
    (hn : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) :
    (forestSlotLaw x a k (activeCount x a).toNat).map (fun F => taggedPopulation F a) =
      TaggedPopulation.continuationLaw x a k (TaggedPopulation.initial (Finset.range (activeCount x a).toNat)) := by
  have haτ : (a : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast (Nat.le_add_right a k) : (a : ℕ∞) ≤ (a + k : ℕ)).trans hn
  obtain ⟨past, hpast⟩ := (treeLaw_hasHistory x a haτ).exists
  have hcard : past.active.card = (activeCount x a).toNat := by
    have hh := congrArg Int.toNat hpast.current.count
    simpa only [Int.toNat_natCast] using hh
  simpa only [hcard] using forestSlotLaw_taggedPopulation_of_past hpast hn

theorem forestSlotLaw_tagsIn (x : SignSequence) (a k : ℕ)
    (hn : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ F ∂forestSlotLaw x a k (activeCount x a).toNat,
      TaggedPopulation.TagsIn (Finset.range (activeCount x a).toNat) (taggedPopulation F a) := by
  have hh := TaggedPopulation.continuationLaw_tagsIn x a k
    (TaggedPopulation.tagsIn_initial (Finset.range (activeCount x a).toNat))
  rw [← forestSlotLaw_taggedPopulation x a k hn] at hh
  exact (ae_map_iff (f := fun F : State => taggedPopulation F a)
    measurable_from_top.aemeasurable (by trivial)).mp hh

theorem treeLaw_slotForest_tagsIn (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ q ∂treeLaw x b, TaggedPopulation.TagsIn (Finset.range (activeCount x a).toNat)
      (taggedPopulation (slotForest q a) a) := by
  have he : a + (b - a) = b := Nat.add_sub_of_le hab
  have hn : ((a + (b - a) : ℕ) : ℕ∞) ≤ extinctionTime x := by rw [he]; exact hb
  have hh := forestSlotLaw_tagsIn x a (b - a) hn
  rw [← treeLaw_slotForest x hab hb] at hh
  exact (ae_map_iff (f := fun q : State => slotForest q a)
    measurable_from_top.aemeasurable
    (p := fun F : State => TaggedPopulation.TagsIn (Finset.range (activeCount x a).toNat)
      (taggedPopulation F a)) (by trivial)).mp hh

theorem forestSlotLaw_active_card_le (x : SignSequence) (a k : ℕ)
    (hn : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ F ∂forestSlotLaw x a k (activeCount x a).toNat, F.active.card ≤ a + k + 1 := by
  have haτ : (a : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast (Nat.le_add_right a k) : (a : ℕ∞) ≤ (a + k : ℕ)).trans hn
  obtain ⟨past, hpast⟩ := (treeLaw_hasHistory x a haτ).exists
  have hcard : past.active.card = (activeCount x a).toNat := by
    have hh := congrArg Int.toNat hpast.current.count
    simpa only [Int.toNat_natCast] using hh
  have hslot := continuationLaw_slotForest hpast hn
  rw [hcard] at hslot
  rw [← hslot]
  apply (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mpr
  filter_upwards [continuationLaw_valid x hpast.current.valid] with q hq
  rw [slotForest_active_card]
  have hsub : q.active ⊆ Finset.range (a + k + 1) := by
    intro r hr
    exact Finset.mem_range.mpr (by have := hq.vertices_le r (hq.active_subset hr); omega)
  simpa only [Finset.card_range] using Finset.card_le_card hsub

end Freezing1.Forward
