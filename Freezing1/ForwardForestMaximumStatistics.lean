module

public import Freezing1.ForwardForestTallStatistics
public import Freezing1.ForwardBlockStatistics

/-! The marked-root component maximum is a function of the full bare forest. -/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

set_option backward.isDefEq.respectTransparency false

theorem componentActive_slotStarForest (F : State) {m a r : ℕ} (hm : m ≤ a + 1)
    (hr : r ∈ Finset.range m) :
    componentActive (slotStarForest m F) a r = insert r (componentActive F a r) := by
  ext v
  simp only [componentActive, Finset.mem_filter, Finset.mem_insert]
  rw [cutAncestor_slotStarForest]
  change ((v ∈ F.active ∪ Finset.range m) ∧ cutAncestor F a v = r) ↔
    v = r ∨ (v ∈ F.active ∧ cutAncestor F a v = r)
  constructor
  · rintro ⟨hv, hanc⟩
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Or.inr ⟨hv, hanc⟩
    · have hva : v ≤ a := by have := Finset.mem_range.mp hv; omega
      rw [cutAncestor_of_le F a v hva] at hanc
      exact Or.inl hanc
  · rintro (hvr | ⟨hv, hanc⟩)
    · subst v
      have hra : r ≤ a := by have := Finset.mem_range.mp hr; omega
      exact ⟨Finset.mem_union.mpr (Or.inr hr), cutAncestor_of_le F a r hra⟩
    · exact ⟨Finset.mem_union.mpr (Or.inl hv), hanc⟩

noncomputable def forestComponentMaximum (F : State) (a m : ℕ) : ℕ :=
  TaggedPopulation.componentMaximum (Finset.range m) (taggedPopulation F a)

theorem forestComponentMaximum_slotStarForest (F : State) {m a : ℕ} (hm : m ≤ a + 1) :
    forestComponentMaximum (slotStarForest m F) a m = forestComponentMaximum F a m := by
  unfold forestComponentMaximum TaggedPopulation.componentMaximum
  apply Finset.sup_congr rfl
  intro r hr
  have hra : r ≤ a := by have := Finset.mem_range.mp hr; omega
  rw [rootPopulationWithRoot_taggedPopulation _ a r hra,
    rootPopulationWithRoot_taggedPopulation F a r hra]
  simp only [componentPopulationWithRoot, componentActive_slotStarForest F hm hr, Finset.insert_idem]

theorem forestComponentMaximum_relabel (F : State) (a m : ℕ) (e : Equiv.Perm ℕ)
    (he : ∀ i : ℕ, a < i → e i = i) (hroots : (Finset.range m).image e = Finset.range m) :
    forestComponentMaximum (F.relabel e) a m = forestComponentMaximum F a m := by
  unfold forestComponentMaximum
  rw [taggedPopulation_relabel e F a he, ← hroots, TaggedPopulation.componentMaximum_relabel]
  rw [hroots]

noncomputable def bareForestComponentMaximum (a m : ℕ) (hm : m ≤ a + 1) : RootErasedForest m → ℕ :=
  Quotient.lift (fun F => forestComponentMaximum F a m) (by
    rintro F G ⟨e, he, hG⟩
    rw [hG, forestComponentMaximum_relabel F a m e (fun i hi => he i (by omega)) he.image_range])

theorem bareForestComponentMaximum_bareSlotOrbit (F : State) (a m : ℕ) (hm : m ≤ a + 1) :
    bareForestComponentMaximum a m hm (bareSlotOrbit m F) = forestComponentMaximum F a m := by
  rw [bareSlotOrbit_eq]
  exact forestComponentMaximum_slotStarForest F hm

theorem forestComponentMaximum_slotForest {x : SignSequence} {b : ℕ} {s : State}
    (hs : HasHistory x b s) (hb : (b : ℕ∞) ≤ extinctionTime x) (a : ℕ) :
    forestComponentMaximum (slotForest s a) a (cutRoots s a).card = componentMaximum s a := by
  let e := rootNormalizer a (cutRoots s a)
  have hroots : (cutRoots s a).image e = Finset.range (cutRoots s a).card :=
    rootNormalizer_image a (cutRoots s a) (fun r hr => ((mem_cutRoots s a r).mp hr).2)
  change TaggedPopulation.componentMaximum (Finset.range (cutRoots s a).card)
    (taggedPopulation ((forestCut s a).relabel e) a) = _
  rw [taggedPopulation_relabel e _ a (rootNormalizer_future a (cutRoots s a)), ← hroots,
    TaggedPopulation.componentMaximum_relabel, taggedPopulation_forestCut hs hb a,
    componentMaximum_taggedPopulation]

theorem cutRoots_card_eq_activeCount {x : SignSequence} {b : ℕ} {s : State}
    (hs : HasHistory x b s) (hb : (b : ℕ∞) ≤ extinctionTime x) {a : ℕ} (hab : a ≤ b) :
    (cutRoots s a).card = (activeCount x a).toNat := by
  have hh := congrArg Int.toNat ((hs.historyShape hb).prefix_phaseData hab).count
  simpa only [Int.toNat_natCast, cutRoots] using hh

/-- The actual source M, including every distinguished root exactly once,
is measurable from the bare all-star forest. -/
theorem bareForestComponentMaximum_actual {x : SignSequence} {b : ℕ} {s : State}
    (hs : HasHistory x b s) (hb : (b : ℕ∞) ≤ extinctionTime x) {a : ℕ} (hab : a ≤ b)
    (hm : (activeCount x a).toNat ≤ a + 1) :
    bareForestComponentMaximum a (activeCount x a).toNat hm
      (bareSlotOrbit (activeCount x a).toNat (slotForest s a)) = componentMaximum s a := by
  rw [bareForestComponentMaximum_bareSlotOrbit]
  rw [← cutRoots_card_eq_activeCount hs hb hab]
  exact forestComponentMaximum_slotForest hs hb a

end Freezing1.Forward
