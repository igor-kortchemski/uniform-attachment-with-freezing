module

public import Freezing1.ForwardForestTaggedProjection
public import Freezing1.ForwardForestStarOrbit
public import Freezing1.ForwardTaggedCounts
public import Freezing1.TaggedPopulationStatistics

/-! The source's tall-descendant counts are functions of its complete bare forest. -/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

set_option backward.isDefEq.respectTransparency false

theorem cutHeightAux_congr_parent (s q : State) (hp : s.parent = q.parent) (a m v : ℕ) :
    cutHeightAux s a m v = cutHeightAux q a m v := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih => simp only [cutHeightAux, hp, ih]

theorem cutAncestorAux_congr_parent (s q : State) (hp : s.parent = q.parent) (a m v : ℕ) :
    cutAncestorAux s a m v = cutAncestorAux q a m v := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih => simp only [cutAncestorAux, hp, ih]

theorem cutHeight_slotStarForest (F : State) (m a v : ℕ) :
    cutHeight (slotStarForest m F) a v = cutHeight F a v := by
  change cutHeightAux (slotStarForest m F) a (F.height v) v = cutHeightAux F a (F.height v) v
  exact cutHeightAux_congr_parent (slotStarForest m F) F rfl _ _ _

theorem cutAncestor_slotStarForest (F : State) (m a v : ℕ) :
    cutAncestor (slotStarForest m F) a v = cutAncestor F a v := by
  change cutAncestorAux (slotStarForest m F) a (F.height v) v = cutAncestorAux F a (F.height v) v
  exact cutAncestorAux_congr_parent (slotStarForest m F) F rfl _ _ _

noncomputable def forestTallCount (F : State) (a : ℕ) (t : ℝ) : ℕ :=
  TaggedPopulation.totalTall (taggedPopulation F a) t

theorem forestTallCount_eq_filter (F : State) (a : ℕ) (t : ℝ) :
    forestTallCount F a t = (F.active.filter fun v => t < (cutHeight F a v : ℝ)).card := by
  simp only [forestTallCount, TaggedPopulation.totalTall, taggedPopulation, Multiset.filter_map,
    Multiset.card_map, Function.comp_apply]
  rfl

theorem forestTallCount_slotStarForest (F : State) {m a : ℕ} (hm : m ≤ a + 1)
    {t : ℝ} (ht : 0 ≤ t) : forestTallCount (slotStarForest m F) a t = forestTallCount F a t := by
  rw [forestTallCount_eq_filter, forestTallCount_eq_filter]
  simp_rw [cutHeight_slotStarForest]
  congr 1
  ext v
  simp only [Finset.mem_filter]
  change (v ∈ F.active ∪ Finset.range m ∧ t < (cutHeight F a v : ℝ)) ↔
    (v ∈ F.active ∧ t < (cutHeight F a v : ℝ))
  constructor
  · rintro ⟨hv, hvt⟩
    rcases Finset.mem_union.mp hv with hv | hv
    · exact ⟨hv, hvt⟩
    · have hva : v ≤ a := by have := Finset.mem_range.mp hv; omega
      have hz : cutHeight F a v = 0 := cutHeightAux_eq_zero_of_le F a _ v hva
      rw [hz, Nat.cast_zero] at hvt
      exact (not_lt_of_ge ht hvt).elim
  · rintro ⟨hv, hvt⟩
    exact ⟨Finset.mem_union.mpr (Or.inl hv), hvt⟩

theorem forestTallCount_relabel (F : State) (a : ℕ) (t : ℝ) (e : Equiv.Perm ℕ)
    (he : ∀ i : ℕ, a < i → e i = i) : forestTallCount (F.relabel e) a t = forestTallCount F a t := by
  rw [forestTallCount, taggedPopulation_relabel e F a he, TaggedPopulation.totalTall_relabel]
  rfl

noncomputable def bareForestTallCount (a m : ℕ) (hm : m ≤ a + 1) (t : ℝ) : RootErasedForest m → ℕ :=
  Quotient.lift (fun F => forestTallCount F a t) (by
    rintro F G ⟨e, he, hG⟩
    rw [hG, forestTallCount_relabel F a t e (fun i hi => he i (by omega))])

theorem bareForestTallCount_bareSlotOrbit (F : State) (a m : ℕ) (hm : m ≤ a + 1)
    {t : ℝ} (ht : 0 ≤ t) : bareForestTallCount a m hm t (bareSlotOrbit m F) = forestTallCount F a t := by
  rw [bareSlotOrbit_eq]
  exact forestTallCount_slotStarForest F hm ht

theorem forestTallCount_slotForest {x : SignSequence} {b : ℕ} {s : State}
    (hs : HasHistory x b s) (hb : (b : ℕ∞) ≤ extinctionTime x) (a : ℕ) (t : ℝ) :
    forestTallCount (slotForest s a) a t = blockTallCount s a b t := by
  unfold slotForest
  rw [forestTallCount_relabel _ a t _ (rootNormalizer_future a (cutRoots s a))]
  rw [forestTallCount, taggedPopulation_forestCut hs hb a,
    totalTall_taggedPopulation hs.current a t]

/-- The actual N count is measurable from the paper's full bare forest;
adding marked roots does not add tall vertices when the threshold is nonnegative. -/
theorem bareForestTallCount_actual {x : SignSequence} {b : ℕ} {s : State}
    (hs : HasHistory x b s) (hb : (b : ℕ∞) ≤ extinctionTime x)
    (a m : ℕ) (hm : m ≤ a + 1) {t : ℝ} (ht : 0 ≤ t) :
    bareForestTallCount a m hm t (bareSlotOrbit m (slotForest s a)) = blockTallCount s a b t := by
  rw [bareForestTallCount_bareSlotOrbit _ a m hm ht, forestTallCount_slotForest hs hb a t]

end Freezing1.Forward
