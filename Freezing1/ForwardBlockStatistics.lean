module

public import Freezing1.ForwardTaggedCounts
public import Freezing1.TaggedPopulationStatistics
public import Freezing1.ForwardContinuationPrefix

/-!
# The true joint law of the two block statistics given an earlier tree

The distinguished root is counted in the maximum even after it freezes.
Its presence is read exactly from the height-zero tagged occurrence. Both
statistics therefore have a continuation law depending only on the schedule
and the deterministic active population at the cut.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped Classical ENNReal

theorem cutAncestorAux_self_of_cutHeightAux_zero (s : State) (a m v : ℕ)
    (hz : cutHeightAux s a m v = 0) : cutAncestorAux s a m v = v := by
  cases m with
  | zero => rfl
  | succ m =>
    by_cases hv : v ≤ a
    · simp only [cutAncestorAux, hv, ite_true]
    · simp only [cutHeightAux, hv, ite_false] at hz
      omega

theorem cutAncestor_self_of_cutHeight_zero (s : State) (a v : ℕ)
    (hz : cutHeight s a v = 0) : cutAncestor s a v = v :=
  cutAncestorAux_self_of_cutHeightAux_zero s a _ v hz

theorem zero_mem_taggedPopulation_iff (s : State) (a r : ℕ) (hr : r ≤ a) :
    (r, 0) ∈ taggedPopulation s a ↔ r ∈ s.active := by
  simp only [taggedPopulation, Multiset.mem_map, Finset.mem_val]
  constructor
  · rintro ⟨v, hv, he⟩
    have hanc : cutAncestor s a v = r := congrArg Prod.fst he
    have hh : cutHeight s a v = 0 := congrArg Prod.snd he
    rw [cutAncestor_self_of_cutHeight_zero s a v hh] at hanc
    simpa only [hanc] using hv
  · intro hv
    refine ⟨r, hv, ?_⟩
    rw [cutAncestor_of_le s a r hr,
      show cutHeight s a r = 0 from cutHeightAux_eq_zero_of_le s a _ r hr]

theorem rootPopulationWithRoot_taggedPopulation (s : State) (a r : ℕ) (hr : r ≤ a) :
    TaggedPopulation.rootPopulationWithRoot (taggedPopulation s a) r =
      componentPopulationWithRoot s a r := by
  have hc : TaggedPopulation.rootPopulation (taggedPopulation s a) r =
      (componentActive s a r).card := by
    have hh := rootPopulation_taggedPopulation s a r
    unfold componentPopulation at hh
    exact_mod_cast hh
  simp only [TaggedPopulation.rootPopulationWithRoot, hc, zero_mem_taggedPopulation_iff s a r hr]
  have hm : r ∈ componentActive s a r ↔ r ∈ s.active := by
    simp only [componentActive, Finset.mem_filter, cutAncestor_of_le s a r hr, and_true]
  by_cases hv : r ∈ s.active
  · simp only [hv, ite_true, Nat.add_zero, componentPopulationWithRoot,
      Finset.insert_eq_of_mem (hm.mpr hv)]
  · simp only [hv, ite_false, componentPopulationWithRoot,
      Finset.card_insert_of_notMem (fun hh => hv (hm.mp hh))]

theorem componentMaximum_taggedPopulation (s : State) (a : ℕ) :
    TaggedPopulation.componentMaximum (cutRoots s a) (taggedPopulation s a) =
      componentMaximum s a := by
  apply Finset.sup_congr rfl
  intro r hr
  exact rootPopulationWithRoot_taggedPopulation s a r ((mem_cutRoots s a r).mp hr).2

/-- The actual continuation distribution of the pair `(N, M)` is independent
of the incoming tree. Its population argument is the schedule's true count. -/
theorem continuationLaw_blockStatistics {x : SignSequence} {a k : ℕ} {s : State}
    (hs : HasHistory x a s) (hn : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) (t : ℝ) :
    (continuationLaw x a k s).map
        (fun q => (blockTallCount q a (a + k) t, componentMaximum q a)) =
      TaggedPopulation.blockStatisticsLaw x a k (activeCount x a).toNat t := by
  let μ := continuationLaw x a k s
  have hcount : s.active.card = (activeCount x a).toNat := by
    have hh := congrArg Int.toNat hs.current.count
    simpa only [Int.toNat_natCast] using hh
  calc
    _ = μ.map (fun q => TaggedPopulation.blockStatistics s.active t (taggedPopulation q a)) := by
      apply Measure.map_congr
      filter_upwards [continuationLaw_hasHistory hs hn, continuationLaw_truncate_self hs hn]
        with q hq hp
      have hroots : cutRoots q a = s.active := congrArg State.active hp
      rw [TaggedPopulation.blockStatistics, totalTall_taggedPopulation hq.current a t,
        ← hroots, componentMaximum_taggedPopulation]
    _ = (μ.map (fun q => taggedPopulation q a)).map
        (TaggedPopulation.blockStatistics s.active t) :=
      (Measure.map_map (μ := μ)
        (show Measurable (TaggedPopulation.blockStatistics s.active t) from measurable_from_top)
        (show Measurable (fun q : State => taggedPopulation q a) from measurable_from_top)).symm
    _ = TaggedPopulation.blockStatisticsLaw x a k s.active.card t := by
      rw [continuationLaw_taggedPopulation_at_cut hs.current hn,
        TaggedPopulation.map_blockStatistics_eq]
    _ = _ := by rw [hcount]

end Freezing1.Forward
