module

public import Freezing1.TaggedPopulationCounts
public import Mathlib.Logic.Equiv.Fintype

/-!
# The joint tall-count and star-maximum law depends only on root cardinality

A distinguished root contributes one extra vertex precisely when its
height-zero occurrence is absent. Relabeling the roots preserves this
convention, and hence preserves the pair of source block statistics.
-/

@[expose] public section

namespace Freezing1.TaggedPopulation

open MeasureTheory
open scoped Classical

noncomputable def rootPopulationWithRoot (m : State) (r : ℕ) : ℕ :=
  rootPopulation m r + if (r, 0) ∈ m then 0 else 1

noncomputable def componentMaximum (roots : Finset ℕ) (m : State) : ℕ :=
  roots.sup (rootPopulationWithRoot m)

noncomputable def blockStatistics (roots : Finset ℕ) (t : ℝ) (m : State) : ℕ × ℕ :=
  (totalTall m t, componentMaximum roots m)

theorem zero_mem_relabel (e : Equiv.Perm ℕ) (m : State) (r : ℕ) :
    (e r, 0) ∈ relabel e m ↔ (r, 0) ∈ m := by
  simp only [relabel, Multiset.mem_map]
  constructor
  · rintro ⟨⟨u, h⟩, huv, he⟩
    have hu : u = r := e.injective (congrArg Prod.fst he)
    have hh : h = 0 := congrArg Prod.snd he
    simpa only [hu, hh] using huv
  · intro hr
    exact ⟨(r, 0), hr, rfl⟩

theorem rootPopulationWithRoot_relabel (e : Equiv.Perm ℕ) (m : State) (r : ℕ) :
    rootPopulationWithRoot (relabel e m) (e r) = rootPopulationWithRoot m r := by
  simp only [rootPopulationWithRoot, rootPopulation_relabel, zero_mem_relabel]

theorem componentMaximum_relabel (e : Equiv.Perm ℕ) (roots : Finset ℕ) (m : State) :
    componentMaximum (roots.image e) (relabel e m) = componentMaximum roots m := by
  simp only [componentMaximum, Finset.sup_image]
  apply Finset.sup_congr rfl
  intro r _
  exact rootPopulationWithRoot_relabel e m r

theorem blockStatistics_relabel (e : Equiv.Perm ℕ) (roots : Finset ℕ) (t : ℝ) (m : State) :
    blockStatistics (roots.image e) t (relabel e m) = blockStatistics roots t m := by
  simp only [blockStatistics, totalTall_relabel, componentMaximum_relabel]

theorem map_blockStatistics_eq_of_card_eq (x : SignSequence) (a k : ℕ)
    (roots roots' : Finset ℕ) (hc : roots.card = roots'.card) (t : ℝ) :
    (continuationLaw x a k (initial roots)).map (blockStatistics roots t) =
      (continuationLaw x a k (initial roots')).map (blockStatistics roots' t) := by
  obtain ⟨e, he⟩ := Equiv.Perm.exists_map_finset_eq roots roots' hc
  have himage : roots.image e = roots' := by
    simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using he
  have hmap := map_continuationLaw_relabel x a k e (initial roots)
  rw [relabel_initial, himage] at hmap
  rw [← hmap, Measure.map_map measurable_from_top measurable_from_top]
  apply congrArg (Measure.map · (continuationLaw x a k (initial roots)))
  funext m
  simpa only [Function.comp_apply, himage] using (blockStatistics_relabel e roots t m).symm

noncomputable def blockStatisticsLaw (x : SignSequence) (a k count : ℕ) (t : ℝ) :
    Measure (ℕ × ℕ) :=
  (continuationLaw x a k (initial (Finset.range count))).map
    (blockStatistics (Finset.range count) t)

theorem map_blockStatistics_eq (x : SignSequence) (a k : ℕ) (roots : Finset ℕ) (t : ℝ) :
    (continuationLaw x a k (initial roots)).map (blockStatistics roots t) =
      blockStatisticsLaw x a k roots.card t :=
  map_blockStatistics_eq_of_card_eq x a k roots (Finset.range roots.card) (by simp) t

end Freezing1.TaggedPopulation
