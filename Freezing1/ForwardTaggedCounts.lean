module

public import Freezing1.ForwardTaggedPopulation
public import Freezing1.TaggedPopulationCounts
public import Freezing1.ForwardComponentMaximum

/-!
# Tagged counts are the source's actual forward counts

At the upper endpoint the cut roots are exactly the active vertices. The
tagged tall count is therefore the actual block count. Component caps are
bounded by the source maximum, including its distinguished star convention.
-/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

theorem cutRoots_eq_active_of_phaseData {x : SignSequence} {b : ℕ} {s : State}
    (hd : PhaseData x b s) : cutRoots s b = s.active := by
  ext v
  rw [mem_cutRoots]
  constructor
  · rintro ⟨hv, _hvb⟩
    obtain ⟨hvV, hf⟩ := Finset.mem_filter.mp hv
    apply (hd.valid.active_iff v hvV).mpr
    cases he : s.frozenAt v with
    | none => rfl
    | some j =>
      have hle := (hd.labels.bounded v hvV j he).2
      have hlt := hf j he
      omega
  · intro hv
    have hvV := hd.valid.active_subset hv
    have hf := (hd.valid.active_iff v hvV).mp hv
    refine ⟨Finset.mem_filter.mpr ⟨hvV, ?_⟩, hd.valid.vertices_le v hvV⟩
    intro j hj
    simp only [hf, reduceCtorEq] at hj

theorem rootPopulation_taggedPopulation (s : State) (a r : ℕ) :
    (TaggedPopulation.rootPopulation (taggedPopulation s a) r : ℤ) =
      componentPopulation s a r := by
  simp only [TaggedPopulation.rootPopulation, taggedPopulation, componentPopulation,
    componentActive, Multiset.filter_map, Multiset.card_map, Function.comp_apply]
  rfl

theorem totalTall_taggedPopulation {x : SignSequence} {b : ℕ} {s : State}
    (hd : PhaseData x b s) (a : ℕ) (t : ℝ) :
    TaggedPopulation.totalTall (taggedPopulation s a) t = blockTallCount s a b t := by
  simp only [TaggedPopulation.totalTall, taggedPopulation, Multiset.filter_map,
    Multiset.card_map, Function.comp_apply, blockTallCount,
    cutRoots_eq_active_of_phaseData hd]
  change (s.active.filter (fun v => t < (cutHeight s a v : ℝ))).card =
    (s.active.filter (fun v => t < (blockHeight s a b v : ℝ))).card
  congr 1
  apply Finset.filter_congr
  intro v hv
  have hz : cutHeight s b v = 0 :=
    cutHeightAux_eq_zero_of_le s b _ v (hd.valid.vertices_le v (hd.valid.active_subset hv))
  simp only [blockHeight, hz, Nat.sub_zero]

theorem goodTall_taggedPopulation (s : State) (a : ℕ) (G : Finset ℕ) (t : ℝ) :
    TaggedPopulation.goodTall (taggedPopulation s a) G t =
      (s.active.filter fun v => cutAncestor s a v ∈ G ∧ t < (cutHeight s a v : ℝ)).card := by
  simp only [TaggedPopulation.goodTall, taggedPopulation, Multiset.filter_map,
    Multiset.card_map, Function.comp_apply]
  rfl

/-- A supported tagged component cannot exceed the source's actual maximum. -/
theorem rootPopulation_tagged_le_componentMaximum (s : State) (a : ℕ)
    (roots : Finset ℕ) (hroots : cutRoots s a = roots)
    (hsupport : TaggedPopulation.TagsIn roots (taggedPopulation s a)) (r : ℕ) :
    TaggedPopulation.rootPopulation (taggedPopulation s a) r ≤ componentMaximum s a := by
  by_cases hz : TaggedPopulation.rootPopulation (taggedPopulation s a) r = 0
  · rw [hz]; exact Nat.zero_le _
  · have hm : 0 < ((taggedPopulation s a).filter (fun v => v.1 = r)).card :=
      Nat.pos_of_ne_zero hz
    obtain ⟨v, hv⟩ := Multiset.card_pos_iff_exists_mem.mp hm
    obtain ⟨hv, hvr⟩ := Multiset.mem_filter.mp hv
    have hr : r ∈ cutRoots s a := by rw [hroots, ← hvr]; exact hsupport v hv
    have hle : (TaggedPopulation.rootPopulation (taggedPopulation s a) r : ℤ) ≤
        componentPopulationWithRoot s a r := by
      rw [rootPopulation_taggedPopulation]
      change ((componentActive s a r).card : ℤ) ≤ (insert r (componentActive s a r)).card
      exact_mod_cast Finset.card_le_card (Finset.subset_insert r (componentActive s a r))
    have hnat : TaggedPopulation.rootPopulation (taggedPopulation s a) r ≤
        componentPopulationWithRoot s a r := by exact_mod_cast hle
    exact hnat.trans (Finset.le_sup hr)

end Freezing1.Forward
