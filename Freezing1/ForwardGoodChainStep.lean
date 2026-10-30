module

public import Freezing1.ForwardTaggedCounts
public import Freezing1.TaggedPopulationGrowth
public import Freezing1.ForwardGoodChainPropagation
public import Freezing1.ForwardContinuationPrefix

/-!
# A genuine conditional growth estimate for good vertices

The old good vertices mark the initial roots of the tagged continuation.
Actual parent inheritance identifies the new good count, and the proved
permutation symmetry bounds it while keeping both forest restrictions inside
the event. No independence of the past and those restrictions is used.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped ENNReal Classical

theorem continuationLaw_goodSet_growth_failure_le
    {x : SignSequence} {s : State} {C k₀ k : ℕ}
    (hs : HasHistory x (C ^ k) s) (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hτ : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x)
    (ha : (3 : ℝ) ≤ (C ^ k : ℕ)) (t : ℝ) {b M : ℝ} (hb : 0 < b) (hM : 0 ≤ M)
    (hg : b ≤ ((goodSet s C k₀ k t).card : ℝ)) :
    (continuationLaw x (C ^ k) (C ^ (k + 1) - C ^ k) s).real
      {q | 4 * ((C ^ k : ℕ) : ℝ) ≤
          (blockTallCount q (C ^ k) (C ^ (k + 1)) t : ℝ) ∧
        (componentMaximum q (C ^ k) : ℝ) ≤ M ∧
        ((goodSet q C k₀ (k + 1) t).card : ℝ) < 2 * b} ≤ 3 * M / b := by
  let a := C ^ k
  let j := C ^ (k + 1) - C ^ k
  let G := goodSet s C k₀ k t
  let μ := continuationLaw x a j s
  let ν := TaggedPopulation.continuationLaw x a j (TaggedPopulation.initial s.active)
  let E : Set TaggedPopulation.State := {m |
    4 * (a : ℝ) ≤ (TaggedPopulation.totalTall m t : ℝ) ∧
    (∀ r, (TaggedPopulation.rootPopulation m r : ℝ) ≤ M) ∧
    (TaggedPopulation.goodTall m G t : ℝ) < 2 * b}
  have hab : C ^ k ≤ C ^ (k + 1) := pow_le_pow_right₀ hC (Nat.le_succ k)
  have he : a + j = C ^ (k + 1) := Nat.add_sub_of_le hab
  have hτ' : ((a + j : ℕ) : ℕ∞) ≤ extinctionTime x := by rw [he]; exact hτ
  have hmap : μ.map (fun q => taggedPopulation q a) = ν :=
    continuationLaw_taggedPopulation_at_cut hs.current hτ'
  have htags : ∀ᵐ q ∂μ, TaggedPopulation.TagsIn s.active (taggedPopulation q a) := by
    apply ae_of_ae_map (p := TaggedPopulation.TagsIn s.active) measurable_from_top.aemeasurable
    rw [hmap]
    exact TaggedPopulation.continuationLaw_tagsIn x a j (TaggedPopulation.tagsIn_initial s.active)
  have hhist := continuationLaw_hasHistory hs hτ'
  rw [he] at hhist
  have hprefix := continuationLaw_truncate_self hs hτ'
  have hgood := continuationLaw_goodSet_succ x hs.current.valid hC hk t
  have hsub : ∀ᵐ q ∂μ,
      (4 * (a : ℝ) ≤ (blockTallCount q a (C ^ (k + 1)) t : ℝ) ∧
        (componentMaximum q a : ℝ) ≤ M ∧
        ((goodSet q C k₀ (k + 1) t).card : ℝ) < 2 * b) → taggedPopulation q a ∈ E := by
    filter_upwards [htags, hhist, hprefix, hgood] with q hqtag hqhist hqprefix hqgood
    intro hq
    have hroots : cutRoots q a = s.active := congrArg State.active hqprefix
    refine ⟨?_, ?_, ?_⟩
    · rw [totalTall_taggedPopulation hqhist.current a t]
      exact hq.1
    · intro r
      have hr : (TaggedPopulation.rootPopulation (taggedPopulation q a) r : ℝ) ≤
          componentMaximum q a := by
        exact_mod_cast rootPopulation_tagged_le_componentMaximum q a s.active hroots hqtag r
      exact hr.trans hq.2.1
    · rw [goodTall_taggedPopulation]
      change ((q.active.filter (fun v => cutAncestor q (C ^ k) v ∈ goodSet s C k₀ k t ∧
        t < (cutHeight q (C ^ k) v : ℝ))).card : ℝ) < 2 * b
      rw [← hqgood]
      exact hq.2.2
  have hpop : (s.active.card : ℝ) ≤ (a : ℝ) + 1 := by
    have hsubset : s.active ⊆ Finset.range (a + 1) := by
      intro v hv
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hs.current.valid.vertices_le v
        (hs.current.valid.active_subset hv)))
    have hc := Finset.card_le_card hsubset
    simp only [Finset.card_range] at hc
    exact_mod_cast hc
  have hbound : ν.real E ≤ 3 * M / b :=
    TaggedPopulation.continuationLaw_goodTall_growth_failure_le x a j s.active G
      (goodSet_subset s C k₀ k t) t ha hb hpop hg hM
  calc
    _ ≤ μ.real {q | taggedPopulation q a ∈ E} :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ = ν.real E := by
      have hh := congrArg (fun ρ : Measure TaggedPopulation.State => ρ E) hmap
      rw [Measure.map_apply measurable_from_top (by trivial)] at hh
      exact congrArg ENNReal.toReal hh
    _ ≤ _ := hbound

end Freezing1.Forward
