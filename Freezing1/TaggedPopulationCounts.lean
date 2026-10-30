module

public import Freezing1.TaggedPopulationKernel
public import Freezing1.UniformPermutationGrowth

/-!
# Root populations and marked descendants in the tagged process

All counts retain multiset multiplicity. Root support is propagated by the
actual occurrence-selection kernels; total marked mass and component caps
are invariant under relabeling of the initial roots.
-/

@[expose] public section

namespace Freezing1.TaggedPopulation

open MeasureTheory
open scoped ENNReal BigOperators Classical

def TagsIn (roots : Finset ℕ) (m : State) : Prop := ∀ v ∈ m, v.1 ∈ roots

theorem tagsIn_initial (roots : Finset ℕ) : TagsIn roots (initial roots) := by
  intro v hv
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hv
  exact hr

theorem tagsIn_step {roots : Finset ℕ} {m : State} (hm : TagsIn roots m)
    (sign : Bool) {v : ℕ × ℕ} (hv : v ∈ m) : TagsIn roots (step m sign v) := by
  intro w hw
  cases sign
  · exact hm w (Multiset.mem_of_mem_erase (by simpa only [step, Bool.false_eq_true,
      ↓reduceIte] using hw))
  · simp only [step, ↓reduceIte, Multiset.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hm v hv
    · exact hm w hw

theorem transitionLaw_tagsIn {roots : Finset ℕ} {m : State} (hm : TagsIn roots m)
    (sign : Bool) : ∀ᵐ t ∂transitionLaw m sign, TagsIn roots t := by
  by_cases hzero : m = 0
  · simp only [transitionLaw, hzero, ite_true]
    exact (ae_dirac_iff (by trivial)).mpr (by simpa only [hzero] using hm)
  · rw [transitionLaw, ite_eq_right hzero]
    apply (ae_map_iff (measurable_of_countable _).aemeasurable (by trivial)).mpr
    filter_upwards [multisetUniform_ae_mem m] with v hv
    exact tagsIn_step hm sign hv

theorem continuationLaw_tagsIn (x : SignSequence) (a k : ℕ)
    {roots : Finset ℕ} {m : State} (hm : TagsIn roots m) :
    ∀ᵐ t ∂continuationLaw x a k m, TagsIn roots t := by
  induction k generalizing a m with
  | zero => simpa only [continuationLaw] using (ae_dirac_iff (by trivial)).mpr hm
  | succ k ih =>
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [continuationLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _t, (1 : ℝ≥0∞) ∂transitionLaw m (x (a + 1)) := by
        apply lintegral_congr_ae
        filter_upwards [transitionLaw_tagsIn hm (x (a + 1))] with t ht
        exact (ae_iff_prob_eq_one measurable_from_top).mp (ih (a + 1) ht)
      _ = _ := by simp

noncomputable def rootPopulation (m : State) (r : ℕ) : ℕ :=
  (m.filter fun v => v.1 = r).card

noncomputable def rootTallPopulation (m : State) (t : ℝ) (r : ℕ) : ℕ :=
  (m.filter fun v => v.1 = r ∧ t < (v.2 : ℝ)).card

noncomputable def totalTall (m : State) (t : ℝ) : ℕ :=
  (m.filter fun v => t < (v.2 : ℝ)).card

noncomputable def goodTall (m : State) (G : Finset ℕ) (t : ℝ) : ℕ :=
  (m.filter fun v => v.1 ∈ G ∧ t < (v.2 : ℝ)).card

theorem rootTallPopulation_le (m : State) (t : ℝ) (r : ℕ) :
    rootTallPopulation m t r ≤ rootPopulation m r := by
  unfold rootTallPopulation rootPopulation
  have he : m.filter (fun v => v.1 = r ∧ t < (v.2 : ℝ)) =
      (m.filter fun v => v.1 = r).filter (fun v => t < (v.2 : ℝ)) := by
    rw [Multiset.filter_filter]
    apply Multiset.filter_congr
    intro v _
    exact and_comm
  rw [he]
  apply Multiset.card_le_card
  exact Multiset.filter_le _ _

theorem rootPopulation_relabel (e : Equiv.Perm ℕ) (m : State) (r : ℕ) :
    rootPopulation (relabel e m) (e r) = rootPopulation m r := by
  simp [rootPopulation, relabel, Multiset.filter_map]

theorem rootTallPopulation_relabel (e : Equiv.Perm ℕ) (m : State) (t : ℝ) (r : ℕ) :
    rootTallPopulation (relabel e m) t (e r) = rootTallPopulation m t r := by
  simp [rootTallPopulation, relabel, Multiset.filter_map]

theorem totalTall_relabel (e : Equiv.Perm ℕ) (m : State) (t : ℝ) :
    totalTall (relabel e m) t = totalTall m t := by
  simp [totalTall, relabel, Multiset.filter_map]

noncomputable def extendRootPermutation (roots : Finset ℕ) (σ : Equiv.Perm roots) :
    Equiv.Perm ℕ := σ.extendDomain (Equiv.refl _)

theorem extendRootPermutation_apply (roots : Finset ℕ) (σ : Equiv.Perm roots)
    (r : roots) : extendRootPermutation roots σ r = (σ r : ℕ) := by
  simpa only [extendRootPermutation, Equiv.refl_apply] using
    σ.extendDomain_apply_image (Equiv.refl _) r

theorem image_extendRootPermutation (roots : Finset ℕ) (σ : Equiv.Perm roots) :
    roots.image (extendRootPermutation roots σ) = roots := by
  ext r
  constructor
  · rintro hr
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
    rw [extendRootPermutation_apply roots σ ⟨q, hq⟩]
    exact (σ ⟨q, hq⟩).property
  · intro hr
    let q : roots := σ.symm ⟨r, hr⟩
    refine Finset.mem_image.mpr ⟨q, q.property, ?_⟩
    rw [extendRootPermutation_apply]
    simp [q]

noncomputable def goodRoots (roots G : Finset ℕ) : Finset roots :=
  Finset.univ.filter fun r => r.val ∈ G

theorem card_goodRoots (roots G : Finset ℕ) (hG : G ⊆ roots) :
    (goodRoots roots G).card = G.card := by
  apply Finset.card_bij (fun r _ => r.val)
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro r _ s _ hrs
    exact Subtype.ext hrs
  · intro r hr
    exact ⟨⟨r, hG hr⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩, rfl⟩

/-- Grouping actual marked occurrences by their original root tag. -/
theorem goodTall_relabel_eq_sum {roots : Finset ℕ} {m : State} (hm : TagsIn roots m)
    (e : Equiv.Perm ℕ) (G : Finset ℕ) (t : ℝ) :
    goodTall (relabel e m) G t =
      ∑ r ∈ roots, if e r ∈ G then rootTallPopulation m t r else 0 := by
  let mt : Multiset ℕ := (m.filter fun v => t < (v.2 : ℝ)).map Prod.fst
  have hsupport : ∀ r ∈ mt.filter (fun r => e r ∈ G), r ∈ roots := by
    intro r hr
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_filter.mp hr).1
    exact hm v (Multiset.mem_filter.mp hv).1
  have hcount : ∀ r, (mt.filter (fun r => e r ∈ G)).count r =
      if e r ∈ G then rootTallPopulation m t r else 0 := by
    intro r
    simp only [Multiset.count_filter, mt, Multiset.count_map, rootTallPopulation,
      Multiset.filter_filter]
    split_ifs
    · congr 1
      apply Multiset.filter_congr
      intro v _
      simp [eq_comm]
    · rfl
  have hcard : (mt.filter (fun r => e r ∈ G)).card = goodTall (relabel e m) G t := by
    simp only [mt, goodTall, relabel, Multiset.filter_map, Multiset.card_map,
      Multiset.filter_filter, Function.comp_apply]
  have hsum := Multiset.sum_count_eq_card hsupport
  simpa only [hcount, hcard] using hsum.symm

theorem goodTall_all_roots {roots : Finset ℕ} {m : State} (hm : TagsIn roots m) (t : ℝ) :
    goodTall m roots t = totalTall m t := by
  unfold goodTall totalTall
  congr 1
  apply Multiset.filter_congr
  intro v hv
  simp only [hm v hv, true_and]

theorem sum_rootTallPopulation {roots : Finset ℕ} {m : State}
    (hm : TagsIn roots m) (t : ℝ) :
    (∑ r ∈ roots, rootTallPopulation m t r) = totalTall m t := by
  have h := goodTall_relabel_eq_sum hm (Equiv.refl ℕ) roots t
  have he : relabel (Equiv.refl ℕ) m = m := by simp [relabel]
  rw [he, goodTall_all_roots hm t] at h
  calc
    _ = ∑ r ∈ roots, if (Equiv.refl ℕ) r ∈ roots then rootTallPopulation m t r else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      simp [hr]
    _ = _ := h.symm

/-- The marked count after an actual random root permutation is exactly the
weighted permutation count already analyzed, with multiplicities retained. -/
theorem goodTall_eq_weightedPermutationCount {roots : Finset ℕ} {m : State}
    (hm : TagsIn roots m) (G : Finset ℕ) (t : ℝ) (σ : Equiv.Perm roots) :
    (goodTall (relabel (extendRootPermutation roots σ) m) G t : ℝ) =
      weightedPermutationCount (goodRoots roots G)
        (fun r : roots => (rootTallPopulation m t r : ℝ)) σ := by
  rw [goodTall_relabel_eq_sum hm, Nat.cast_sum, ← Finset.sum_coe_sort]
  unfold weightedPermutationCount
  apply Finset.sum_congr rfl
  intro r _
  simp [permutationIndicator, goodRoots,
    extendRootPermutation_apply roots σ r]

end Freezing1.TaggedPopulation
