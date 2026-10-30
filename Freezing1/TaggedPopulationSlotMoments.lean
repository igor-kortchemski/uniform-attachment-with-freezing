module

public import Freezing1.ForwardForestRootOrbit
public import Freezing1.TaggedPopulationCounts
public import Freezing1.UniformPermutationWeighted

/-! Exact finite matching moments for the root slots used by the actual forest law. -/

@[expose] public section

namespace Freezing1.TaggedPopulation

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable def goodSlotSet (m : ℕ) (G : Finset ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i => i.val ∈ G

theorem card_goodSlotSet {m : ℕ} {G : Finset ℕ} (hG : G ⊆ Finset.range m) :
    (goodSlotSet m G).card = G.card := by
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro r hr
    exact ⟨⟨r, Finset.mem_range.mp (hG hr)⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩, rfl⟩

theorem goodTall_relabel_image (e : Equiv.Perm ℕ) (M : State) (G : Finset ℕ) (t : ℝ) :
    goodTall (relabel e M) (G.image e) t = goodTall M G t := by
  simp [goodTall, relabel, Multiset.filter_map]

theorem goodTall_slot_eq_weighted {m : ℕ} {M : State} (hM : TagsIn (Finset.range m) M)
    (G : Finset ℕ) (t : ℝ) (σ : Equiv.Perm (Fin m)) :
    (goodTall (relabel (Forward.rootSlotPermutation m σ) M) G t : ℝ) =
      weightedPermutationCount (goodSlotSet m G)
        (fun i : Fin m => (rootTallPopulation M t i.val : ℝ)) σ := by
  rw [goodTall_relabel_eq_sum hM, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_zero]
  rw [← Fin.sum_univ_eq_sum_range
    (fun r => if Forward.rootSlotPermutation m σ r ∈ G then (rootTallPopulation M t r : ℝ) else 0) m]
  unfold weightedPermutationCount
  apply Finset.sum_congr rfl
  intro i _
  have he : Forward.rootSlotPermutation m σ i.val = (σ i).val :=
    Equiv.Perm.viaFintypeEmbedding_apply_image σ ⟨Fin.val, Fin.val_injective⟩ i
  simp [he, permutationIndicator, goodSlotSet]

theorem sum_slot_tall_weights {m : ℕ} {M : State} (hM : TagsIn (Finset.range m) M) (t : ℝ) :
    (∑ i : Fin m, (rootTallPopulation M t i.val : ℝ)) = totalTall M t := by
  rw [Fin.sum_univ_eq_sum_range (fun r => (rootTallPopulation M t r : ℝ)) m,
    ← Nat.cast_sum, sum_rootTallPopulation hM]

theorem integral_goodTall_slot {m : ℕ} {M : State} (hM : TagsIn (Finset.range m) M)
    (G : Finset ℕ) (hG : G ⊆ Finset.range m) (t : ℝ) :
    (∫ σ, (goodTall (relabel (Forward.rootSlotPermutation m σ) M) G t : ℝ)
      ∂uniformPermutationLaw (Fin m)) = ((G.card : ℝ) / m) * totalTall M t := by
  simp_rw [goodTall_slot_eq_weighted hM G t]
  rw [integral_weightedPermutationCount, card_goodSlotSet hG, Fintype.card_fin,
    sum_slot_tall_weights hM t]

theorem variance_goodTall_slot_le {m : ℕ} {M : State} (hM : TagsIn (Finset.range m) M)
    (G : Finset ℕ) (t : ℝ) {B : ℝ}
    (hcap : ∀ r : ℕ, (rootPopulation M r : ℝ) ≤ B) :
    variance (fun σ => (goodTall (relabel (Forward.rootSlotPermutation m σ) M) G t : ℝ))
      (uniformPermutationLaw (Fin m)) ≤
      B * ∫ σ, (goodTall (relabel (Forward.rootSlotPermutation m σ) M) G t : ℝ)
        ∂uniformPermutationLaw (Fin m) := by
  simp_rw [goodTall_slot_eq_weighted hM G t]
  apply variance_weightedPermutationCount_le _ _ (fun _ => Nat.cast_nonneg _)
  intro i
  exact (show (rootTallPopulation M t i.val : ℝ) ≤ rootPopulation M i.val by
    exact_mod_cast rootTallPopulation_le M t i.val).trans (hcap i.val)

end Freezing1.TaggedPopulation
