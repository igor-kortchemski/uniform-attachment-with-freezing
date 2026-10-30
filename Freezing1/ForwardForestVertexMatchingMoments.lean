module

public import Freezing1.ForwardForestVertexObservations
public import Freezing1.TaggedPopulationSlotMoments

/-! Finite matching moments for identifiable later vertices, including distinct components. -/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable def forestMarkedVertexIndicator (F : State) (a : ℕ) (t : ℝ)
    (G : Finset ℕ) (v : ℕ) : ℝ :=
  if (v ∈ F.active ∧ t < (cutHeight F a v : ℝ)) ∧ cutAncestor F a v ∈ G then 1 else 0

theorem forestMarkedVertexIndicator_bounds (F : State) (a : ℕ) (t : ℝ) (G : Finset ℕ) (v : ℕ) :
    0 ≤ forestMarkedVertexIndicator F a t G v ∧ forestMarkedVertexIndicator F a t G v ≤ 1 := by
  unfold forestMarkedVertexIndicator
  split <;> norm_num

theorem forestMarkedVertexIndicator_le_tall (F : State) (a : ℕ) (t : ℝ) (G : Finset ℕ) (v : ℕ) :
    forestMarkedVertexIndicator F a t G v ≤ forestVertexTallIndicator F a t v := by
  unfold forestMarkedVertexIndicator forestVertexTallIndicator
  by_cases hv : v ∈ F.active ∧ t < (cutHeight F a v : ℝ)
  · simp only [hv, true_and, ite_true]
    split <;> norm_num
  · simp only [hv, false_and, ite_false]
    exact le_rfl

def forestVertexRootFin {F : State} {a m v : ℕ}
    (htags : TaggedPopulation.TagsIn (Finset.range m) (taggedPopulation F a)) (hv : v ∈ F.active) : Fin m :=
  ⟨cutAncestor F a v, Finset.mem_range.mp (htags (cutAncestor F a v, cutHeight F a v)
    (Multiset.mem_map.mpr ⟨v, hv, rfl⟩))⟩

theorem forestMarkedVertexIndicator_permutation_of_tall {F : State} {a m v : ℕ}
    (hm : m ≤ a + 1) (hv : a < v)
    (htags : TaggedPopulation.TagsIn (Finset.range m) (taggedPopulation F a))
    (G : Finset ℕ) (t : ℝ) (hTall : v ∈ F.active ∧ t < (cutHeight F a v : ℝ))
    (σ : Equiv.Perm (Fin m)) :
    forestMarkedVertexIndicator (F.relabel (rootSlotPermutation m σ)) a t G v =
      permutationIndicator (TaggedPopulation.goodSlotSet m G) σ (forestVertexRootFin htags hTall.1) := by
  let e := rootSlotPermutation m σ
  have he := rootSlotPermutation_bounded m σ
  have hev : e v = v := he v (by omega)
  have hmem : v ∈ (F.relabel e).active ↔ v ∈ F.active := by simpa only [hev] using mem_active_relabel e F v
  have hh : cutHeight (F.relabel e) a v = cutHeight F a v := by
    simpa only [hev] using cutHeight_relabel e F a v (fun i hi => he i (by omega))
  have ha : cutAncestor (F.relabel e) a v = e (cutAncestor F a v) := by
    simpa only [hev] using cutAncestor_relabel e F a v (fun i hi => he i (by omega))
  have hr : e (cutAncestor F a v) = (σ (forestVertexRootFin htags hTall.1)).val :=
    Equiv.Perm.viaFintypeEmbedding_apply_image σ ⟨Fin.val, Fin.val_injective⟩ (forestVertexRootFin htags hTall.1)
  change forestMarkedVertexIndicator (F.relabel e) a t G v = _
  simp only [forestMarkedVertexIndicator, hmem, hh, hTall.1, hTall.2, true_and, ha, hr]
  simp [permutationIndicator, TaggedPopulation.goodSlotSet]

theorem forestMarkedVertexIndicator_permutation_of_not_tall {F : State} {a m v : ℕ}
    (hm : m ≤ a + 1) (hv : a < v) (G : Finset ℕ) (t : ℝ)
    (hTall : ¬(v ∈ F.active ∧ t < (cutHeight F a v : ℝ))) (σ : Equiv.Perm (Fin m)) :
    forestMarkedVertexIndicator (F.relabel (rootSlotPermutation m σ)) a t G v = 0 := by
  apply le_antisymm
  · have hh := forestMarkedVertexIndicator_le_tall (F.relabel (rootSlotPermutation m σ)) a t G v
    rw [forestVertexTallIndicator_relabel hm hv (rootSlotPermutation_bounded m σ) F t] at hh
    simpa only [forestVertexTallIndicator, hTall, ite_false] using hh
  · exact (forestMarkedVertexIndicator_bounds _ a t G v).1

theorem integral_forestMarkedVertexIndicator {F : State} {a m v : ℕ}
    (hm : m ≤ a + 1) (hv : a < v)
    (htags : TaggedPopulation.TagsIn (Finset.range m) (taggedPopulation F a))
    (G : Finset ℕ) (hG : G ⊆ Finset.range m) (t : ℝ) :
    (∫ σ, forestMarkedVertexIndicator (F.relabel (rootSlotPermutation m σ)) a t G v
      ∂uniformPermutationLaw (Fin m)) =
      ((G.card : ℝ) / m) * forestVertexTallIndicator F a t v := by
  by_cases hTall : v ∈ F.active ∧ t < (cutHeight F a v : ℝ)
  · simp_rw [forestMarkedVertexIndicator_permutation_of_tall hm hv htags G t hTall]
    rw [integral_permutationIndicator, TaggedPopulation.card_goodSlotSet hG, Fintype.card_fin]
    simp [forestVertexTallIndicator, hTall]
  · simp_rw [forestMarkedVertexIndicator_permutation_of_not_tall hm hv G t hTall]
    simp only [integral_zero, forestVertexTallIndicator, hTall, ite_false, mul_zero]

theorem integral_forestMarkedVertexIndicator_pair_le {F : State} {a m v w : ℕ}
    (hm : m ≤ a + 1) (hv : a < v) (hw : a < w)
    (htags : TaggedPopulation.TagsIn (Finset.range m) (taggedPopulation F a))
    (G : Finset ℕ) (hG : G ⊆ Finset.range m) (t : ℝ)
    (hsep : forestVertexSeparated F a v w) :
    (∫ σ, forestMarkedVertexIndicator (F.relabel (rootSlotPermutation m σ)) a t G v *
      forestMarkedVertexIndicator (F.relabel (rootSlotPermutation m σ)) a t G w
      ∂uniformPermutationLaw (Fin m)) ≤
      ((G.card : ℝ) / m) ^ 2 * forestVertexTallIndicator F a t v * forestVertexTallIndicator F a t w := by
  by_cases hvTall : v ∈ F.active ∧ t < (cutHeight F a v : ℝ)
  · by_cases hwTall : w ∈ F.active ∧ t < (cutHeight F a w : ℝ)
    · simp_rw [forestMarkedVertexIndicator_permutation_of_tall hm hv htags G t hvTall,
        forestMarkedVertexIndicator_permutation_of_tall hm hw htags G t hwTall]
      have hij : forestVertexRootFin htags hvTall.1 ≠ forestVertexRootFin htags hwTall.1 := by
        intro hh
        exact hsep (congrArg Fin.val hh)
      have hh := integral_permutationIndicator_pair_le (TaggedPopulation.goodSlotSet m G) hij
      rw [TaggedPopulation.card_goodSlotSet hG, Fintype.card_fin] at hh
      simpa [forestVertexTallIndicator, hvTall, hwTall] using hh
    · simp_rw [forestMarkedVertexIndicator_permutation_of_not_tall hm hw G t hwTall]
      simp only [mul_zero, integral_zero, forestVertexTallIndicator, hwTall, ite_false, le_refl]
  · simp_rw [forestMarkedVertexIndicator_permutation_of_not_tall hm hv G t hvTall]
    simp only [zero_mul, integral_zero, forestVertexTallIndicator, hvTall, ite_false, mul_zero, le_refl]

end Freezing1.Forward
