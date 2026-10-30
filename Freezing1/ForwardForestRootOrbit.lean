module

public import Freezing1.ForwardForestSlots
public import Freezing1.UniformPermutationMoments

/-! Erasing precisely the names of the old roots in a complete cut forest. -/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

theorem State.relabel_refl (s : State) : s.relabel (Equiv.refl ℕ) = s := by
  apply State.ext_data
  · simp [State.relabel]
  · simp [State.relabel]
  · rfl
  · rfl
  · rfl
  · rfl

theorem State.relabel_trans (s : State) (e f : Equiv.Perm ℕ) :
    (s.relabel e).relabel f = s.relabel (e.trans f) := by
  apply State.ext_data
  · simp [State.relabel, Finset.image_image, Equiv.trans_apply]
  · simp [State.relabel, Finset.image_image, Equiv.trans_apply]
  · rfl
  · rfl
  · rfl
  · rfl

def RootPermutation (m : ℕ) (e : Equiv.Perm ℕ) : Prop := ∀ t : ℕ, m ≤ t → e t = t

theorem RootPermutation.symm {m : ℕ} {e : Equiv.Perm ℕ} (he : RootPermutation m e) :
    RootPermutation m e.symm := by
  intro t ht
  apply e.injective
  simp only [Equiv.apply_symm_apply, he t ht]

theorem RootPermutation.trans {m : ℕ} {e f : Equiv.Perm ℕ}
    (he : RootPermutation m e) (hf : RootPermutation m f) : RootPermutation m (e.trans f) := by
  intro t ht
  simp only [Equiv.trans_apply, he t ht, hf t ht]

theorem RootPermutation.image_range {m : ℕ} {e : Equiv.Perm ℕ} (he : RootPermutation m e) :
    (Finset.range m).image e = Finset.range m := by
  apply Finset.eq_of_subset_of_card_le
  · intro t ht
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
    apply Finset.mem_range.mpr
    by_contra hh
    have hm : m ≤ e r := Nat.le_of_not_gt hh
    have heq : e r = r := e.injective (he (e r) hm)
    have hrm := Finset.mem_range.mp hr
    omega
  · simp only [Finset.card_image_of_injective _ e.injective]
    exact le_rfl

def rootForestSetoid (m : ℕ) : Setoid State where
  r F G := ∃ e : Equiv.Perm ℕ, RootPermutation m e ∧ G = F.relabel e
  iseqv := by
    constructor
    · intro F
      exact ⟨Equiv.refl ℕ, fun _ _ => rfl, F.relabel_refl.symm⟩
    · rintro F G ⟨e, he, rfl⟩
      refine ⟨e.symm, he.symm, ?_⟩
      rw [State.relabel_trans, Equiv.self_trans_symm, State.relabel_refl]
    · rintro F G H ⟨e, he, hG⟩ ⟨f, hf, hH⟩
      refine ⟨e.trans f, he.trans hf, ?_⟩
      rw [hH, hG, State.relabel_trans]

abbrev RootErasedForest (m : ℕ) := Quotient (rootForestSetoid m)

instance (m : ℕ) : MeasurableSpace (RootErasedForest m) := ⊤
instance (m : ℕ) : DiscreteMeasurableSpace (RootErasedForest m) := ⟨fun _ => trivial⟩

def eraseRootNames (m : ℕ) (F : State) : RootErasedForest m := Quotient.mk _ F

theorem eraseRootNames_relabel {m : ℕ} {e : Equiv.Perm ℕ} (he : RootPermutation m e) (F : State) :
    eraseRootNames m (F.relabel e) = eraseRootNames m F := by
  have hh : (rootForestSetoid m).r F (F.relabel e) := ⟨e, he, rfl⟩
  exact (Quotient.sound (s := rootForestSetoid m) hh).symm

def rootSlotPermutation (m : ℕ) (σ : Equiv.Perm (Fin m)) : Equiv.Perm ℕ :=
  σ.viaFintypeEmbedding ⟨Fin.val, Fin.val_injective⟩

theorem rootSlotPermutation_bounded (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    RootPermutation m (rootSlotPermutation m σ) := by
  intro t ht
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  rintro ⟨i, hi⟩
  have hil := i.isLt
  change i.val = t at hi
  omega

theorem forestSlotLaw_root_permutation (x : SignSequence) (a k m : ℕ)
    (hm : m ≤ a + 1) (σ : Equiv.Perm (Fin m)) :
    (forestSlotLaw x a k m).map (State.relabel (rootSlotPermutation m σ)) = forestSlotLaw x a k m := by
  have he := rootSlotPermutation_bounded m σ
  exact forestSlotLaw_relabel_invariant x a k m _
    (fun t ht => he t (by omega)) he.image_range

/-- Uniformly rematching the old-root slots leaves the genuine full forest
law unchanged. The permutation is independently sampled by this bind. -/
theorem forestSlotLaw_uniform_root_permutation (x : SignSequence) (a k m : ℕ)
    (hm : m ≤ a + 1) :
    (forestSlotLaw x a k m).bind (fun F => (uniformPermutationLaw (Fin m)).map
      (fun σ => F.relabel (rootSlotPermutation m σ))) = forestSlotLaw x a k m := by
  calc
    _ = (forestSlotLaw x a k m).bind (fun F => (uniformPermutationLaw (Fin m)).bind
        (fun σ => Measure.dirac (F.relabel (rootSlotPermutation m σ)))) := by
      congr 1
      funext F
      exact (Measure.bind_dirac_eq_map _ measurable_from_top).symm
    _ = (uniformPermutationLaw (Fin m)).bind (fun σ => (forestSlotLaw x a k m).bind
        (fun F => Measure.dirac (F.relabel (rootSlotPermutation m σ)))) := by
      apply Measure.bind_comm
      exact measurable_from_prod_countable_left (fun _ => measurable_from_top)
    _ = (uniformPermutationLaw (Fin m)).bind (fun _ => forestSlotLaw x a k m) := by
      congr 1
      funext σ
      rw [Measure.bind_dirac_eq_map _ measurable_from_top, forestSlotLaw_root_permutation x a k m hm]
    _ = _ := by simp only [Measure.bind_const, measure_univ, one_smul]

/-- Exact matching conditional on the root-erased forest, expressed as a
joint law. Its outer forest and independent uniform permutation are actual
proved laws, not a hypothesized conditional matching distribution. -/
theorem forestSlotLaw_uniform_matching_observation {β : Type*} [MeasurableSpace β]
    (x : SignSequence) (a k m : ℕ) (hm : m ≤ a + 1) (ψ : State → β) :
    (forestSlotLaw x a k m).map (fun F => (eraseRootNames m F, ψ F)) =
      (forestSlotLaw x a k m).bind (fun F => (uniformPermutationLaw (Fin m)).map
        (fun σ => (eraseRootNames m F, ψ (F.relabel (rootSlotPermutation m σ))))) := by
  conv_lhs => rw [← forestSlotLaw_uniform_root_permutation x a k m hm]
  rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  congr 1
  funext F
  rw [Measure.map_map measurable_from_top measurable_from_top]
  congr 1
  funext σ
  dsimp only [Function.comp_def]
  rw [eraseRootNames_relabel (rootSlotPermutation_bounded m σ)]

end Freezing1.Forward
