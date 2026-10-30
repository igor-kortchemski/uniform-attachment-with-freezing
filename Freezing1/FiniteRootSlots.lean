module

public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

/-! Bounded root renamings fix every future birth ID. -/

@[expose] public section

namespace Freezing1

open scoped Classical

def boundedRootSet (a : ℕ) (roots : Finset ℕ) : Finset (Fin (a + 1)) :=
  Finset.univ.filter fun i => i.val ∈ roots

theorem boundedRootSet_image {a : ℕ} {roots : Finset ℕ}
    (hb : ∀ r ∈ roots, r ≤ a) : (boundedRootSet a roots).image Fin.val = roots := by
  ext r
  simp only [boundedRootSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hr
    exact ⟨⟨r, by have := hb r hr; omega⟩, hr, rfl⟩

theorem boundedRootSet_card {a : ℕ} {roots : Finset ℕ}
    (hb : ∀ r ∈ roots, r ≤ a) : (boundedRootSet a roots).card = roots.card := by
  calc
    _ = ((boundedRootSet a roots).image Fin.val).card :=
      (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ = _ := congrArg Finset.card (boundedRootSet_image hb)

theorem exists_bounded_root_relabel (a : ℕ) (roots roots' : Finset ℕ)
    (hb : ∀ r ∈ roots, r ≤ a) (hb' : ∀ r ∈ roots', r ≤ a)
    (hc : roots.card = roots'.card) :
    ∃ e : Equiv.Perm ℕ, roots.image e = roots' ∧ ∀ t : ℕ, a < t → e t = t := by
  have hc' : (boundedRootSet a roots).card = (boundedRootSet a roots').card := by
    rw [boundedRootSet_card hb, boundedRootSet_card hb', hc]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq
    (boundedRootSet a roots) (boundedRootSet a roots') hc'
  have hσ' : (boundedRootSet a roots).image σ = boundedRootSet a roots' := by
    simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using hσ
  let emb : Fin (a + 1) ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let e : Equiv.Perm ℕ := σ.viaFintypeEmbedding emb
  have he (i : Fin (a + 1)) : e i.val = (σ i).val :=
    Equiv.Perm.viaFintypeEmbedding_apply_image σ emb i
  refine ⟨e, ?_, ?_⟩
  · calc
      roots.image e = ((boundedRootSet a roots).image Fin.val).image e := by rw [boundedRootSet_image hb]
      _ = (boundedRootSet a roots).image (fun i => e i.val) := Finset.image_image
      _ = (boundedRootSet a roots).image (fun i => (σ i).val) := by
        congr 1
        funext i
        exact he i
      _ = ((boundedRootSet a roots).image σ).image Fin.val := Finset.image_image.symm
      _ = roots' := by rw [hσ', boundedRootSet_image hb']
  · intro t ht
    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
    rintro ⟨i, hi⟩
    have hil := i.isLt
    change i.val = t at hi
    omega

theorem exists_canonical_root_relabel (a : ℕ) (roots : Finset ℕ)
    (hb : ∀ r ∈ roots, r ≤ a) :
    ∃ e : Equiv.Perm ℕ, roots.image e = Finset.range roots.card ∧
      ∀ t : ℕ, a < t → e t = t := by
  have hsub : roots ⊆ Finset.range (a + 1) := fun r hr => Finset.mem_range.mpr (by have := hb r hr; omega)
  have hc : roots.card ≤ a + 1 := by simpa only [Finset.card_range] using Finset.card_le_card hsub
  exact exists_bounded_root_relabel a roots (Finset.range roots.card) hb
    (fun r hr => by have := Finset.mem_range.mp hr; omega) (by simp)

end Freezing1
