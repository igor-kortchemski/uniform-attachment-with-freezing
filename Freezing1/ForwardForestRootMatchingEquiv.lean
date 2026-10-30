module

public import Freezing1.ForwardForestSlots

/-! Every old-root permutation is a genuine bijection to the lower active set. -/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def rootSlotEquiv (a : ℕ) (roots : Finset ℕ)
    (hb : ∀ r ∈ roots, r ≤ a) : Fin roots.card ≃ roots where
  toFun i := ⟨(rootNormalizer a roots).symm i.val, by
    have hi : i.val ∈ roots.image (rootNormalizer a roots) := by
      rw [rootNormalizer_image a roots hb]
      exact Finset.mem_range.mpr i.isLt
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hi
    simpa only [← he, Equiv.symm_apply_apply] using hr⟩
  invFun r := ⟨rootNormalizer a roots r.val, by
    apply Finset.mem_range.mp
    rw [← rootNormalizer_image a roots hb]
    exact Finset.mem_image.mpr ⟨r.val, r.property, rfl⟩⟩
  left_inv i := by apply Fin.ext; simp
  right_inv r := by apply Subtype.ext; simp

@[simp] theorem rootSlotEquiv_val (a : ℕ) (roots : Finset ℕ)
    (hb : ∀ r ∈ roots, r ≤ a) (i : Fin roots.card) :
    (rootSlotEquiv a roots hb i).val = (rootNormalizer a roots).symm i.val := rfl

noncomputable def rootMatchingEquiv (a : ℕ) (roots : Finset ℕ)
    (hb : ∀ r ∈ roots, r ≤ a) (σ : Equiv.Perm (Fin roots.card)) :
    Fin roots.card ≃ roots := σ.trans (rootSlotEquiv a roots hb)

theorem rootMatchingEquiv_val (a : ℕ) (roots : Finset ℕ)
    (hb : ∀ r ∈ roots, r ≤ a) (σ : Equiv.Perm (Fin roots.card)) (i : Fin roots.card) :
    (rootMatchingEquiv a roots hb σ i).val = (rootNormalizer a roots).symm (σ i).val := rfl

/-- This parametrizes every possible bijection, with no omission or repeated
matching. Thus uniform permutations give uniform matching of all old roots. -/
noncomputable def rootMatchingParametrization (a : ℕ) (roots : Finset ℕ)
    (hb : ∀ r ∈ roots, r ≤ a) :
    Equiv.Perm (Fin roots.card) ≃ (Fin roots.card ≃ roots) where
  toFun := rootMatchingEquiv a roots hb
  invFun e := e.trans (rootSlotEquiv a roots hb).symm
  left_inv σ := by ext i; simp [rootMatchingEquiv]
  right_inv e := by ext i; simp [rootMatchingEquiv]

end Freezing1.Forward
