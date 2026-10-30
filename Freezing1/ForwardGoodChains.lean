module

public import Freezing1.ForwardCutUpdates
public import Freezing1.ForwardComponentPopulation
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Deterministic chains of tall geometric blocks

Good vertices are active vertices satisfying every earlier block-height test.
The block increments telescope, so a chain of good tests gives a genuine lower
bound on the tree height. Attachment after a block leaves its increment
unchanged on old vertices and passes it from a parent to its new child.
-/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical BigOperators

noncomputable def goodSet (s : State) (C k₀ k : ℕ) (t : ℝ) : Finset ℕ :=
  s.active.filter fun v => ∀ ell ∈ Finset.Ico k₀ k,
    t < (blockHeight s (C ^ ell) (C ^ (ell + 1)) v : ℝ)

theorem goodSet_subset (s : State) (C k₀ k : ℕ) (t : ℝ) :
    goodSet s C k₀ k t ⊆ s.active := Finset.filter_subset _ _

theorem goodSet_base (s : State) (C k₀ : ℕ) (t : ℝ) :
    goodSet s C k₀ k₀ t = s.active := by simp [goodSet]

theorem cutHeightAux_le_fuel (s : State) (a m v : ℕ) : cutHeightAux s a m v ≤ m := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    simp only [cutHeightAux]
    split_ifs
    · exact Nat.zero_le _
    · exact Nat.add_le_add_right (ih _) 1

theorem cutHeight_le_height (s : State) (a v : ℕ) : cutHeight s a v ≤ s.height v :=
  cutHeightAux_le_fuel s a _ v

theorem cutHeightAux_antitone (s : State) (m v : ℕ) :
    Antitone (fun a => cutHeightAux s a m v) := by
  induction m generalizing v with
  | zero => intro a b hab; exact le_rfl
  | succ m ih =>
    intro a b hab
    by_cases hvb : v ≤ b
    · simp only [cutHeightAux, ite_eq_left hvb]
      exact Nat.zero_le _
    · have hva : ¬v ≤ a := by omega
      simp only [cutHeightAux, ite_eq_right hvb, ite_eq_right hva]
      exact Nat.add_le_add_right (ih (s.parent v) hab) 1

theorem cutHeight_antitone (s : State) (v : ℕ) : Antitone (fun a => cutHeight s a v) :=
  cutHeightAux_antitone s _ v

theorem blockHeight_attach_old {n : ℕ} {s : State} (hs : ValidAt n s)
    (a b p : ℕ) {v : ℕ} (hv : v ∈ s.vertices) :
    blockHeight (attach s (n + 1) p) a b v = blockHeight s a b v := by
  simp only [blockHeight, cutHeight_attach_old hs a p hv, cutHeight_attach_old hs b p hv]

theorem blockHeight_attach_new {n : ℕ} {s : State} (hs : ValidAt n s)
    {a b p : ℕ} (ha : a ≤ n) (hb : b ≤ n) (hp : p ∈ s.active) :
    blockHeight (attach s (n + 1) p) a b (n + 1) = blockHeight s a b p := by
  simp only [blockHeight, cutHeight_attach_new hs ha hp, cutHeight_attach_new hs hb hp,
    Nat.add_sub_add_right]

theorem blockHeight_freeze (s : State) (t p a b v : ℕ) :
    blockHeight (freeze s t p) a b v = blockHeight s a b v := by
  simp only [blockHeight, cutHeight_freeze]

/-- The natural block increments telescope after their nonnegativity has
been proved from monotonicity of the time cut. -/
theorem sum_blockHeight_eq (s : State) (C : ℕ) (hC : 1 ≤ C) (k₀ k v : ℕ)
    (hk : k₀ ≤ k) :
    (∑ ell ∈ Finset.Ico k₀ k, (blockHeight s (C ^ ell) (C ^ (ell + 1)) v : ℝ)) =
      (cutHeight s (C ^ k₀) v : ℝ) - (cutHeight s (C ^ k) v : ℝ) := by
  induction k with
  | zero =>
    have he : k₀ = 0 := by omega
    subst k₀
    simp
  | succ k ih =>
    by_cases hkk : k₀ ≤ k
    · rw [Finset.sum_Ico_succ_top hkk, ih hkk]
      have hm : cutHeight s (C ^ (k + 1)) v ≤ cutHeight s (C ^ k) v :=
        cutHeight_antitone s v (pow_le_pow_right₀ hC (Nat.le_succ k))
      rw [blockHeight, Nat.cast_sub hm]
      ring
    · have he : k₀ = k + 1 := by omega
      subst k₀
      simp

theorem sum_blockHeight_le_height (s : State) (C : ℕ) (hC : 1 ≤ C) (k₀ k v : ℕ)
    (hk : k₀ ≤ k) :
    (∑ ell ∈ Finset.Ico k₀ k, (blockHeight s (C ^ ell) (C ^ (ell + 1)) v : ℝ)) ≤
      (s.height v : ℝ) := by
  rw [sum_blockHeight_eq s C hC k₀ k v hk]
  have hh : (cutHeight s (C ^ k₀) v : ℝ) ≤ s.height v := by
    exact_mod_cast cutHeight_le_height s (C ^ k₀) v
  have hz : (0 : ℝ) ≤ cutHeight s (C ^ k) v := Nat.cast_nonneg _
  linarith

/-- A good vertex gains at least one threshold for each completed block. -/
theorem goodSet_height_lower (s : State) (C : ℕ) (hC : 1 ≤ C) (k₀ k : ℕ)
    (hk : k₀ ≤ k) (t : ℝ) {v : ℕ} (hv : v ∈ goodSet s C k₀ k t) :
    ((k - k₀ : ℕ) : ℝ) * t ≤ (s.height v : ℝ) := by
  have hh := (Finset.mem_filter.mp hv).2
  have hsum : (∑ _ell ∈ Finset.Ico k₀ k, t) ≤
      ∑ ell ∈ Finset.Ico k₀ k, (blockHeight s (C ^ ell) (C ^ (ell + 1)) v : ℝ) :=
    Finset.sum_le_sum (fun ell he => (hh ell he).le)
  have hm := hsum.trans (sum_blockHeight_le_height s C hC k₀ k v hk)
  simpa using hm

/-- At the right endpoint, the new block test is the cut height itself. -/
theorem goodSet_succ_iff {C k₀ k : ℕ} (hk : k₀ ≤ k) {s : State}
    (hs : ValidAt (C ^ (k + 1)) s) (t : ℝ) (v : ℕ) :
    v ∈ goodSet s C k₀ (k + 1) t ↔
      v ∈ goodSet s C k₀ k t ∧ t < (cutHeight s (C ^ k) v : ℝ) := by
  have hblock (hv : v ∈ s.active) :
      blockHeight s (C ^ k) (C ^ (k + 1)) v = cutHeight s (C ^ k) v := by
    have hz : cutHeight s (C ^ (k + 1)) v = 0 :=
      cutHeightAux_eq_zero_of_le s _ _ v (hs.vertices_le v (hs.active_subset hv))
    simp only [blockHeight, hz, Nat.sub_zero]
  have hmem (j : ℕ) : v ∈ goodSet s C k₀ j t ↔
      v ∈ s.active ∧ ∀ ell ∈ Finset.Ico k₀ j,
        t < (blockHeight s (C ^ ell) (C ^ (ell + 1)) v : ℝ) := Finset.mem_filter
  rw [hmem, hmem]
  constructor
  · rintro ⟨hv, hall⟩
    refine ⟨⟨hv, fun ell he => hall ell (by simp only [Finset.mem_Ico] at he ⊢; omega)⟩, ?_⟩
    simpa only [hblock hv] using hall k (Finset.mem_Ico.mpr ⟨hk, Nat.lt_succ_self k⟩)
  · rintro ⟨⟨hv, hall⟩, hnew⟩
    refine ⟨hv, ?_⟩
    intro ell he
    by_cases heq : ell = k
    · subst ell
      simpa only [hblock hv] using hnew
    · exact hall ell (by simp only [Finset.mem_Ico] at he ⊢; omega)

end Freezing1.Forward
