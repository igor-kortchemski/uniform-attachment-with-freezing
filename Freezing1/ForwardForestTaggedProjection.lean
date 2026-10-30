module

public import Freezing1.ForwardForestReconstruction
public import Freezing1.ForwardForestRelabel
public import Freezing1.ForwardTaggedPopulation

/-! Complete cut-forest data recover the genuine active root/height population. -/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

set_option backward.isDefEq.respectTransparency false

theorem cutHeightAux_stable_fuel (s : State) (a m v : ℕ) :
    cutHeightAux s a (cutHeightAux s a m v) v = cutHeightAux s a m v := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    by_cases hv : v ≤ a
    · simp only [cutHeightAux, ite_eq_left hv]
    · have he : cutHeightAux s a (m + 1) v = cutHeightAux s a m (s.parent v) + 1 := by
        simp only [cutHeightAux, ite_eq_right hv]
      rw [he]
      simp only [cutHeightAux, ite_eq_right hv, ih]

theorem cutAncestorAux_stable_fuel (s : State) (a m v : ℕ) :
    cutAncestorAux s a (cutHeightAux s a m v) v = cutAncestorAux s a m v := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    by_cases hv : v ≤ a
    · simp only [cutHeightAux, cutAncestorAux, ite_eq_left hv]
    · have he : cutHeightAux s a (m + 1) v = cutHeightAux s a m (s.parent v) + 1 := by
        simp only [cutHeightAux, ite_eq_right hv]
      rw [he]
      simp only [cutAncestorAux, ite_eq_right hv, ih]

theorem parent_mem_cutVertices_of_after {x : SignSequence} {n : ℕ} {s : State}
    (hs : HasHistory x n s) (hn : (n : ℕ∞) ≤ extinctionTime x)
    {a v : ℕ} (hv : v ∈ s.vertices) (hav : a < v) : s.parent v ∈ cutVertices s a := by
  have hshape := hs.historyShape hn
  have hv0 : v ≠ 0 := by omega
  refine Finset.mem_filter.mpr ⟨hs.current.valid.parent_mem v hv, ?_⟩
  intro t ht
  exact hav.trans (hshape.parent_frozen_after_child v hv hv0 t ht)

theorem cutHeightAux_forestCut {x : SignSequence} {n : ℕ} {s : State}
    (hs : HasHistory x n s) (hn : (n : ℕ∞) ≤ extinctionTime x) (a m : ℕ)
    {v : ℕ} (hv : v ∈ cutVertices s a) :
    cutHeightAux (forestCut s a) a m v = cutHeightAux s a m v := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    by_cases hva : v ≤ a
    · simp only [cutHeightAux, ite_eq_left hva]
    · have hvV := (Finset.mem_filter.mp hv).1
      have hp := parent_mem_cutVertices_of_after hs hn hvV (Nat.lt_of_not_ge hva)
      have hparent : (forestCut s a).parent v = s.parent v := by simp [forestCut, hv, hva]
      simp only [cutHeightAux, ite_eq_right hva, hparent, ih hp]

theorem cutAncestorAux_forestCut {x : SignSequence} {n : ℕ} {s : State}
    (hs : HasHistory x n s) (hn : (n : ℕ∞) ≤ extinctionTime x) (a m : ℕ)
    {v : ℕ} (hv : v ∈ cutVertices s a) :
    cutAncestorAux (forestCut s a) a m v = cutAncestorAux s a m v := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    by_cases hva : v ≤ a
    · simp only [cutAncestorAux, ite_eq_left hva]
    · have hvV := (Finset.mem_filter.mp hv).1
      have hp := parent_mem_cutVertices_of_after hs hn hvV (Nat.lt_of_not_ge hva)
      have hparent : (forestCut s a).parent v = s.parent v := by simp [forestCut, hv, hva]
      simp only [cutAncestorAux, ite_eq_right hva, hparent, ih hp]

theorem cutHeight_forestCut {x : SignSequence} {n : ℕ} {s : State}
    (hs : HasHistory x n s) (hn : (n : ℕ∞) ≤ extinctionTime x) (a : ℕ)
    {v : ℕ} (hv : v ∈ cutVertices s a) : cutHeight (forestCut s a) a v = cutHeight s a v := by
  change cutHeightAux (forestCut s a) a ((forestCut s a).height v) v = _
  rw [show (forestCut s a).height v = cutHeight s a v by simp [forestCut, hv],
    cutHeightAux_forestCut hs hn a _ hv]
  exact cutHeightAux_stable_fuel s a (s.height v) v

theorem cutAncestor_forestCut {x : SignSequence} {n : ℕ} {s : State}
    (hs : HasHistory x n s) (hn : (n : ℕ∞) ≤ extinctionTime x) (a : ℕ)
    {v : ℕ} (hv : v ∈ cutVertices s a) : cutAncestor (forestCut s a) a v = cutAncestor s a v := by
  change cutAncestorAux (forestCut s a) a ((forestCut s a).height v) v = _
  rw [show (forestCut s a).height v = cutHeight s a v by simp [forestCut, hv],
    cutAncestorAux_forestCut hs hn a _ hv]
  exact cutAncestorAux_stable_fuel s a (s.height v) v

theorem taggedPopulation_forestCut {x : SignSequence} {n : ℕ} {s : State}
    (hs : HasHistory x n s) (hn : (n : ℕ∞) ≤ extinctionTime x) (a : ℕ) :
    taggedPopulation (forestCut s a) a = taggedPopulation s a := by
  apply Multiset.map_congr rfl
  intro v hv
  have hvC := active_subset_cutVertices hs.current.valid a hv
  rw [cutAncestor_forestCut hs hn a hvC, cutHeight_forestCut hs hn a hvC]

theorem relabel_preserves_cut (e : Equiv.Perm ℕ) (a : ℕ)
    (he : ∀ t : ℕ, a < t → e t = t) (v : ℕ) : e v ≤ a ↔ v ≤ a := by
  constructor
  · intro hev
    by_contra hv
    rw [he v (Nat.lt_of_not_ge hv)] at hev
    exact hv hev
  · intro hv
    by_contra hev
    have hee := he (e v) (Nat.lt_of_not_ge hev)
    have hve : e v = v := e.injective hee
    omega

theorem cutHeightAux_relabel (e : Equiv.Perm ℕ) (s : State) (a m v : ℕ)
    (he : ∀ t : ℕ, a < t → e t = t) :
    cutHeightAux (s.relabel e) a m (e v) = cutHeightAux s a m v := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    by_cases hv : v ≤ a
    · have hev := (relabel_preserves_cut e a he v).mpr hv
      simp only [cutHeightAux, ite_eq_left hv, ite_eq_left hev]
    · have hev : ¬e v ≤ a := fun hh => hv ((relabel_preserves_cut e a he v).mp hh)
      have hp : (s.relabel e).parent (e v) = e (s.parent v) := by simp [State.relabel]
      simp only [cutHeightAux, ite_eq_right hv, ite_eq_right hev, hp, ih]

theorem cutAncestorAux_relabel (e : Equiv.Perm ℕ) (s : State) (a m v : ℕ)
    (he : ∀ t : ℕ, a < t → e t = t) :
    cutAncestorAux (s.relabel e) a m (e v) = e (cutAncestorAux s a m v) := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    by_cases hv : v ≤ a
    · have hev := (relabel_preserves_cut e a he v).mpr hv
      simp only [cutAncestorAux, ite_eq_left hv, ite_eq_left hev]
    · have hev : ¬e v ≤ a := fun hh => hv ((relabel_preserves_cut e a he v).mp hh)
      have hp : (s.relabel e).parent (e v) = e (s.parent v) := by simp [State.relabel]
      simp only [cutAncestorAux, ite_eq_right hv, ite_eq_right hev, hp, ih]

theorem cutHeight_relabel (e : Equiv.Perm ℕ) (s : State) (a v : ℕ)
    (he : ∀ t : ℕ, a < t → e t = t) :
    cutHeight (s.relabel e) a (e v) = cutHeight s a v := by
  unfold cutHeight
  rw [show (s.relabel e).height (e v) = s.height v by simp [State.relabel]]
  exact cutHeightAux_relabel e s a _ v he

theorem cutAncestor_relabel (e : Equiv.Perm ℕ) (s : State) (a v : ℕ)
    (he : ∀ t : ℕ, a < t → e t = t) :
    cutAncestor (s.relabel e) a (e v) = e (cutAncestor s a v) := by
  unfold cutAncestor
  rw [show (s.relabel e).height (e v) = s.height v by simp [State.relabel]]
  exact cutAncestorAux_relabel e s a _ v he

theorem taggedPopulation_relabel (e : Equiv.Perm ℕ) (s : State) (a : ℕ)
    (he : ∀ t : ℕ, a < t → e t = t) :
    taggedPopulation (s.relabel e) a = TaggedPopulation.relabel e (taggedPopulation s a) := by
  unfold taggedPopulation TaggedPopulation.relabel
  change ((s.active.image e).val.map _) = _
  rw [Finset.image_val_of_injOn e.injective.injOn, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro v _
  dsimp only [Function.comp_def]
  rw [cutAncestor_relabel e s a v he, cutHeight_relabel e s a v he]

end Freezing1.Forward
