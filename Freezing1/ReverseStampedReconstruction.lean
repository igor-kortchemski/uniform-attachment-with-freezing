module

public import Freezing1.RootedForestExtensionality
public import Freezing1.ReverseStampedDefaults

/-!
# One-step reconstruction of timestamped reverse histories

The edge carrying the current time uniquely identifies its child and parent.
Deleting that parent edge restores the previous parent map and timestamps.
Root/depth extensionality and actual outside defaults then restore the entire
previous state. Singleton insertion is likewise reversible on fresh labels.
These are deterministic history-uniqueness ingredients, not a terminal
probability formula.
-/

@[expose] public section

namespace Freezing1.ReverseStamped

open scoped Classical

theorem Forest.ext_data {F G : Forest} (hf : F.forest = G.forest)
    (ht : F.edgeTime = G.edgeTime) : F = G := by
  cases F
  cases G
  cases hf
  cases ht
  rfl

/-- Exact full-state equality from parent maps and timestamps, using the
proved actual outside defaults for root/depth data. -/
theorem eq_of_parent_edgeTime_eq {F G : Forest}
    (hF : CanonicalDefaults F) (hG : CanonicalDefaults G)
    (hv : F.forest.vertices = G.forest.vertices) (hp : F.forest.parent = G.forest.parent)
    (ht : F.edgeTime = G.edgeTime) : F = G := by
  apply Forest.ext_data _ ht
  exact RootedForest.eq_of_parent_eq hv hp
    (fun v h => ⟨(hF.outside v h).2.1, (hF.outside v h).2.2.1⟩)
    (fun v h => ⟨(hG.outside v h).2.1, (hG.outside v h).2.2.1⟩)

/-- A legal merged output uniquely determines both its predecessor forest
and the ordered root pair, at every reverse phase. -/
theorem joinChoice_predecessor_eq {x : SignSequence} {n i : ℕ} {F G : Forest}
    (hF : TimesValidAt x n (i + 1) F) (hG : TimesValidAt x n (i + 1) G)
    (hdF : CanonicalDefaults F) (hdG : CanonicalDefaults G)
    {p q : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)}
    (hp : p ∈ F.forest.roots.offDiag) (hq : q ∈ G.forest.roots.offDiag)
    (he : joinChoice F (i + 1) p = joinChoice G (i + 1) q) : F = G ∧ p = q := by
  have hp' := Finset.mem_offDiag.mp hp
  have hq' := Finset.mem_offDiag.mp hq
  have hv : F.forest.vertices = G.forest.vertices := by
    have h := congrArg (fun H : Forest => H.forest.vertices) he
    simpa only [joinChoice, dite_eq_left hp, dite_eq_left hq, RootedForest.join_vertices] using h
  have hb : p.2 = q.2 := by
    by_contra hb
    have htime := congrArg (fun H : Forest => H.edgeTime p.2) he
    simp only [joinChoice, dite_eq_left hp, dite_eq_left hq, Function.update_self,
      Function.update_of_ne hb] at htime
    have hpG : p.2 ∈ G.forest.vertices := hv ▸ (RootedForest.mem_roots.mp hp'.2.1).1
    have hnonzero : G.edgeTime p.2 ≠ 0 := by omega
    have hlarge := (hG.range p.2 hpG hnonzero).1
    omega
  have ha : p.1 = q.1 := by
    have hparent := congrArg (fun H : Forest => H.forest.parent p.2) he
    simpa only [joinChoice, dite_eq_left hp, dite_eq_left hq,
      RootedForest.join, hb, ↓reduceIte] using hparent
  have hpair : p = q := Prod.ext ha hb
  have hparent : F.forest.parent = G.forest.parent := by
    funext v
    by_cases hbv : v = p.2
    · subst v
      exact (F.forest.parent_of_root hp'.2.1).trans
        (by simpa only [← hb] using (G.forest.parent_of_root hq'.2.1).symm)
    · have hbq : v ≠ q.2 := by simpa only [← hb] using hbv
      have h := congrArg (fun H : Forest => H.forest.parent v) he
      simpa only [joinChoice, dite_eq_left hp, dite_eq_left hq,
        RootedForest.join, hbv, hbq, ↓reduceIte] using h
  have htime : F.edgeTime = G.edgeTime := by
    funext v
    by_cases hbv : v = p.2
    · subst v
      have hzF := (hF.root_zero p.2 (RootedForest.mem_roots.mp hp'.2.1).1).mpr hp'.2.1
      have hzG := (hG.root_zero q.2 (RootedForest.mem_roots.mp hq'.2.1).1).mpr hq'.2.1
      simpa only [← hb] using hzF.trans hzG.symm
    · have hbq : v ≠ q.2 := by simpa only [← hb] using hbv
      have h := congrArg (fun H : Forest => H.edgeTime v) he
      simpa only [joinChoice, dite_eq_left hp, dite_eq_left hq,
        Function.update_of_ne hbv, Function.update_of_ne hbq] using h
  exact ⟨eq_of_parent_edgeTime_eq hdF hdG hv hparent htime, hpair⟩

/-- Inserting the prescribed fresh singleton also uniquely determines its
predecessor, including all otherwise unused functional values. -/
theorem insertLabel_predecessor_eq {F G : Forest} {i : ℕ}
    (hdF : CanonicalDefaults F) (hdG : CanonicalDefaults G)
    (hf : Sum.inr i ∉ F.forest.vertices) (hg : Sum.inr i ∉ G.forest.vertices)
    (he : insertLabel F i = insertLabel G i) : F = G := by
  have hv : F.forest.vertices = G.forest.vertices := by
    have h := congrArg (fun H : Forest => H.forest.vertices.erase (.inr i)) he
    simpa only [insertLabel, dite_eq_right hf, dite_eq_right hg, RootedForest.adjoin_vertices,
      Finset.erase_insert hf, Finset.erase_insert hg] using h
  have hp : F.forest.parent = G.forest.parent := by
    funext v
    by_cases hvi : v = Sum.inr i
    · subst v
      exact (hdF.outside _ hf).1.trans (hdG.outside _ hg).1.symm
    · have h := congrArg (fun H : Forest => H.forest.parent v) he
      simpa only [insertLabel, dite_eq_right hf, dite_eq_right hg,
        RootedForest.adjoin, hvi, ↓reduceIte] using h
  have ht : F.edgeTime = G.edgeTime := by
    funext v
    by_cases hvi : v = Sum.inr i
    · subst v
      exact (hdF.outside _ hf).2.2.2.trans (hdG.outside _ hg).2.2.2.symm
    · have h := congrArg (fun H : Forest => H.edgeTime v) he
      simpa only [insertLabel, dite_eq_right hf, dite_eq_right hg,
        Function.update_of_ne hvi] using h
  exact eq_of_parent_edgeTime_eq hdF hdG hv hp ht

/-- A legal deterministic step of the timestamped reverse construction. -/
def LegalStep (x : SignSequence) (i : ℕ) (F H : Forest) : Prop :=
  if x (i + 1) then ∃ p ∈ F.forest.roots.offDiag, H = joinChoice F (i + 1) p
  else H = insertLabel F i

/-- Under the actual phase invariants, the predecessor of any legal output
is unique for either sign of the schedule. -/
theorem legalStep_predecessor_eq {x : SignSequence} {n i : ℕ} {F G H : Forest}
    (hvF : Reverse.ValidAt x n (i + 1) F.forest)
    (hvG : Reverse.ValidAt x n (i + 1) G.forest)
    (htF : TimesValidAt x n (i + 1) F) (htG : TimesValidAt x n (i + 1) G)
    (hdF : CanonicalDefaults F) (hdG : CanonicalDefaults G)
    (hsF : LegalStep x i F H) (hsG : LegalStep x i G H) : F = G := by
  cases hx : x (i + 1)
  · simp only [LegalStep, hx, Bool.false_eq_true, ↓reduceIte] at hsF hsG
    have hf : Sum.inr i ∉ F.forest.vertices := by
      rw [hvF.vertices_eq]
      exact Reverse.fresh_freezing_label x n i
    have hg : Sum.inr i ∉ G.forest.vertices := by
      rw [hvG.vertices_eq]
      exact Reverse.fresh_freezing_label x n i
    exact insertLabel_predecessor_eq hdF hdG hf hg (hsF.symm.trans hsG)
  · simp only [LegalStep, hx, ↓reduceIte] at hsF hsG
    obtain ⟨p, hp, heF⟩ := hsF
    obtain ⟨q, hq, heG⟩ := hsG
    exact (joinChoice_predecessor_eq htF htG hdF hdG hp hq (heF.symm.trans heG)).1

/-- The terminal timestamped tree determines every earlier reverse phase.
This verifies the uniqueness part of the source's reverse-history argument;
it does not assume or identify a terminal probability. -/
theorem history_eq_of_terminal_eq {x : SignSequence} {n : ℕ} (F G : ℕ → Forest)
    (hvF : ∀ i ≤ n, Reverse.ValidAt x n i (F i).forest)
    (hvG : ∀ i ≤ n, Reverse.ValidAt x n i (G i).forest)
    (htF : ∀ i ≤ n, TimesValidAt x n i (F i))
    (htG : ∀ i ≤ n, TimesValidAt x n i (G i))
    (hdF : ∀ i ≤ n, CanonicalDefaults (F i))
    (hdG : ∀ i ≤ n, CanonicalDefaults (G i))
    (hsF : ∀ i < n, LegalStep x i (F (i + 1)) (F i))
    (hsG : ∀ i < n, LegalStep x i (G (i + 1)) (G i))
    (hzero : F 0 = G 0) : ∀ i ≤ n, F i = G i := by
  intro i
  induction i with
  | zero => exact fun _ => hzero
  | succ i ih =>
    intro hi
    have hei := ih (by omega)
    exact legalStep_predecessor_eq (hvF (i + 1) hi) (hvG (i + 1) hi)
      (htF (i + 1) hi) (htG (i + 1) hi) (hdF (i + 1) hi) (hdG (i + 1) hi)
      (hsF i (by omega)) (by simpa only [hei] using hsG i (by omega))

end Freezing1.ReverseStamped
