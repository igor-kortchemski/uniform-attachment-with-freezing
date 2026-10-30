module

public import Freezing1.CanonicalReverseRelabel
public import Mathlib.Logic.Equiv.Basic

/-!
# Exact fibers of the canonical terminal-state map

For the actual terminal vertex set, two timestamped reverse states with the
same canonical state differ only by a permutation of the active labels.
The proof matches active vertices by their incoming-edge IDs and frozen
vertices by their displayed labels, then recovers every parent pointer.
Together with the free action this identifies the complete fiber size.
-/

@[expose] public section

namespace Freezing1.CanonicalTree

open ReverseStamped
open scoped Classical

noncomputable def activeCoordinates {F : Forest} {k : ℕ}
    (hmem : ∀ j, Sum.inl j ∈ F.forest.vertices ↔ j < k)
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v) :
    {j : ℕ // j < k} ≃ {t : ℕ // t ∈ (reverse F).active} :=
  Equiv.ofBijective (fun j => ⟨F.edgeTime (.inl j.val),
    (reverse_active_iff hinj ((hmem j).mpr j.property)).mpr rfl⟩) (by
    constructor
    · intro a b he
      apply Subtype.ext
      exact Sum.inl.inj (hinj _ ((hmem a).mpr a.property) _ ((hmem b).mpr b.property)
        (congrArg Subtype.val he))
    · rintro ⟨t, ht⟩
      obtain ⟨v, hv, he⟩ := Finset.mem_image.mp ht
      obtain ⟨hv, hl⟩ := Finset.mem_filter.mp hv
      cases v with
      | inl j => exact ⟨⟨j, (hmem j).mp hv⟩, Subtype.ext he⟩
      | inr j => simp [reverseLabel] at hl)

@[simp] theorem activeCoordinates_apply {F : Forest} {k : ℕ}
    (hmem : ∀ j, Sum.inl j ∈ F.forest.vertices ↔ j < k)
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v) (j : {j : ℕ // j < k}) :
    (activeCoordinates hmem hinj j).val = F.edgeTime (.inl j.val) := rfl

/-- The displayed freezing label fixes the corresponding canonical vertex ID. -/
theorem frozen_time_eq_of_reverseState_eq {F G : Forest}
    (hF : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v)
    (hG : ∀ u ∈ G.forest.vertices, ∀ v ∈ G.forest.vertices,
      G.edgeTime u = G.edgeTime v → u = v)
    (he : reverseState F = reverseState G) {j : ℕ}
    (hj : Sum.inr j ∈ F.forest.vertices) : G.edgeTime (.inr j) = F.edgeTime (.inr j) := by
  have hobs : reverse F = reverse G :=
    (forward_reverseState hF).symm.trans ((congrArg forward he).trans (forward_reverseState hG))
  have hf : (F.edgeTime (.inr j), j + 1) ∈ (reverse F).frozen :=
    mem_frozenPairs.mpr ⟨.inr j, hj, rfl, rfl⟩
  rw [hobs] at hf
  obtain ⟨v, hv, ht, hl⟩ := mem_frozenPairs.mp hf
  cases v with
  | inl l => simp [reverseLabel] at hl
  | inr l =>
    have heq : l = j := by simpa [reverseLabel] using hl
    simpa only [heq] using ht

/-- Equal canonical states supply a supported active permutation matching
every actual incoming-edge ID; frozen labels are fixed pointwise. -/
theorem exists_activePermutation_matching_times {x : SignSequence} {n : ℕ} {F G : Forest}
    (hvF : F.forest.vertices = Reverse.phaseLabels x n 0)
    (hvG : G.forest.vertices = Reverse.phaseLabels x n 0)
    (hF : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v)
    (hG : ∀ u ∈ G.forest.vertices, ∀ v ∈ G.forest.vertices,
      G.edgeTime u = G.edgeTime v → u = v)
    (he : reverseState F = reverseState G) :
    ∃ σ ∈ activePermutations (activeCount x n).toNat,
      ∀ v ∈ F.forest.vertices, G.edgeTime (activeEquiv σ v) = F.edgeTime v := by
  let k := (activeCount x n).toNat
  have hmF : ∀ j, Sum.inl j ∈ F.forest.vertices ↔ j < k := by
    intro j; simp [hvF, Reverse.phaseLabels, k]
  have hmG : ∀ j, Sum.inl j ∈ G.forest.vertices ↔ j < k := by
    intro j; simp [hvG, Reverse.phaseLabels, k]
  have ha : (reverse F).active = (reverse G).active := congrArg Forward.State.active he
  let eF := activeCoordinates hmF hF
  let eG := activeCoordinates hmG hG
  let eA : {t : ℕ // t ∈ (reverse F).active} ≃ {t : ℕ // t ∈ (reverse G).active} :=
    Equiv.subtypeEquivRight (fun t => by rw [ha])
  let π : Equiv.Perm {j : ℕ // j < k} := eF.trans (eA.trans eG.symm)
  let σ : Equiv.Perm ℕ := π.subtypeCongr (Equiv.refl {j : ℕ // ¬j < k})
  have hσ : σ ∈ activePermutations k := by
    apply mem_perms_of_finset_iff.mpr
    intro j hj
    by_contra hn
    have hn' : ¬j < k := by simpa using hn
    apply hj
    simp [σ, Equiv.Perm.subtypeCongr.right_apply π _ hn']
  refine ⟨σ, hσ, ?_⟩
  intro v hv
  cases v with
  | inl j =>
    have hj : j < k := (hmF j).mp hv
    have hcoord : eG (π ⟨j, hj⟩) = eA (eF ⟨j, hj⟩) := by simp [π]
    have ht := congrArg Subtype.val hcoord
    simpa [σ, Equiv.Perm.subtypeCongr.left_apply π _ hj, eF, eG, eA] using ht
  | inr j => exact frozen_time_eq_of_reverseState_eq hF hG he hv

/-- Once the coordinate functions agree, canonical parents recover the whole
functional forest, including its proved unused defaults. -/
theorem eq_of_reverseState_eq_of_edgeTime_eq {F G : Forest}
    (hdF : CanonicalDefaults F) (hdG : CanonicalDefaults G)
    (hv : F.forest.vertices = G.forest.vertices)
    (ht : F.edgeTime = G.edgeTime)
    (hF : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v)
    (hG : ∀ u ∈ G.forest.vertices, ∀ v ∈ G.forest.vertices,
      G.edgeTime u = G.edgeTime v → u = v)
    (he : reverseState F = reverseState G) : F = G := by
  apply eq_of_parent_edgeTime_eq hdF hdG hv _ ht
  funext v
  by_cases hvF : v ∈ F.forest.vertices
  · have hvG : v ∈ G.forest.vertices := hv ▸ hvF
    apply hG _ (hv ▸ F.forest.parent_mem v hvF) _ (G.forest.parent_mem v hvG)
    calc
      G.edgeTime (F.forest.parent v) = F.edgeTime (F.forest.parent v) := congrFun ht _ |>.symm
      _ = (reverseState F).parent (F.edgeTime v) := (reverseState_vertex_data hF hvF).1.symm
      _ = (reverseState G).parent (G.edgeTime v) := by rw [he, ht]
      _ = G.edgeTime (G.forest.parent v) := (reverseState_vertex_data hG hvG).1
  · have hvG : v ∉ G.forest.vertices := by rwa [← hv]
    rw [(hdF.outside v hvF).1, (hdG.outside v hvG).1]

/-- Every canonical fiber is contained in one active-label orbit. Together
with `reverseState_relabel`, this is equality of the two sets. -/
theorem exists_relabel_of_reverseState_eq {x : SignSequence} {n : ℕ} {F G : Forest}
    (hdF : CanonicalDefaults F) (hdG : CanonicalDefaults G)
    (hvF : F.forest.vertices = Reverse.phaseLabels x n 0)
    (hvG : G.forest.vertices = Reverse.phaseLabels x n 0)
    (hF : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v)
    (hG : ∀ u ∈ G.forest.vertices, ∀ v ∈ G.forest.vertices,
      G.edgeTime u = G.edgeTime v → u = v)
    (he : reverseState F = reverseState G) :
    ∃ σ ∈ activePermutations (activeCount x n).toNat, relabel F (activeEquiv σ) = G := by
  obtain ⟨σ, hσ, htimes⟩ := exists_activePermutation_matching_times hvF hvG hF hG he
  let e := activeEquiv σ
  have hv : (relabel F e).forest.vertices = G.forest.vertices := by
    change F.forest.vertices.map e.toEmbedding = _
    rw [hvF, activePermutation_phaseLabels hσ, hvG]
  have hd := hdF.relabel e
  have ht : (relabel F e).edgeTime = G.edgeTime := by
    funext w
    by_cases hw : w ∈ G.forest.vertices
    · obtain ⟨v, rfl⟩ := e.surjective w
      have hmem : e v ∈ (relabel F e).forest.vertices := hv.symm ▸ hw
      have hvF' : v ∈ F.forest.vertices := by simpa [relabel] using hmem
      exact (relabel_time F e v).trans (htimes v hvF').symm
    · have hw' : w ∉ (relabel F e).forest.vertices := by rwa [hv]
      rw [(hd.outside w hw').2.2.2, (hdG.outside w hw).2.2.2]
  refine ⟨σ, hσ, eq_of_reverseState_eq_of_edgeTime_eq hd hdG hv ht
    (relabel_time_injective hF e) hG ?_⟩
  exact (reverseState_relabel hF σ).trans he

theorem terminal_history_data {x : SignSequence} {n : ℕ} {F : Forest}
    (hh : HasPartialHistory x n n F) : PhaseData x n 0 F := by
  simpa only [Nat.sub_self] using hh.current

theorem terminal_history_times_injective {x : SignSequence} {n : ℕ} {F : Forest}
    (hh : HasPartialHistory x n n F) :
    ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v := by
  have hd := terminal_history_data hh
  apply hd.times.edgeTime_injective_of_one_root
  simpa [activeCount_zero] using hd.valid.roots_card

/-- Exact reachable fiber: every element and every active renaming has a
legal reverse history, and no other reachable terminal state shares the image. -/
theorem terminalFiber_eq_activeOrbit {x : SignSequence} {n : ℕ} {F : Forest}
    (hh : HasPartialHistory x n n F) :
    {G : Forest | HasPartialHistory x n n G ∧ reverseState G = reverseState F} =
      ((activePermutations (activeCount x n).toNat).image
        (fun σ => relabel F (activeEquiv σ)) : Set Forest) := by
  have hdF := terminal_history_data hh
  have hF := terminal_history_times_injective hh
  ext G
  constructor
  · rintro ⟨hhG, he⟩
    have hdG := terminal_history_data hhG
    obtain ⟨σ, hσ, hσG⟩ := exists_relabel_of_reverseState_eq hdF.defaults hdG.defaults
      hdF.valid.vertices_eq hdG.valid.vertices_eq hF (terminal_history_times_injective hhG) he.symm
    exact Finset.mem_image.mpr ⟨σ, hσ, hσG⟩
  · intro hG
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hG
    exact ⟨hh.relabel hσ, reverseState_relabel hF σ⟩

end Freezing1.CanonicalTree
