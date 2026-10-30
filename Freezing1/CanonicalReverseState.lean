module

public import Freezing1.CanonicalTreeObservable
public import Freezing1.ForwardStateDefaults

/-!
# Full forward coordinates for a timestamped reverse tree

Incoming edge times select canonical vertex representatives. Parent pointers,
verified depths and frozen labels are transported to the forward State type;
unused function values are the forward defaults. Forgetting these additional
functional fields is exactly the already defined common tree observable.
No equality between the two process laws is assumed here.
-/

@[expose] public section

namespace Freezing1.CanonicalTree

open scoped Classical

theorem Observable.ext_data {S T : Observable} (hv : S.vertices = T.vertices)
    (hg : S.graph = T.graph) (ha : S.active = T.active) (hf : S.frozen = T.frozen) : S = T := by
  cases S
  cases T
  cases hv
  cases hg
  cases ha
  cases hf
  rfl

noncomputable def vertexOfId (F : ReverseStamped.Forest) (t : ℕ)
    (ht : t ∈ (reverse F).vertices) : ℕ ⊕ ℕ :=
  Classical.choose (Finset.mem_image.mp ht)

theorem vertexOfId_mem (F : ReverseStamped.Forest) (t : ℕ)
    (ht : t ∈ (reverse F).vertices) : vertexOfId F t ht ∈ F.forest.vertices :=
  (Classical.choose_spec (Finset.mem_image.mp ht)).1

theorem vertexOfId_time (F : ReverseStamped.Forest) (t : ℕ)
    (ht : t ∈ (reverse F).vertices) : F.edgeTime (vertexOfId F t ht) = t :=
  (Classical.choose_spec (Finset.mem_image.mp ht)).2

theorem vertexOfId_eq {F : ReverseStamped.Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v)
    {v : ℕ ⊕ ℕ} (hv : v ∈ F.forest.vertices)
    (ht : F.edgeTime v ∈ (reverse F).vertices) : vertexOfId F (F.edgeTime v) ht = v :=
  hinj _ (vertexOfId_mem _ _ _) _ hv (vertexOfId_time _ _ _)

/-- Transport the complete parent/depth representation while retaining the
same canonical graph and displayed labels as the source observable. -/
noncomputable def reverseState (F : ReverseStamped.Forest) : Forward.State where
  vertices := (reverse F).vertices
  graph := (reverse F).graph
  active := (reverse F).active
  parent t := if ht : t ∈ (reverse F).vertices then
    F.edgeTime (F.forest.parent (vertexOfId F t ht)) else 0
  height t := if ht : t ∈ (reverse F).vertices then F.forest.depth (vertexOfId F t ht) else 0
  frozenAt t := if ht : t ∈ (reverse F).vertices then reverseLabel (vertexOfId F t ht) else none

/-- Every actual vertex keeps its parent, height and frozen label exactly. -/
theorem reverseState_vertex_data {F : ReverseStamped.Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v)
    {v : ℕ ⊕ ℕ} (hv : v ∈ F.forest.vertices) :
    (reverseState F).parent (F.edgeTime v) = F.edgeTime (F.forest.parent v) ∧
    (reverseState F).height (F.edgeTime v) = F.forest.depth v ∧
    (reverseState F).frozenAt (F.edgeTime v) = reverseLabel v := by
  have ht : F.edgeTime v ∈ (reverse F).vertices := Finset.mem_image_of_mem _ hv
  simp only [reverseState, dite_eq_left ht, vertexOfId_eq hinj hv]
  trivial

/-- The complete transported state has exactly the common source observable. -/
theorem forward_reverseState {F : ReverseStamped.Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v) : forward (reverseState F) = reverse F := by
  have hf : (forward (reverseState F)).frozen = (reverse F).frozen := by
    ext p
    rcases p with ⟨t,l⟩
    rw [forward_frozen_iff]
    change (t ∈ (reverse F).vertices ∧ (reverseState F).frozenAt t = some l) ↔
      (t,l) ∈ frozenPairs F.forest.vertices F.edgeTime reverseLabel
    rw [mem_frozenPairs]
    constructor
    · rintro ⟨ht, hl⟩
      refine ⟨vertexOfId F t ht, vertexOfId_mem _ _ _, vertexOfId_time _ _ _, ?_⟩
      simpa only [reverseState, dite_eq_left ht] using hl
    · rintro ⟨v, hv, rfl, hl⟩
      exact ⟨Finset.mem_image_of_mem _ hv, (reverseState_vertex_data hinj hv).2.2.trans hl⟩
  exact Observable.ext_data rfl rfl rfl hf

/-- Unused IDs have exactly the forward defaults, and roots have parent ID0. -/
theorem reverseState_defaults {x : SignSequence} {n i : ℕ} {F : ReverseStamped.Forest}
    (ht : ReverseStamped.TimesValidAt x n i F) : Forward.CanonicalDefaults (reverseState F) := by
  constructor
  · by_cases hzero : 0 ∈ (reverse F).vertices
    · have hv := vertexOfId_mem F 0 hzero
      have htime := vertexOfId_time F 0 hzero
      have hr := (ht.root_zero _ hv).mp htime
      simp only [reverseState, dite_eq_left hzero, F.forest.parent_of_root hr, htime]
    · simp only [reverseState, dite_eq_right hzero]
  · intro t hnot
    change t ∉ (reverse F).vertices at hnot
    simp only [reverseState, dite_eq_right hnot]
    trivial

/-- Parent IDs strictly precede child IDs on every actual parent edge. -/
theorem reverseState_parent_lt {F : ReverseStamped.Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v)
    (ho : ReverseStamped.TimestampOrder F) {t : ℕ}
    (ht : t ∈ (reverseState F).vertices) (ht0 : t ≠ 0) :
    (reverseState F).parent t < t := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
  rw [(reverseState_vertex_data hinj hv).1]
  exact ho.parent_lt v hv ht0

end Freezing1.CanonicalTree
