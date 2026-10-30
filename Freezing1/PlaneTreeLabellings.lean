module

public import Freezing1.PlaneTreeLabelledTopology

/-!
# Every plane shape admits every assignment of its vertex and edge labels

This semantic bridge shows that the closed labelled-coordinate carrier
imposes no chronological or distinctness condition on the actual labels.
-/

@[expose] public section

namespace Freezing1.PlaneLabelled

open scoped Classical

variable {V E : Type*}

theorem LabelSlot.ext_label {s t : LabelSlot V} (h : s.label = t.label) : s = t := by
  cases s
  cases t
  cases h
  rfl

abbrev Vertex (T : PlaneTree.Tree) := {u : PlaneTree.Address // PlaneTree.Present T u}
abbrev Edge (T : PlaneTree.Tree) :=
  {u : PlaneTree.Address // PlaneTree.Present T u ∧ u ≠ []}

noncomputable def decorate (T : PlaneTree.Tree) (v : Vertex T → V) (e : Edge T → E) : Tree V E := by
  let vs : PlaneTree.Address → LabelSlot V := fun u =>
    ⟨if hu : PlaneTree.Present T u then some (v ⟨u, hu⟩) else none⟩
  let es : PlaneTree.Address → LabelSlot E := fun u =>
    ⟨if hu : PlaneTree.Present T u ∧ u ≠ [] then some (e ⟨u, hu⟩) else none⟩
  refine ⟨(T, vs, es), ?_⟩
  intro u
  dsimp only
  constructor
  · by_cases hu : PlaneTree.Present T u <;> simp [vs, presence, hu]
  · by_cases hp : PlaneTree.Present T u
    · by_cases hu : u = [] <;> simp [es, edgePresence, presence, hp, hu]
    · simp [es, edgePresence, presence, hp]

@[simp] theorem shape_decorate (T : PlaneTree.Tree) (v : Vertex T → V) (e : Edge T → E) :
    shape (decorate T v e) = T := rfl

theorem vertexSlot_decorate (T : PlaneTree.Tree) (v : Vertex T → V) (e : Edge T → E)
    (u : Vertex T) : (vertexSlot (decorate T v e) u.val).label = some (v u) := by
  simp [vertexSlot, decorate, u.property]

theorem edgeSlot_decorate (T : PlaneTree.Tree) (v : Vertex T → V) (e : Edge T → E)
    (u : Edge T) : (edgeSlot (decorate T v e) u.val).label = some (e u) := by
  simp [edgeSlot, decorate, u.property]

theorem vertexSlot_isSome (T : Tree V E) (u : Vertex (shape T)) :
    (vertexSlot T u.val).label.isSome := by
  have hh := (T.property u.val).1
  have hu : PlaneTree.Present T.val.1 u.val := u.property
  simpa only [vertexSlot, presence, decide_eq_true hu] using hh

theorem edgeSlot_isSome (T : Tree V E) (u : Edge (shape T)) :
    (edgeSlot T u.val).label.isSome := by
  have hh := (T.property u.val).2
  have hu : PlaneTree.Present T.val.1 u.val := u.property.1
  simpa only [edgeSlot, edgePresence, ite_eq_right u.property.2,
    presence, decide_eq_true hu] using hh

noncomputable def vertexLabel (T : Tree V E) (u : Vertex (shape T)) : V :=
  (vertexSlot T u.val).label.get (vertexSlot_isSome T u)

noncomputable def edgeLabel (T : Tree V E) (u : Edge (shape T)) : E :=
  (edgeSlot T u.val).label.get (edgeSlot_isSome T u)

theorem some_vertexLabel (T : Tree V E) (u : Vertex (shape T)) :
    some (vertexLabel T u) = (vertexSlot T u.val).label := Option.some_get _

theorem some_edgeLabel (T : Tree V E) (u : Edge (shape T)) :
    some (edgeLabel T u) = (edgeSlot T u.val).label := Option.some_get _

theorem tree_ext {S T : Tree V E} (hs : shape S = shape T)
    (hv : ∀ u, vertexSlot S u = vertexSlot T u) (he : ∀ u, edgeSlot S u = edgeSlot T u) : S = T := by
  apply Subtype.ext
  exact Prod.ext hs (Prod.ext (funext hv) (funext he))

theorem decorate_recovered (T : Tree V E) :
    decorate (shape T) (vertexLabel T) (edgeLabel T) = T := by
  refine tree_ext (S := decorate (shape T) (vertexLabel T) (edgeLabel T)) (T := T) rfl ?_ ?_
  · intro u
    apply LabelSlot.ext_label
    by_cases hu : PlaneTree.Present (shape T) u
    · rw [vertexSlot_decorate (shape T) (vertexLabel T) (edgeLabel T) ⟨u, hu⟩]
      exact some_vertexLabel T ⟨u, hu⟩
    · have hs := vertexSlot_empty_of_absent T u hu
      rw [vertexSlot_empty_of_absent _ _ (by simpa only [shape_decorate] using hu), hs]
  · intro u
    apply LabelSlot.ext_label
    by_cases hu : PlaneTree.Present (shape T) u ∧ u ≠ []
    · rw [edgeSlot_decorate (shape T) (vertexLabel T) (edgeLabel T) ⟨u, hu⟩]
      exact some_edgeLabel T ⟨u, hu⟩
    · by_cases hroot : u = []
      · subst u
        rw [root_edgeSlot, root_edgeSlot]
      · have habsent : ¬PlaneTree.Present (shape T) u := fun hp => hu ⟨hp, hroot⟩
        rw [edgeSlot_empty_of_absent _ _ (by simpa only [shape_decorate] using habsent),
          edgeSlot_empty_of_absent T u habsent]

/-- Every encoded tree is precisely its shape with its actual labels;
the carrier excludes no nonchronological or repeated label assignment. -/
theorem decorate_surjective : Function.Surjective
    (fun p : Σ T : PlaneTree.Tree, (Vertex T → V) × (Edge T → E) => decorate p.1 p.2.1 p.2.2) := by
  intro T
  exact ⟨⟨shape T, vertexLabel T, edgeLabel T⟩, decorate_recovered T⟩

end Freezing1.PlaneLabelled
