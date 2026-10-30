module

public import Freezing1.CanonicalReverseState
public import Freezing1.ReverseStampedRelabel
public import Freezing1.ForwardReconstruction

/-!
# The canonical tree forgets exactly the names of active vertices

Relabeling active vertices leaves the full canonical forward state unchanged.
Frozen labels, parent pointers, heights and edge dates are retained. These
deterministic statements support the later fiber calculation; no probability
identity is used here.
-/

@[expose] public section

namespace Freezing1.CanonicalTree

open ReverseStamped
open scoped Classical

@[simp] theorem reverseLabel_activeEquiv (σ : Equiv.Perm ℕ) (v : ℕ ⊕ ℕ) :
    reverseLabel (activeEquiv σ v) = reverseLabel v := by cases v <;> rfl

theorem relabel_time_injective {F : Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v)
    (e : (ℕ ⊕ ℕ) ≃ (ℕ ⊕ ℕ)) :
    ∀ u ∈ (relabel F e).forest.vertices, ∀ v ∈ (relabel F e).forest.vertices,
      (relabel F e).edgeTime u = (relabel F e).edgeTime v → u = v := by
  intro u hu v hv he
  obtain ⟨a, rfl⟩ := e.surjective u
  obtain ⟨b, rfl⟩ := e.surjective v
  exact congrArg e (hinj a (by simpa [relabel] using hu) b
    (by simpa [relabel] using hv) (by simpa using he))

theorem reverse_relabel (F : Forest) (σ : Equiv.Perm ℕ) :
    reverse (relabel F (activeEquiv σ)) = reverse F := by
  let e := activeEquiv σ
  apply Observable.ext_data
  · ext t
    simp only [reverse, Finset.mem_image]
    change (∃ v ∈ (F.forest.relabel e).vertices, F.edgeTime (e.symm v) = t) ↔
      ∃ v ∈ F.forest.vertices, F.edgeTime v = t
    constructor
    · rintro ⟨v, hv, ht⟩
      obtain ⟨u, rfl⟩ := e.surjective v
      exact ⟨u, by simpa using hv, by simpa using ht⟩
    · rintro ⟨v, hv, ht⟩
      exact ⟨e v, by simpa using hv, by simpa using ht⟩
  · ext a b
    change (a ≠ b ∧ ∃ u ∈ (F.forest.relabel e).vertices,
      ∃ v ∈ (F.forest.relabel e).vertices,
        F.edgeTime (e.symm u) = a ∧ F.edgeTime (e.symm v) = b ∧
        (F.forest.relabel e).graph.Adj u v) ↔
      (a ≠ b ∧ ∃ u ∈ F.forest.vertices, ∃ v ∈ F.forest.vertices,
        F.edgeTime u = a ∧ F.edgeTime v = b ∧ F.forest.graph.Adj u v)
    constructor
    · rintro ⟨hne, u, hu, v, hv, hua, hvb, hadj⟩
      obtain ⟨u', rfl⟩ := e.surjective u
      obtain ⟨v', rfl⟩ := e.surjective v
      exact ⟨hne, u', by simpa using hu, v', by simpa using hv,
        by simpa using hua, by simpa using hvb, by simpa using hadj⟩
    · rintro ⟨hne, u, hu, v, hv, hua, hvb, hadj⟩
      exact ⟨hne, e u, by simpa using hu, e v, by simpa using hv,
        by simpa using hua, by simpa using hvb, by simpa using hadj⟩
  · ext t
    simp only [reverse, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨v, ⟨hv, hl⟩, ht⟩
      obtain ⟨u, rfl⟩ := e.surjective v
      exact ⟨u, ⟨by simpa [relabel, e] using hv,
        by simpa [e] using hl⟩, by simpa [e] using ht⟩
    · rintro ⟨v, ⟨hv, hl⟩, ht⟩
      exact ⟨e v, ⟨by simpa [relabel, e] using hv,
        by simpa [e] using hl⟩, by simpa [e] using ht⟩
  · ext p
    rcases p with ⟨t, l⟩
    simp only [reverse, mem_frozenPairs]
    constructor
    · rintro ⟨v, hv, ht, hl⟩
      obtain ⟨u, rfl⟩ := e.surjective v
      exact ⟨u, by simpa [relabel, e] using hv, by simpa [e] using ht,
        by simpa [e] using hl⟩
    · rintro ⟨v, hv, ht, hl⟩
      exact ⟨e v, by simpa [relabel, e] using hv, by simpa [e] using ht,
        by simpa [e] using hl⟩

/-- The complete canonical state, not only its unlabelled graph, is invariant. -/
theorem reverseState_relabel {F : Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v) (σ : Equiv.Perm ℕ) :
    reverseState (relabel F (activeEquiv σ)) = reverseState F := by
  let e := activeEquiv σ
  have heq := reverse_relabel F σ
  have hinj' := relabel_time_injective hinj e
  have hdata : ∀ t ∈ (reverse F).vertices,
      (reverseState (relabel F e)).parent t = (reverseState F).parent t ∧
      (reverseState (relabel F e)).height t = (reverseState F).height t ∧
      (reverseState (relabel F e)).frozenAt t = (reverseState F).frozenAt t := by
    intro t ht
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
    have hv' : e v ∈ (relabel F e).forest.vertices := by simpa [relabel] using hv
    have hd := reverseState_vertex_data hinj hv
    have hd' := reverseState_vertex_data hinj' hv'
    simpa [relabel, e, RootedForest.relabel, hd.1, hd.2.1, hd.2.2] using hd'
  apply Forward.State.ext_data
  · exact congrArg Observable.vertices heq
  · exact congrArg Observable.active heq
  · exact congrArg Observable.graph heq
  · funext t
    by_cases ht : t ∈ (reverse F).vertices
    · exact (hdata t ht).1
    · have ht' : t ∉ (reverse (relabel F (activeEquiv σ))).vertices := by simpa only [heq] using ht
      simp only [reverseState, dite_eq_right ht, dite_eq_right ht']
  · funext t
    by_cases ht : t ∈ (reverse F).vertices
    · exact (hdata t ht).2.1
    · have ht' : t ∉ (reverse (relabel F (activeEquiv σ))).vertices := by simpa only [heq] using ht
      simp only [reverseState, dite_eq_right ht, dite_eq_right ht']
  · funext t
    by_cases ht : t ∈ (reverse F).vertices
    · exact (hdata t ht).2.2
    · have ht' : t ∉ (reverse (relabel F (activeEquiv σ))).vertices := by simpa only [heq] using ht
      simp only [reverseState, dite_eq_right ht, dite_eq_right ht']

end Freezing1.CanonicalTree
