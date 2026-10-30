module

public import Freezing1.ForwardComponentContinuation
public import Freezing1.CanonicalUniformSampling

/-! Exact relabeling equivariance of complete forward forest continuations. -/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable def State.relabel (e : Equiv.Perm ℕ) (s : State) : State where
  vertices := s.vertices.image e
  active := s.active.image e
  graph := s.graph.comap e.symm
  parent v := e (s.parent (e.symm v))
  height v := s.height (e.symm v)
  frozenAt v := s.frozenAt (e.symm v)

theorem relabel_attach (e : Equiv.Perm ℕ) (s : State) (t p : ℕ) :
    (attach s t p).relabel e = attach (s.relabel e) (e t) (e p) := by
  apply State.ext_data
  · exact Finset.image_insert _ _ _
  · exact Finset.image_insert _ _ _
  · ext u v
    change (s.graph ⊔ SimpleGraph.edge p t).Adj (e.symm u) (e.symm v) ↔
      ((s.graph.comap e.symm) ⊔ SimpleGraph.edge (e p) (e t)).Adj u v
    simp only [SimpleGraph.sup_adj, SimpleGraph.comap_adj, SimpleGraph.edge_adj]
    have hne : (e.symm u ≠ e.symm v) ↔ u ≠ v := not_congr e.symm.injective.eq_iff
    simp only [Equiv.symm_apply_eq, hne]
  · funext v
    by_cases hv : v = e t
    · subst v
      simp [State.relabel, attach]
    · have hv' : e.symm v ≠ t := by intro hh; exact hv (by simpa using congrArg e hh)
      simp [State.relabel, attach, hv, hv']
  · funext v
    by_cases hv : v = e t
    · subst v
      simp [State.relabel, attach]
    · have hv' : e.symm v ≠ t := by intro hh; exact hv (by simpa using congrArg e hh)
      simp [State.relabel, attach, hv, hv']
  · funext v
    by_cases hv : v = e t
    · subst v
      simp [State.relabel, attach]
    · have hv' : e.symm v ≠ t := by intro hh; exact hv (by simpa using congrArg e hh)
      simp [State.relabel, attach, hv, hv']

theorem relabel_freeze (e : Equiv.Perm ℕ) (s : State) (t p : ℕ) :
    (freeze s t p).relabel e = freeze (s.relabel e) t (e p) := by
  apply State.ext_data
  · rfl
  · ext v
    simp only [State.relabel, freeze, Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨w, ⟨hwp, hw⟩, rfl⟩
      exact ⟨fun hh => hwp (e.injective hh), ⟨w, hw, rfl⟩⟩
    · rintro ⟨hvp, w, hw, rfl⟩
      exact ⟨w, ⟨fun hh => hvp (congrArg e hh), hw⟩, rfl⟩
  · rfl
  · rfl
  · rfl
  · funext v
    by_cases hv : v = e p
    · subst v
      simp [State.relabel, freeze]
    · have hv' : e.symm v ≠ p := by intro hh; exact hv (by simpa using congrArg e hh)
      simp [State.relabel, freeze, hv, hv']

/-- Birth IDs are transported; freezing times are time labels, so remain t. -/
theorem relabel_step (e : Equiv.Perm ℕ) (s : State) (t p : ℕ) (sign : Bool)
    (ht : e t = t) :
    (step s t sign p).relabel e = step (s.relabel e) t sign (e p) := by
  have hmem : e p ∈ (s.relabel e).active ↔ p ∈ s.active := by
    simp [State.relabel]
  by_cases hp : p ∈ s.active
  · simp only [step, hp, hmem.mpr hp, ite_true]
    cases sign
    · exact relabel_freeze e s t p
    · simpa only [ht, Bool.true_eq, ite_true] using relabel_attach e s t p
  · have hp' : e p ∉ (s.relabel e).active := fun hh => hp (hmem.mp hh)
    simp only [step, hp, hp', ite_false]

theorem map_transitionLaw_relabel (e : Equiv.Perm ℕ) (s : State) (t : ℕ) (sign : Bool)
    (ht : e t = t) :
    (transitionLaw s t sign).map (State.relabel e) = transitionLaw (s.relabel e) t sign := by
  have hnon : (s.relabel e).active.Nonempty ↔ s.active.Nonempty := Finset.image_nonempty
  by_cases hne : s.active.Nonempty
  · rw [transitionLaw, ite_eq_left hne, transitionLaw, ite_eq_left (hnon.mpr hne),
      Measure.map_map measurable_from_top (measurable_of_countable _)]
    have hu := map_uniformOfFinset_of_injOn s.active e (measurable_of_countable _) e.injective.injOn
    change (Measure.uniformOfFinset s.active).map
      (fun p => (step s t sign p).relabel e) =
      (Measure.uniformOfFinset (s.active.image e)).map (fun p => step (s.relabel e) t sign p)
    rw [← hu, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    congr 1
    funext p
    exact relabel_step e s t p sign ht
  · have hne' : ¬(s.relabel e).active.Nonempty := fun hh => hne (hnon.mp hh)
    simp only [transitionLaw, hne, hne', ite_false, Measure.map_dirac' measurable_from_top]

theorem map_continuationLaw_relabel (x : SignSequence) (a k : ℕ)
    (e : Equiv.Perm ℕ) (s : State) (he : ∀ t : ℕ, a < t → e t = t) :
    (continuationLaw x a k s).map (State.relabel e) =
      continuationLaw x a k (s.relabel e) := by
  induction k generalizing a s with
  | zero => simp [continuationLaw]
  | succ k ih =>
    rw [continuationLaw, Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    calc
      _ = (transitionLaw s (a + 1) (x (a + 1))).bind
          (fun q => continuationLaw x (a + 1) k (q.relabel e)) := by
        congr 1
        funext q
        exact ih (a + 1) q (fun t ht => he t (by omega))
      _ = ((transitionLaw s (a + 1) (x (a + 1))).map (State.relabel e)).bind
          (continuationLaw x (a + 1) k) := by
        rw [Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
      _ = _ := by rw [map_transitionLaw_relabel e s _ _ (he (a + 1) (by omega)), continuationLaw]

end Freezing1.Forward
