module

public import Freezing1.ForwardForestReconstruction
public import Freezing1.ForwardForestStarConvention

/-! Bare source forests reconstruct geometry, although they erase root clocks. -/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

set_option backward.isDefEq.respectTransparency false

structure TreeGeometry where
  vertices : Finset ℕ
  graph : SimpleGraph ℕ
  parent : ℕ → ℕ
  height : ℕ → ℕ

def State.geometry (s : State) : TreeGeometry :=
  ⟨s.vertices, s.graph, s.parent, s.height⟩

instance : MeasurableSpace TreeGeometry := ⊤
instance : MeasurableSingletonClass TreeGeometry := ⟨fun _ => trivial⟩

theorem geometry_starForest (s : State) (a : ℕ) :
    (starForest s a).geometry = (forestCut s a).geometry := rfl

/-- Matching a bare source forest to its actual earlier tree determines
every geometric field. No freezing clock or upper activity is asserted to
be reconstructible from the source's all-star convention. -/
theorem geometry_eq_of_prefix_starForest {x : SignSequence} {a b : ℕ} {s t : State}
    (hs : HasHistory x b s) (ht : HasHistory x b t)
    (hb : (b : ℕ∞) ≤ extinctionTime x)
    (hprefix : truncateAt s a = truncateAt t a) (hforest : starForest s a = starForest t a) :
    s.geometry = t.geometry := by
  have hss := hs.historyShape hb
  have hts := ht.historyShape hb
  have hverts : s.vertices = t.vertices := by
    ext v
    rw [hss.schedule.vertex_iff, hts.schedule.vertex_iff]
  have hcverts : cutVertices s a = cutVertices t a := congrArg State.vertices hforest
  have hparent : s.parent = t.parent := by
    funext v
    by_cases hva : v ≤ a
    · have hh := congrArg (fun q : State => q.parent v) hprefix
      simpa only [truncateAt, hva, ite_true] using hh
    · by_cases hv : v ∈ s.vertices
      · have hvC := mem_cutVertices_of_birth_after_cut hs hb hv (Nat.lt_of_not_ge hva)
        have hvCt : v ∈ cutVertices t a := hcverts ▸ hvC
        have hh := congrArg (fun q : State => q.parent v) hforest
        simpa only [starForest, forestCut, hvC, hvCt, hva, ite_true, ite_false] using hh
      · have hvt : v ∉ t.vertices := by simpa only [← hverts] using hv
        exact (hs.current.defaults.outside v hv).1.trans (ht.current.defaults.outside v hvt).1.symm
  have hheightOn : ∀ v : ℕ, v ∈ s.vertices → s.height v = t.height v := by
    intro v
    induction v using Nat.strong_induction_on with
    | h v ih =>
      intro hv
      have hvt : v ∈ t.vertices := hverts ▸ hv
      by_cases hv0 : v = 0
      · subst v
        exact hs.current.valid.height_root.trans ht.current.valid.height_root.symm
      · rw [hs.current.valid.height_parent v hv hv0, ht.current.valid.height_parent v hvt hv0,
          ← congrFun hparent v,
          ih _ (hs.current.valid.parent_lt v hv hv0) (hs.current.valid.parent_mem v hv)]
  have hheight : s.height = t.height := by
    funext v
    by_cases hv : v ∈ s.vertices
    · exact hheightOn v hv
    · have hvt : v ∉ t.vertices := by simpa only [← hverts] using hv
      exact (hs.current.defaults.outside v hv).2.1.trans (ht.current.defaults.outside v hvt).2.1.symm
  have hgraph : s.graph = t.graph := by
    ext u v
    rw [hss.graph_iff, hts.graph_iff, hverts, hparent]
  unfold State.geometry
  rw [hverts, hgraph, hparent, hheight]

def CompatibleBareForest (x : SignSequence) (a b : ℕ) (past F : State) : Prop :=
  ∃ t : State, HasHistory x b t ∧ truncateAt t a = past ∧ starForest t a = F

noncomputable def reconstructBareGeometry (x : SignSequence) (a b : ℕ) (past F : State) : TreeGeometry :=
  if h : CompatibleBareForest x a b past F then (Classical.choose h).geometry else past.geometry

theorem reconstructBareGeometry_actual {x : SignSequence} {a b : ℕ} {s : State}
    (hs : HasHistory x b s) (hb : (b : ℕ∞) ≤ extinctionTime x) :
    reconstructBareGeometry x a b (truncateAt s a) (starForest s a) = s.geometry := by
  have hc : CompatibleBareForest x a b (truncateAt s a) (starForest s a) := ⟨s, hs, rfl, rfl⟩
  rw [reconstructBareGeometry, dite_eq_left hc]
  obtain ⟨ht, hp, hf⟩ := Classical.choose_spec hc
  exact geometry_eq_of_prefix_starForest ht hs hb hp hf

end Freezing1.Forward
