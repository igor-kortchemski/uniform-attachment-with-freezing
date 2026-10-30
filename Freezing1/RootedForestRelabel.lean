module

public import Freezing1.RootedForestExtensionality

/-!
# Relabeling finite rooted forests

An equivalence transports every vertex, parent, component root and depth.
The graph is transported by an explicit isomorphism, and root merging commutes
with relabeling. This is structural infrastructure for the active-label fiber
count; no equality of process distributions is assumed.
-/

@[expose] public section

namespace Freezing1.RootedForest

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

def relabel (F : RootedForest V) (e : V ≃ W) : RootedForest W where
  vertices := F.vertices.map e.toEmbedding
  parent w := e (F.parent (e.symm w))
  root w := e (F.root (e.symm w))
  depth w := F.depth (e.symm w)
  parent_mem := by
    intro w hw
    have hv : e.symm w ∈ F.vertices := by simpa using hw
    simpa using F.parent_mem _ hv
  root_mem := by
    intro w hw
    have hv : e.symm w ∈ F.vertices := by simpa using hw
    simpa using F.root_mem _ hv
  root_fixed := by
    intro w hw
    have hv : e.symm w ∈ F.vertices := by simpa using hw
    simpa only [Equiv.symm_apply_apply] using congrArg e (F.root_fixed _ hv)
  parent_root := by
    intro w hw
    have hv : e.symm w ∈ F.vertices := by simpa using hw
    simpa only [Equiv.symm_apply_apply] using congrArg e (F.parent_root _ hv)
  root_parent := by
    intro w hw
    have hv : e.symm w ∈ F.vertices := by simpa using hw
    simpa only [Equiv.symm_apply_apply] using congrArg e (F.root_parent _ hv)
  depth_root := by
    intro w hw
    have hv : e.symm w ∈ F.vertices := by simpa using hw
    simpa only [Equiv.symm_apply_apply] using F.depth_root _ hv
  depth_parent := by
    intro w hw hn
    have hv : e.symm w ∈ F.vertices := by simpa using hw
    have hne : e.symm w ≠ F.root (e.symm w) := by
      intro he
      apply hn
      simpa only [Equiv.apply_symm_apply] using congrArg e he
    simpa only [Equiv.symm_apply_apply] using F.depth_parent _ hv hne

@[simp] theorem relabel_parent (F : RootedForest V) (e : V ≃ W) (v : V) :
    (F.relabel e).parent (e v) = e (F.parent v) := by simp [relabel]

@[simp] theorem relabel_root (F : RootedForest V) (e : V ≃ W) (v : V) :
    (F.relabel e).root (e v) = e (F.root v) := by simp [relabel]

@[simp] theorem relabel_depth (F : RootedForest V) (e : V ≃ W) (v : V) :
    (F.relabel e).depth (e v) = F.depth v := by simp [relabel]

@[simp] theorem relabel_mem_vertices (F : RootedForest V) (e : V ≃ W) (v : V) :
    e v ∈ (F.relabel e).vertices ↔ v ∈ F.vertices := by simp [relabel]

theorem relabel_roots (F : RootedForest V) (e : V ≃ W) :
    (F.relabel e).roots = F.roots.map e.toEmbedding := by
  ext w
  obtain ⟨v, rfl⟩ := e.surjective w
  simp [mem_roots, relabel]

@[simp] theorem relabel_graph_adj (F : RootedForest V) (e : V ≃ W) (u v : V) :
    (F.relabel e).graph.Adj (e u) (e v) ↔ F.graph.Adj u v := by
  simp [graph, relabel]

/-- The whole ambient graph, including unused isolated vertices, is preserved. -/
def relabelGraphIso (F : RootedForest V) (e : V ≃ W) : F.graph ≃g (F.relabel e).graph where
  toEquiv := e
  map_rel_iff' := by intro u v; exact F.relabel_graph_adj e u v

theorem relabel_isolated (s : Finset V) (e : V ≃ W) :
    (isolated s).relabel e = isolated (s.map e.toEmbedding) := by
  apply ext_data
  · rfl
  · funext w; simp [relabel, isolated]
  · funext w; simp [relabel, isolated]
  · rfl

theorem relabel_join (F : RootedForest V) (e : V ≃ W) {a b : V}
    (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b) :
    (F.join a b ha hb hab).relabel e =
      (F.relabel e).join (e a) (e b)
        (by rw [relabel_roots]; simpa using ha)
        (by rw [relabel_roots]; simpa using hb) (e.injective.ne hab) := by
  apply ext_data
  · rfl
  · funext w
    obtain ⟨v, rfl⟩ := e.surjective w
    by_cases h : v = b <;> simp [relabel, join, h]
  · funext w
    obtain ⟨v, rfl⟩ := e.surjective w
    by_cases h : F.root v = b <;> simp [relabel, join, h]
  · funext w
    obtain ⟨v, rfl⟩ := e.surjective w
    simp [relabel, join]

theorem relabel_adjoin (F : RootedForest V) (e : V ≃ W) {v : V} (hv : v ∉ F.vertices) :
    (F.adjoin v hv).relabel e =
      (F.relabel e).adjoin (e v) (by simpa using hv) := by
  apply ext_data
  · simp [relabel, adjoin]
  · funext w
    obtain ⟨u, rfl⟩ := e.surjective w
    by_cases h : u = v <;> simp [relabel, adjoin, h]
  · funext w
    obtain ⟨u, rfl⟩ := e.surjective w
    by_cases h : u = v <;> simp [relabel, adjoin, h]
  · funext w
    obtain ⟨u, rfl⟩ := e.surjective w
    simp [relabel, adjoin]

end Freezing1.RootedForest
