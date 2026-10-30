module

public import Freezing1.ForwardForestCutLaw

/-!
# A past tree and its root-labelled complete cut forest reconstruct the future

The uniqueness is proved from the actual terminal parent data, freezing
times and history shape. The later total choice operator has this verified
characterization on every compatible pair; it does not assume a grafting law.
-/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

set_option backward.isDefEq.respectTransparency false

theorem mem_cutVertices_of_birth_after_cut {x : SignSequence} {n : ℕ} {s : State}
    (hs : HasHistory x n s) (hn : (n : ℕ∞) ≤ extinctionTime x)
    {a v : ℕ} (hv : v ∈ s.vertices) (hav : a < v) : v ∈ cutVertices s a := by
  have hshape := hs.historyShape hn
  refine Finset.mem_filter.mpr ⟨hv, ?_⟩
  intro t ht
  exact hav.trans (hshape.frozen_after_birth v hv t ht)

theorem frozenAt_eq_prefix_of_not_mem_cut {x : SignSequence} {n : ℕ} {s : State}
    (hs : HasHistory x n s) (hn : (n : ℕ∞) ≤ extinctionTime x)
    {a v : ℕ} (hv : v ∈ s.vertices) (hvc : v ∉ cutVertices s a) :
    (truncateAt s a).frozenAt v = s.frozenAt v := by
  have hva : v ≤ a := by
    by_contra hh
    exact hvc (mem_cutVertices_of_birth_after_cut hs hn hv (Nat.lt_of_not_ge hh))
  cases hf : s.frozenAt v with
  | none => simp [truncateAt, hf]
  | some t =>
    have hta : t ≤ a := by
      by_contra hh
      have hat : a < t := Nat.lt_of_not_ge hh
      apply hvc
      refine Finset.mem_filter.mpr ⟨hv, ?_⟩
      intro j hj
      have he : t = j := Option.some.inj (hf.symm.trans hj)
      simpa only [← he] using hat
    simp [truncateAt, hf, hva, hta]

/-- The old names are retained in this theorem. Erasing them is precisely
the information loss that later necessitates a random matching. -/
theorem eq_of_prefix_forestCut {x : SignSequence} {a b : ℕ} {s t : State}
    (hs : HasHistory x b s) (ht : HasHistory x b t)
    (hb : (b : ℕ∞) ≤ extinctionTime x)
    (hprefix : truncateAt s a = truncateAt t a) (hforest : forestCut s a = forestCut t a) :
    s = t := by
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
        simpa only [forestCut, hvC, hvCt, hva, ite_true, ite_false] using hh
      · have hvt : v ∉ t.vertices := by simpa only [← hverts] using hv
        exact (hs.current.defaults.outside v hv).1.trans (ht.current.defaults.outside v hvt).1.symm
  have hfrozen : s.frozenAt = t.frozenAt := by
    funext v
    by_cases hv : v ∈ s.vertices
    · have hvt : v ∈ t.vertices := hverts ▸ hv
      by_cases hvC : v ∈ cutVertices s a
      · have hvCt : v ∈ cutVertices t a := hcverts ▸ hvC
        have hh := congrArg (fun q : State => q.frozenAt v) hforest
        simpa only [forestCut, hvC, hvCt, ite_true] using hh
      · have hvCt : v ∉ cutVertices t a := by simpa only [← hcverts] using hvC
        have hh := congrArg (fun q : State => q.frozenAt v) hprefix
        rw [frozenAt_eq_prefix_of_not_mem_cut hs hb hv hvC,
          frozenAt_eq_prefix_of_not_mem_cut ht hb hvt hvCt] at hh
        exact hh
    · have hvt : v ∉ t.vertices := by simpa only [← hverts] using hv
      exact (hs.current.defaults.outside v hv).2.2.trans (ht.current.defaults.outside v hvt).2.2.symm
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
  have hactive : s.active = t.active := by
    ext v
    rw [hss.active_iff, hts.active_iff, hverts, hfrozen]
  exact State.ext_data hverts hactive hgraph hparent hheight hfrozen

def CompatibleForest (x : SignSequence) (a b : ℕ) (past F : State) : Prop :=
  ∃ t : State, HasHistory x b t ∧ truncateAt t a = past ∧ forestCut t a = F

noncomputable def reconstructForest (x : SignSequence) (a b : ℕ) (past F : State) : State :=
  if h : CompatibleForest x a b past F then Classical.choose h else past

theorem reconstructForest_spec {x : SignSequence} {a b : ℕ} {past F : State}
    (h : CompatibleForest x a b past F) :
    HasHistory x b (reconstructForest x a b past F) ∧
      truncateAt (reconstructForest x a b past F) a = past ∧
      forestCut (reconstructForest x a b past F) a = F := by
  rw [reconstructForest, dite_eq_left h]
  exact Classical.choose_spec h

theorem reconstructForest_actual {x : SignSequence} {a b : ℕ} {s : State}
    (hs : HasHistory x b s) (hb : (b : ℕ∞) ≤ extinctionTime x) :
    reconstructForest x a b (truncateAt s a) (forestCut s a) = s := by
  have hc : CompatibleForest x a b (truncateAt s a) (forestCut s a) := ⟨s, hs, rfl, rfl⟩
  have hr := reconstructForest_spec hc
  exact eq_of_prefix_forestCut hr.1 hs hb hr.2.1 hr.2.2

end Freezing1.Forward
