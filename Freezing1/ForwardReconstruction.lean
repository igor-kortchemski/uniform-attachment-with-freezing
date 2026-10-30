module

public import Freezing1.ForwardLabels
public import Freezing1.ForwardStateDefaults

/-!
# Reconstruction of forward histories

Birth IDs and freezing labels identify the last chosen vertex. Removing the
new birth or undoing the latest frozen label recovers the previous state,
including its canonical unused function values. This is the uniqueness
argument required for the corrected forward support probability in L04.
-/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

theorem State.ext_data {s r : State} (hv : s.vertices = r.vertices)
    (ha : s.active = r.active) (hg : s.graph = r.graph)
    (hp : s.parent = r.parent) (hh : s.height = r.height) (hf : s.frozenAt = r.frozenAt) : s = r := by
  cases s
  cases r
  cases hv
  cases ha
  cases hg
  cases hp
  cases hh
  cases hf
  rfl

/-- A legal attachment output identifies both the chosen parent and its
complete predecessor state. -/
theorem attach_predecessor_eq {n : ℕ} {s r : State} (hs : ValidAt n s) (hr : ValidAt n r)
    (hdS : CanonicalDefaults s) (hdR : CanonicalDefaults r)
    {v w : ℕ} (he : attach s (n + 1) v = attach r (n + 1) w) : s = r ∧ v = w := by
  have hnewS : n + 1 ∉ s.vertices := by intro h; have := hs.vertices_le _ h; omega
  have hnewR : n + 1 ∉ r.vertices := by intro h; have := hr.vertices_le _ h; omega
  have hactiveS : n + 1 ∉ s.active := fun h => hnewS (hs.active_subset h)
  have hactiveR : n + 1 ∉ r.active := fun h => hnewR (hr.active_subset h)
  have hvw : v = w := by
    have h := congrArg (fun q : State => q.parent (n + 1)) he
    simpa only [attach, Function.update_self] using h
  have hverts : s.vertices = r.vertices := by
    have h := congrArg (fun q : State => q.vertices.erase (n + 1)) he
    simpa only [attach, Finset.erase_insert hnewS, Finset.erase_insert hnewR] using h
  have hact : s.active = r.active := by
    have h := congrArg (fun q : State => q.active.erase (n + 1)) he
    simpa only [attach, Finset.erase_insert hactiveS, Finset.erase_insert hactiveR] using h
  have hparent : s.parent = r.parent := by
    funext u
    by_cases hu : u = n + 1
    · subst u
      exact (hdS.outside _ hnewS).1.trans (hdR.outside _ hnewR).1.symm
    · have h := congrArg (fun q : State => q.parent u) he
      simpa only [attach, Function.update_of_ne hu] using h
  have hheight : s.height = r.height := by
    funext u
    by_cases hu : u = n + 1
    · subst u
      exact (hdS.outside _ hnewS).2.1.trans (hdR.outside _ hnewR).2.1.symm
    · have h := congrArg (fun q : State => q.height u) he
      simpa only [attach, Function.update_of_ne hu] using h
  have hfrozen : s.frozenAt = r.frozenAt := by
    funext u
    by_cases hu : u = n + 1
    · subst u
      exact (hdS.outside _ hnewS).2.2.trans (hdR.outside _ hnewR).2.2.symm
    · have h := congrArg (fun q : State => q.frozenAt u) he
      simpa only [attach, Function.update_of_ne hu] using h
  have hgraph : s.graph = r.graph := by
    ext a b
    by_cases ha : a = n + 1
    · subst a
      have hs' : ¬ s.graph.Adj (n + 1) b := fun h => hnewS (hs.adj_mem h).1
      have hr' : ¬ r.graph.Adj (n + 1) b := fun h => hnewR (hr.adj_mem h).1
      simp [hs', hr']
    · by_cases hb : b = n + 1
      · subst b
        have hs' : ¬ s.graph.Adj a (n + 1) := fun h => hnewS (hs.adj_mem h).2
        have hr' : ¬ r.graph.Adj a (n + 1) := fun h => hnewR (hr.adj_mem h).2
        simp [hs', hr']
      · have h := congrArg (fun q : State => q.graph.Adj a b) he
        simpa only [attach, SimpleGraph.sup_adj, SimpleGraph.edge_adj, ha, hb,
          and_false, false_and, or_false, false_or] using Iff.of_eq h
  exact ⟨State.ext_data hverts hact hgraph hparent hheight hfrozen, hvw⟩

/-- The new freezing time is larger than all old frozen labels and therefore
identifies its chosen vertex; active status recovers the overwritten value. -/
theorem freeze_predecessor_eq {n : ℕ} {s r : State} (hs : ValidAt n s) (hr : ValidAt n r)
    (hlR : LabelsValidAt n r) {v w : ℕ} (hv : v ∈ s.active) (hw : w ∈ r.active)
    (he : freeze s (n + 1) v = freeze r (n + 1) w) : s = r ∧ v = w := by
  have hverts : s.vertices = r.vertices := by
    simpa only [freeze] using congrArg State.vertices he
  have hvw : v = w := by
    by_contra hne
    have h := congrArg (fun q : State => q.frozenAt v) he
    simp only [freeze, Function.update_self, Function.update_of_ne hne] at h
    have hvR : v ∈ r.vertices := hverts ▸ hs.active_subset hv
    have hbound := (hlR.bounded v hvR (n + 1) h.symm).2
    omega
  have hact : s.active = r.active := by
    have h := congrArg State.active he
    change s.active.erase v = r.active.erase w at h
    rw [← hvw] at h hw
    calc
      s.active = insert v (s.active.erase v) := (Finset.insert_erase hv).symm
      _ = insert v (r.active.erase v) := congrArg (insert v) h
      _ = r.active := Finset.insert_erase hw
  have hfrozen : s.frozenAt = r.frozenAt := by
    funext u
    by_cases hu : u = v
    · subst u
      have hsnone := (hs.active_iff v (hs.active_subset hv)).mp hv
      have hrnone := (hr.active_iff w (hr.active_subset hw)).mp hw
      simpa only [← hvw] using hsnone.trans hrnone.symm
    · have huw : u ≠ w := by simpa only [← hvw] using hu
      have h := congrArg (fun q : State => q.frozenAt u) he
      simpa only [freeze, Function.update_of_ne hu, Function.update_of_ne huw] using h
  have hgraph : s.graph = r.graph := by simpa only [freeze] using congrArg State.graph he
  have hparent : s.parent = r.parent := by simpa only [freeze] using congrArg State.parent he
  have hheight : s.height = r.height := by simpa only [freeze] using congrArg State.height he
  exact ⟨State.ext_data hverts hact hgraph hparent hheight hfrozen, hvw⟩

/-- The last legal forward output uniquely determines predecessor and choice. -/
theorem step_predecessor_eq {n : ℕ} {s r : State} (hs : ValidAt n s) (hr : ValidAt n r)
    (hdS : CanonicalDefaults s) (hdR : CanonicalDefaults r) (hlR : LabelsValidAt n r)
    (sign : Bool) {v w : ℕ} (hv : v ∈ s.active) (hw : w ∈ r.active)
    (he : step s (n + 1) sign v = step r (n + 1) sign w) : s = r ∧ v = w := by
  simp only [step, ite_eq_left hv, ite_eq_left hw] at he
  cases sign with
  | false => exact freeze_predecessor_eq hs hr hlR hv hw he
  | true => exact attach_predecessor_eq hs hr hdS hdR he

/-- Each active choice has a different legal output. -/
theorem step_injective_on {n : ℕ} {s : State} (hs : ValidAt n s)
    (hd : CanonicalDefaults s) (hl : LabelsValidAt n s) (sign : Bool) :
    Set.InjOn (step s (n + 1) sign) (↑s.active : Set ℕ) := by
  intro v hv w hw he
  exact (step_predecessor_eq hs hs hd hd hl sign hv hw he).2

def LegalStep (x : SignSequence) (n : ℕ) (s r : State) : Prop :=
  ∃ v ∈ s.active, r = step s (n + 1) (x (n + 1)) v

theorem legalStep_predecessor_eq {x : SignSequence} {n : ℕ} {s r H : State}
    (hs : ValidAt n s) (hr : ValidAt n r) (hdS : CanonicalDefaults s)
    (hdR : CanonicalDefaults r) (hlR : LabelsValidAt n r)
    (hstepS : LegalStep x n s H) (hstepR : LegalStep x n r H) : s = r := by
  obtain ⟨v, hv, heS⟩ := hstepS
  obtain ⟨w, hw, heR⟩ := hstepR
  exact (step_predecessor_eq hs hr hdS hdR hlR _ hv hw (heS.symm.trans heR)).1

end Freezing1.Forward
