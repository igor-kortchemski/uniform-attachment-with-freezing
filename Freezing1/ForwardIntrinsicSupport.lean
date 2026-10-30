module

public import Freezing1.ForwardSupportCharacterization

/-!
# Schedule-free increasing labelled trees and the union of forward supports

A labelled forward tree has vertices named by their attachment times (the edge
labels) and frozen vertices carrying their freezing times (the vertex labels).
The schedule-free conditions below are the paper's intrinsic increasing
conditions: the labels $1,\dots,N$ are used exactly once, as an edge label
(a non-root vertex) or as a vertex label (a freezing time), and they increase
along root paths and over adjacent edges. Every such labelled tree arises from
some schedule with a legal history, hence has positive forward probability for
that schedule; conversely every schedule-compatible support point is of this
form. The printed fixed-schedule support claim is separately false.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped Classical ENNReal

/-- The intrinsic increasing conditions on a labelled forward tree, without a schedule. -/
structure IncreasingLabelled (N : ℕ) (s : State) : Prop where
  root_mem : 0 ∈ s.vertices
  defaults : CanonicalDefaults s
  parent_mem : ∀ v ∈ s.vertices, s.parent v ∈ s.vertices
  parent_lt : ∀ v ∈ s.vertices, v ≠ 0 → s.parent v < v
  height_root : s.height 0 = 0
  height_parent : ∀ v ∈ s.vertices, v ≠ 0 → s.height v = s.height (s.parent v) + 1
  active_iff : ∀ v, v ∈ s.active ↔ v ∈ s.vertices ∧ s.frozenAt v = none
  graph_iff : ∀ u v, s.graph.Adj u v ↔ u ∈ s.vertices ∧ v ∈ s.vertices ∧
    ((u ≠ 0 ∧ s.parent u = v) ∨ (v ≠ 0 ∧ s.parent v = u))
  frozen_injective : ∀ u ∈ s.vertices, ∀ v ∈ s.vertices, ∀ t,
    s.frozenAt u = some t → s.frozenAt v = some t → u = v
  frozen_after_birth : ∀ v ∈ s.vertices, ∀ t, s.frozenAt v = some t → v < t
  parent_frozen_after_child : ∀ v ∈ s.vertices, v ≠ 0 →
    ∀ t, s.frozenAt (s.parent v) = some t → v < t
  vertex_le : ∀ v ∈ s.vertices, v ≤ N
  frozen_le : ∀ v ∈ s.vertices, ∀ t, s.frozenAt v = some t → t ≤ N
  label_disjoint : ∀ v ∈ s.vertices, v ≠ 0 → ∀ w ∈ s.vertices, s.frozenAt w ≠ some v
  label_cover : ∀ t, 1 ≤ t → t ≤ N → t ∈ s.vertices ∨ ∃ w ∈ s.vertices, s.frozenAt w = some t

/-- Every schedule-compatible support point satisfies the intrinsic conditions. -/
theorem HistoryShape.increasingLabelled {x : SignSequence} {N : ℕ} {s : State}
    (h : HistoryShape x N s) : IncreasingLabelled N s where
  root_mem := (h.schedule.vertex_iff 0).mpr (Or.inl rfl)
  defaults := h.defaults
  parent_mem := h.parent_mem
  parent_lt := h.parent_lt
  height_root := h.height_root
  height_parent := h.height_parent
  active_iff := h.active_iff
  graph_iff := h.graph_iff
  frozen_injective := h.frozen_injective
  frozen_after_birth := h.frozen_after_birth
  parent_frozen_after_child := h.parent_frozen_after_child
  vertex_le := by
    intro v hv
    rcases (h.schedule.vertex_iff v).mp hv with rfl | ⟨_, hle, _⟩
    · exact Nat.zero_le _
    · exact hle
  frozen_le := fun v hv t ht => (h.schedule.frozen_label v hv t ht).2.1
  label_disjoint := by
    intro v hv hv0 w hw hf
    have h1 := (h.schedule.frozen_label w hw v hf).2.2
    rcases (h.schedule.vertex_iff v).mp hv with rfl | ⟨_, _, hx⟩
    · exact hv0 rfl
    · rw [hx] at h1
      exact absurd h1 (by simp)
  label_cover := by
    intro t ht1 htN
    cases hx : x t
    · right
      exact h.schedule.frozen_exists t ht1 htN hx
    · left
      exact (h.schedule.vertex_iff t).mpr (Or.inr ⟨ht1, htN, hx⟩)

/-- The schedule recording which labels are edge labels. -/
noncomputable def scheduleOf (s : State) : SignSequence := fun t => decide (t ∈ s.vertices)

theorem IncreasingLabelled.historyShape {N : ℕ} {s : State} (h : IncreasingLabelled N s) :
    HistoryShape (scheduleOf s) N s where
  schedule := by
    refine ⟨?_, ?_, ?_⟩
    · intro v
      constructor
      · intro hv
        by_cases hv0 : v = 0
        · exact Or.inl hv0
        · exact Or.inr ⟨Nat.pos_of_ne_zero hv0, h.vertex_le v hv, by simp [scheduleOf, hv]⟩
      · rintro (rfl | ⟨_, _, hx⟩)
        · exact h.root_mem
        · simpa [scheduleOf] using hx
    · intro v hv t ht
      have hbirth := h.frozen_after_birth v hv t ht
      refine ⟨by omega, h.frozen_le v hv t ht, ?_⟩
      simp only [scheduleOf, decide_eq_false_iff_not]
      intro htv
      by_cases ht0 : t = 0
      · omega
      · exact h.label_disjoint t htv ht0 v hv ht
    · intro t ht1 htN hx
      have hnot : t ∉ s.vertices := by simpa [scheduleOf] using hx
      rcases h.label_cover t ht1 htN with hv | hf
      · exact absurd hv hnot
      · exact hf
  defaults := h.defaults
  parent_mem := h.parent_mem
  parent_lt := h.parent_lt
  height_root := h.height_root
  height_parent := h.height_parent
  active_iff := h.active_iff
  graph_iff := h.graph_iff
  frozen_injective := h.frozen_injective
  frozen_after_birth := h.frozen_after_birth
  parent_frozen_after_child := h.parent_frozen_after_child

/-- Along the legal history, every time before `N` has an active vertex, so the schedule has not
reached its extinction time. -/
theorem HistoryShape.le_extinctionTime {x : SignSequence} {N : ℕ} {s : State}
    (h : HistoryShape x N s) : (N : ℕ∞) ≤ extinctionTime x := by
  obtain ⟨F, hFN, hF0, hdata, hsteps⟩ := h.hasHistory
  cases N with
  | zero => simp
  | succ M =>
    have hpos : PositiveThrough x M := by
      intro k hk
      obtain ⟨v, hv, _⟩ := hsteps k (by omega)
      have hcard : 0 < (F k).active.card := Finset.card_pos.mpr ⟨v, hv⟩
      have hc := (hdata k (by omega)).count
      omega
    have h1 : (M : ℕ∞) < extinctionTime x := (lt_extinctionTime_iff x M).mpr hpos
    rw [Nat.cast_succ]
    exact Order.add_one_le_of_lt h1

/-- Every schedule-free increasing labelled tree comes from a schedule not yet extinct at `N`. -/
theorem IncreasingLabelled.exists_schedule {N : ℕ} {s : State} (h : IncreasingLabelled N s) :
    ∃ x : SignSequence, (N : ℕ∞) ≤ extinctionTime x ∧ HistoryShape x N s :=
  ⟨scheduleOf s, h.historyShape.le_extinctionTime, h.historyShape⟩

/-- The union over all schedules of the forward supports is exactly the intrinsic class:
the tree has positive probability for some schedule, and equals the forward product mass. -/
theorem increasingLabelled_iff_exists_support {N : ℕ} {s : State} :
    IncreasingLabelled N s ↔
      ∃ x : SignSequence, (N : ℕ∞) ≤ extinctionTime x ∧ (treeLaw x N) {s} ≠ 0 := by
  constructor
  · intro h
    obtain ⟨x, hn, hs⟩ := h.exists_schedule
    exact ⟨x, hn, (treeLaw_singleton_ne_zero_iff_historyShape x N hn s).mpr hs⟩
  · rintro ⟨x, hn, hne⟩
    exact ((treeLaw_singleton_ne_zero_iff_historyShape x N hn s).mp hne).increasingLabelled

theorem IncreasingLabelled.exists_mass {N : ℕ} {s : State} (h : IncreasingLabelled N s) :
    ∃ x : SignSequence, (N : ℕ∞) ≤ extinctionTime x ∧
      (treeLaw x N).real {s} = forwardHistoryWeight x N := by
  obtain ⟨x, hn, hs⟩ := h.exists_schedule
  exact ⟨x, hn, treeLaw_real_singleton_of_historyShape x N hn hs⟩

end Freezing1.Forward
