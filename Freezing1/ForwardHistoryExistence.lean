module

public import Freezing1.ForwardHistorySupport
public import Freezing1.ForwardScheduleSupport

/-!
# Reconstructing a forward history from increasing terminal data

The assumptions below describe explicit finite labelled tree data: birth IDs,
parent edges, heights, freezing labels and their order. They contain no
probabilistic conclusion or unproved estimate. Truncation at each birth time
reconstructs the legal forward choices.
-/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

structure HistoryShape (x : SignSequence) (n : ℕ) (s : State) : Prop where
  schedule : ScheduleSupport x n s
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

noncomputable def truncateAt (s : State) (k : ℕ) : State where
  vertices := s.vertices.filter (· ≤ k)
  active := s.vertices.filter fun v => v ≤ k ∧ ∀ t, s.frozenAt v = some t → k < t
  graph :=
    { Adj := fun u v => s.graph.Adj u v ∧ u ≤ k ∧ v ≤ k
      symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun _ h => s.graph.irrefl h.1⟩ }
  parent v := if v ≤ k then s.parent v else 0
  height v := if v ≤ k then s.height v else 0
  frozenAt v := match s.frozenAt v with
    | none => none
    | some t => if v ≤ k ∧ t ≤ k then some t else none

theorem HistoryShape.prefix_zero {x : SignSequence} {n : ℕ} {s : State}
    (h : HistoryShape x n s) : truncateAt s 0 = initial := by
  have hroot : 0 ∈ s.vertices := (h.schedule.vertex_iff 0).mpr (Or.inl rfl)
  apply State.ext_data
  · ext v
    simp only [truncateAt, initial, Finset.mem_filter, Finset.mem_singleton, Nat.le_zero]
    exact ⟨And.right, fun he => ⟨he ▸ hroot, he⟩⟩
  · ext v
    simp only [truncateAt, Finset.mem_filter, Nat.le_zero, initial, Finset.mem_singleton]
    constructor
    · exact fun hv => hv.2.1
    · intro hv
      subst v
      exact ⟨hroot, rfl, fun t ht => h.frozen_after_birth 0 hroot t ht⟩
  · ext u v
    change (s.graph.Adj u v ∧ u ≤ 0 ∧ v ≤ 0) ↔ False
    constructor
    · rintro ⟨huv, hu, hv⟩
      have : u = v := by omega
      exact s.graph.irrefl (this ▸ huv)
    · simp
  · funext v
    by_cases hv : v = 0
    · subst v; simpa [truncateAt, initial] using h.defaults.parent_zero
    · simp [truncateAt, initial, hv]
  · funext v
    by_cases hv : v = 0
    · subst v; simpa [truncateAt, initial] using h.height_root
    · simp [truncateAt, initial, hv]
  · funext v
    by_cases hv : v = 0
    · subst v
      cases he : s.frozenAt 0 with
      | none => simp [truncateAt, initial, he]
      | some t =>
        have ht := h.frozen_after_birth 0 hroot t he
        simp [truncateAt, initial, he, show t ≠ 0 by omega]
    · cases he : s.frozenAt v <;> simp [truncateAt, initial, hv, he]

theorem HistoryShape.vertices_le {x : SignSequence} {n : ℕ} {s : State}
    (h : HistoryShape x n s) {v : ℕ} (hv : v ∈ s.vertices) : v ≤ n := by
  rcases (h.schedule.vertex_iff v).mp hv with rfl | hv
  · omega
  · exact hv.2.1

theorem HistoryShape.prefix_self {x : SignSequence} {n : ℕ} {s : State}
    (h : HistoryShape x n s) : truncateAt s n = s := by
  apply State.ext_data
  · ext v
    simp only [truncateAt, Finset.mem_filter]
    exact ⟨And.left, fun hv => ⟨hv, h.vertices_le hv⟩⟩
  · ext v
    rw [h.active_iff]
    simp only [truncateAt, Finset.mem_filter]
    constructor
    · rintro ⟨hv, hle, ht⟩
      refine ⟨hv, ?_⟩
      cases he : s.frozenAt v with
      | none => rfl
      | some t =>
        have := (h.schedule.frozen_label v hv t he).2.1
        have := ht t he
        omega
    · rintro ⟨hv, he⟩
      exact ⟨hv, h.vertices_le hv, by simp [he]⟩
  · ext u v
    change (s.graph.Adj u v ∧ u ≤ n ∧ v ≤ n) ↔ s.graph.Adj u v
    exact ⟨And.left, fun hadj => ⟨hadj, h.vertices_le ((h.graph_iff u v).mp hadj).1,
      h.vertices_le ((h.graph_iff u v).mp hadj).2.1⟩⟩
  · funext v
    by_cases hv : v ≤ n
    · simp [truncateAt, hv]
    · have hn : v ∉ s.vertices := fun hm => hv (h.vertices_le hm)
      simp [truncateAt, hv, (h.defaults.outside v hn).1]
  · funext v
    by_cases hv : v ≤ n
    · simp [truncateAt, hv]
    · have hn : v ∉ s.vertices := fun hm => hv (h.vertices_le hm)
      simp [truncateAt, hv, (h.defaults.outside v hn).2.1]
  · funext v
    cases he : s.frozenAt v with
    | none => simp [truncateAt, he]
    | some t =>
      have hv : v ∈ s.vertices := by
        by_contra hn
        rw [(h.defaults.outside v hn).2.2] at he
        contradiction
      simp [truncateAt, he, h.vertices_le hv, (h.schedule.frozen_label v hv t he).2.1]

/-- A new positive-step vertex has an existing parent which has not frozen yet. -/
theorem HistoryShape.parent_active_prefix {x : SignSequence} {n k : ℕ} {s : State}
    (h : HistoryShape x n s) (hk : k < n) (hx : x (k + 1) = true) :
    s.parent (k + 1) ∈ (truncateAt s k).active := by
  have hv : k + 1 ∈ s.vertices :=
    (h.schedule.vertex_iff _).mpr (Or.inr ⟨by omega, by omega, hx⟩)
  have hp := h.parent_lt _ hv (by omega)
  exact Finset.mem_filter.mpr ⟨h.parent_mem _ hv, by omega,
    fun t ht => lt_trans (by omega) (h.parent_frozen_after_child _ hv (by omega) t ht)⟩

theorem HistoryShape.prefix_attach {x : SignSequence} {n k : ℕ} {s : State}
    (h : HistoryShape x n s) (hk : k < n) (hx : x (k + 1) = true) :
    truncateAt s (k + 1) = attach (truncateAt s k) (k + 1) (s.parent (k + 1)) := by
  have hnew : k + 1 ∈ s.vertices :=
    (h.schedule.vertex_iff _).mpr (Or.inr ⟨by omega, by omega, hx⟩)
  have hp := h.parent_lt _ hnew (by omega)
  have hpm := h.parent_mem _ hnew
  have hnofreeze : ∀ v ∈ s.vertices, s.frozenAt v ≠ some (k + 1) := by
    intro v hv ht
    have := (h.schedule.frozen_label v hv (k + 1) ht).2.2
    rw [hx] at this
    contradiction
  apply State.ext_data
  · ext v
    simp only [truncateAt, attach, Finset.mem_insert, Finset.mem_filter]
    constructor
    · rintro ⟨hv, hle⟩
      by_cases he : v = k + 1
      · exact Or.inl he
      · exact Or.inr ⟨hv, by omega⟩
    · rintro (rfl | ⟨hv, hle⟩)
      · exact ⟨hnew, le_rfl⟩
      · exact ⟨hv, by omega⟩
  · ext v
    simp only [truncateAt, attach, Finset.mem_insert, Finset.mem_filter]
    constructor
    · rintro ⟨hv, hle, ht⟩
      by_cases he : v = k + 1
      · exact Or.inl he
      · exact Or.inr ⟨hv, by omega, fun t hft => lt_trans (by omega) (ht t hft)⟩
    · rintro (rfl | ⟨hv, hle, ht⟩)
      · exact ⟨hnew, le_rfl, fun t hft => h.frozen_after_birth _ hnew t hft⟩
      · refine ⟨hv, by omega, fun t hft => ?_⟩
        have := ht t hft
        have : t ≠ k + 1 := fun he => hnofreeze v hv (he ▸ hft)
        omega
  · ext u v
    change (s.graph.Adj u v ∧ u ≤ k + 1 ∧ v ≤ k + 1) ↔
      (s.graph.Adj u v ∧ u ≤ k ∧ v ≤ k) ∨
        (SimpleGraph.edge (s.parent (k + 1)) (k + 1)).Adj u v
    rw [SimpleGraph.edge_adj]
    have hpne : s.parent (k + 1) ≠ k + 1 := by omega
    constructor
    · rintro ⟨hadj, hu, hv⟩
      obtain ⟨hum, hvm, hpar⟩ := (h.graph_iff u v).mp hadj
      by_cases hue : u = k + 1
      · subst u
        rcases hpar with ⟨_, hpar⟩ | ⟨hv0, hpar⟩
        · exact Or.inr ⟨Or.inr ⟨rfl, hpar.symm⟩, by omega⟩
        · have := h.parent_lt v hvm hv0
          omega
      · by_cases hve : v = k + 1
        · subst v
          rcases hpar with ⟨hu0, hpar⟩ | ⟨_, hpar⟩
          · have := h.parent_lt u hum hu0
            omega
          · exact Or.inr ⟨Or.inl ⟨hpar.symm, rfl⟩, by omega⟩
        · exact Or.inl ⟨hadj, by omega, by omega⟩
    · rintro (⟨hadj, hu, hv⟩ | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩)
      · exact ⟨hadj, by omega, by omega⟩
      · exact ⟨(h.graph_iff _ _).mpr ⟨hpm, hnew, Or.inr ⟨by omega, rfl⟩⟩,
          by omega, le_rfl⟩
      · exact ⟨(h.graph_iff _ _).mpr ⟨hnew, hpm, Or.inl ⟨by omega, rfl⟩⟩,
          le_rfl, by omega⟩
  · funext v
    by_cases he : v = k + 1
    · subst v; simp [truncateAt, attach]
    · have hb : (v ≤ k + 1) = (v ≤ k) := propext (by omega)
      simp [truncateAt, attach, he, hb]
  · funext v
    by_cases he : v = k + 1
    · subst v
      simp [truncateAt, attach, show s.parent (k + 1) ≤ k by omega,
        h.height_parent _ hnew (by omega)]
    · have hb : (v ≤ k + 1) = (v ≤ k) := propext (by omega)
      simp [truncateAt, attach, he, hb]
  · funext v
    by_cases he : v = k + 1
    · subst v
      cases hf : s.frozenAt (k + 1) with
      | none => simp [truncateAt, attach, hf]
      | some t =>
        have := h.frozen_after_birth _ hnew t hf
        simp [truncateAt, attach, hf, show ¬t ≤ k + 1 by omega]
    · have hb : (v ≤ k + 1) = (v ≤ k) := propext (by omega)
      cases hf : s.frozenAt v with
      | none => simp [truncateAt, attach, he, hf]
      | some t =>
        have hv : v ∈ s.vertices := by
          by_contra hn
          rw [(h.defaults.outside v hn).2.2] at hf
          contradiction
        have ht : t ≠ k + 1 := fun ht => hnofreeze v hv (ht ▸ hf)
        have ht' : (t ≤ k + 1) = (t ≤ k) := propext (by omega)
        simp [truncateAt, attach, he, hf, hb, ht']

/-- A freezing label specifies an existing vertex that is still active just before it. -/
theorem HistoryShape.frozen_active_prefix {x : SignSequence} {n k v : ℕ} {s : State}
    (h : HistoryShape x n s) (hv : v ∈ s.vertices) (hf : s.frozenAt v = some (k + 1)) :
    v ∈ (truncateAt s k).active := by
  have hb := h.frozen_after_birth v hv (k + 1) hf
  refine Finset.mem_filter.mpr ⟨hv, by omega, ?_⟩
  intro t ht
  have : t = k + 1 := Option.some.inj (ht.symm.trans hf)
  omega

theorem HistoryShape.prefix_freeze {x : SignSequence} {n k v : ℕ} {s : State}
    (h : HistoryShape x n s) (hx : x (k + 1) = false)
    (hv : v ∈ s.vertices) (hf : s.frozenAt v = some (k + 1)) :
    truncateAt s (k + 1) = freeze (truncateAt s k) (k + 1) v := by
  have hvle := h.frozen_after_birth v hv (k + 1) hf
  have hnew : k + 1 ∉ s.vertices := by
    intro hn
    rcases (h.schedule.vertex_iff _).mp hn with he | ⟨_, _, he⟩
    · omega
    · rw [hx] at he
      contradiction
  have hbound : ∀ u ∈ s.vertices, (u ≤ k + 1 ↔ u ≤ k) := by
    intro u hu
    have : u ≠ k + 1 := fun he => hnew (he ▸ hu)
    omega
  have hverts : (truncateAt s (k + 1)).vertices = (truncateAt s k).vertices := by
    ext u
    simp only [truncateAt, Finset.mem_filter]
    exact and_congr_right (hbound u)
  refine State.ext_data (r := freeze (truncateAt s k) (k + 1) v) hverts ?_ ?_ ?_ ?_ ?_
  · ext u
    simp only [truncateAt, freeze, Finset.mem_erase, Finset.mem_filter]
    constructor
    · rintro ⟨hu, hle, ht⟩
      refine ⟨?_, hu, (hbound u hu).mp hle, fun t hft => lt_trans (by omega) (ht t hft)⟩
      intro he
      subst u
      have := ht (k + 1) hf
      omega
    · rintro ⟨hne, hu, hle, ht⟩
      refine ⟨hu, by omega, ?_⟩
      intro t hft
      have := ht t hft
      have htn : t ≠ k + 1 := by
        intro he
        apply hne
        exact h.frozen_injective u hu v hv (k + 1) (he ▸ hft) hf
      omega
  · ext u w
    change (s.graph.Adj u w ∧ u ≤ k + 1 ∧ w ≤ k + 1) ↔
      (s.graph.Adj u w ∧ u ≤ k ∧ w ≤ k)
    apply and_congr_right
    intro hadj
    obtain ⟨hu, hw, _⟩ := (h.graph_iff u w).mp hadj
    exact and_congr (hbound u hu) (hbound w hw)
  · funext u
    by_cases he : u = k + 1
    · subst u
      simp [truncateAt, freeze, (h.defaults.outside _ hnew).1]
    · have hb : (u ≤ k + 1) = (u ≤ k) := propext (by omega)
      simp [truncateAt, freeze, hb]
  · funext u
    by_cases he : u = k + 1
    · subst u
      simp [truncateAt, freeze, (h.defaults.outside _ hnew).2.1]
    · have hb : (u ≤ k + 1) = (u ≤ k) := propext (by omega)
      simp [truncateAt, freeze, hb]
  · funext u
    by_cases he : u = v
    · subst u
      simp [truncateAt, freeze, hf, show v ≤ k + 1 by omega]
    · cases huft : s.frozenAt u with
      | none => simp [truncateAt, freeze, he, huft]
      | some t =>
        have hu : u ∈ s.vertices := by
          by_contra hn
          rw [(h.defaults.outside u hn).2.2] at huft
          contradiction
        have htn : t ≠ k + 1 := by
          intro ht
          exact he (h.frozen_injective u hu v hv (k + 1) (ht ▸ huft) hf)
        have hb : (u ≤ k + 1) = (u ≤ k) := propext (hbound u hu)
        have ht : (t ≤ k + 1) = (t ≤ k) := propext (by omega)
        simp [truncateAt, freeze, he, huft, hb, ht]

theorem HistoryShape.prefix_legalStep {x : SignSequence} {n k : ℕ} {s : State}
    (h : HistoryShape x n s) (hk : k < n) :
    LegalStep x k (truncateAt s k) (truncateAt s (k + 1)) := by
  cases hx : x (k + 1)
  · obtain ⟨v, hv, hf⟩ := h.schedule.frozen_exists (k + 1) (by omega) (by omega) hx
    have ha := h.frozen_active_prefix hv hf
    refine ⟨v, ha, ?_⟩
    rw [step, ite_eq_left ha, hx]
    exact h.prefix_freeze hx hv hf
  · have ha := h.parent_active_prefix hk hx
    refine ⟨s.parent (k + 1), ha, ?_⟩
    rw [step, ite_eq_left ha, hx]
    exact h.prefix_attach hk hx

/-- Every explicit increasing terminal shape determines an actual legal forward history. -/
theorem HistoryShape.hasHistory {x : SignSequence} {n : ℕ} {s : State}
    (h : HistoryShape x n s) : HasHistory x n s := by
  have hdata : ∀ k ≤ n, PhaseData x k (truncateAt s k) := by
    intro k
    induction k with
    | zero => intro _; rw [h.prefix_zero]; exact initial_phaseData x
    | succ k ih =>
      intro hk
      obtain ⟨v, hv, he⟩ := h.prefix_legalStep (show k < n by omega)
      rw [he]
      exact (ih (by omega)).step hv
  exact ⟨truncateAt s, h.prefix_self, h.prefix_zero, hdata,
    fun k hk => h.prefix_legalStep hk⟩

end Freezing1.Forward
