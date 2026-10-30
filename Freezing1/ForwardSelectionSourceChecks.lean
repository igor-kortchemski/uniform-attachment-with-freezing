module

public import Freezing1.ForwardVertexDegree
public import Freezing1.ForwardLifetimeLimit

/-!
# Explicit checks of the source's forward selection indices

For the schedule `(+,-,+,+,...)`, the true root-survival probability after
the only freezing step is one half, whereas the printed post-step product
is zero. A newborn's degree is one deterministically; a birth step is not a
uniform selection of that newborn. These are defects in the printed proof,
not assumptions of the corrected degree/freezing result.
-/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory
open scoped Topology ENNReal BigOperators Classical

set_option backward.isDefEq.respectTransparency false

def selectionIndexSchedule (i : ℕ) : Bool := decide (i ≠ 2)

theorem selectionIndexSchedule_count (n : ℕ) :
    activeCount selectionIndexSchedule n = if n < 2 then (n : ℤ) + 1 else (n : ℤ) - 1 := by
  induction n with
  | zero => simp [activeCount]
  | succ n ih =>
    rw [activeCount_succ, ih]
    by_cases hn : n < 2
    · interval_cases n <;> norm_num [selectionIndexSchedule]
    · have hne : n + 1 ≠ 2 := by omega
      have hn' : ¬n + 1 < 2 := by omega
      simp [selectionIndexSchedule, hne, hn, hn']

theorem selectionIndexSchedule_nonextinct : extinctionTime selectionIndexSchedule = ⊤ := by
  apply (extinctionTime_eq_top_iff _).mpr
  intro n
  rw [selectionIndexSchedule_count]
  split_ifs <;> omega

theorem selectionIndexSchedule_root_survival_two :
    (treeLaw selectionIndexSchedule 2).real {s | 0 ∈ s.active} = 1 / 2 := by
  rw [treeLaw_vertex_survival selectionIndexSchedule 0 2
    (by simp [selectionIndexSchedule_nonextinct]) (r := 0) le_rfl]
  rw [show Finset.Ioc 0 2 = ({1, 2} : Finset ℕ) by decide]
  norm_num [treeLaw, initial, vertexSurvivalFactor, selectionIndexSchedule,
    activeCount, Finset.sum_range_succ]

theorem selectionIndexSchedule_printed_survival_two :
    (∏ i ∈ Finset.Ioc 0 2,
      (if selectionIndexSchedule i then (1 : ℝ) else 1 - 1 / activeCount selectionIndexSchedule i)) = 0 := by
  rw [show Finset.Ioc 0 2 = ({1, 2} : Finset ℕ) by decide]
  norm_num [selectionIndexSchedule, activeCount, Finset.sum_range_succ]

theorem selectionIndexSchedule_refutes_printed_product :
    (treeLaw selectionIndexSchedule 2).real {s | 0 ∈ s.active} ≠
      ∏ i ∈ Finset.Ioc 0 2,
        (if selectionIndexSchedule i then (1 : ℝ) else 1 - 1 / activeCount selectionIndexSchedule i) := by
  rw [selectionIndexSchedule_root_survival_two, selectionIndexSchedule_printed_survival_two]
  norm_num

theorem selectionIndexSchedule_root_survival_after_two (k : ℕ) :
    (treeLaw selectionIndexSchedule (2 + k)).real {s | 0 ∈ s.active} = 1 / 2 := by
  rw [treeLaw_vertex_survival selectionIndexSchedule 2 k
    (by simp [selectionIndexSchedule_nonextinct]) (r := 0) (by omega),
    selectionIndexSchedule_root_survival_two]
  have hp : (∏ i ∈ Finset.Ioc 2 (2 + k), vertexSurvivalFactor selectionIndexSchedule i) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hne : i ≠ 2 := by have := Finset.mem_Ioc.mp hi; omega
    simp [vertexSurvivalFactor, selectionIndexSchedule, hne]
  rw [hp, mul_one]

theorem selectionIndexSchedule_actual_never_frozen_probability :
    (ForwardInfiniteHistory.fullLaw selectionIndexSchedule).real
      (ForwardInfiniteHistory.survivesForever 0 0) = 1 / 2 := by
  open ForwardInfiniteHistory in
  have hlim := treeLaw_survival_limit_real selectionIndexSchedule 2 (r := 0) (by omega)
  have he : (fun k => (treeLaw selectionIndexSchedule (2 + k)).real
      {s | 0 ∈ s.active}) = fun _ : ℕ => (1 : ℝ) / 2 := by
    funext k
    exact selectionIndexSchedule_root_survival_after_two k
  rw [he] at hlim
  have hp : (ForwardInfiniteHistory.fullLaw selectionIndexSchedule).real
      (ForwardInfiniteHistory.survivesForever 0 2) = 1 / 2 :=
    tendsto_nhds_unique hlim tendsto_const_nhds
  rw [← hp]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [ForwardInfiniteHistory.fullLaw_legalOrHeld selectionIndexSchedule] with H hl
  apply propext
  change (∀ k, 0 ∈ (H (0 + k)).active) ↔ ∀ k, 0 ∈ (H (2 + k)).active
  constructor
  · intro h k
    simpa only [Nat.zero_add] using h (2 + k)
  · intro h k
    simp only [Nat.zero_add]
    by_cases hk : 2 ≤ k
    · have hh := h (k - 2)
      simpa only [Nat.add_sub_of_le hk] using hh
    · have hh := h 0
      simp only [Nat.add_zero] at hh
      exact ForwardInfiniteHistory.active_old_antitone hl (Nat.zero_le k) (by omega) hh

theorem vertexNeighbors_attach_new {n : ℕ} {s : State} (hs : ValidAt n s)
    {p : ℕ} (hp : p ∈ s.active) :
    vertexNeighbors (attach s (n + 1) p) (n + 1) = {p} := by
  have hpv := hs.active_subset hp
  have hpn : p ≠ n + 1 := by have := hs.vertices_le p hpv; omega
  have hnot : ∀ v, ¬s.graph.Adj (n + 1) v := by
    intro v ha
    have := hs.vertices_le (n + 1) (hs.adj_mem ha).1
    omega
  ext v
  simp only [vertexNeighbors, attach, Finset.mem_filter, Finset.mem_insert,
    SimpleGraph.sup_adj, SimpleGraph.edge_adj, hnot, false_or, Finset.mem_singleton]
  by_cases he : v = p
  · subst v
    simp [hpv, Ne.symm hpn]
  · simp [he, Ne.symm hpn]

theorem vertexDegree_attach_new {n : ℕ} {s : State} (hs : ValidAt n s)
    {p : ℕ} (hp : p ∈ s.active) : vertexDegree (attach s (n + 1) p) (n + 1) = 1 := by
  rw [vertexDegree, vertexNeighbors_attach_new hs hp, Finset.card_singleton]

theorem vertexDegree_before_birth {n : ℕ} {s : State} (hs : ValidAt n s) :
    vertexDegree s (n + 1) = 0 := by
  have he : vertexNeighbors s (n + 1) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have := hs.vertices_le (n + 1) (hs.adj_mem (Finset.mem_filter.mp hv).2).1
    omega
  simp only [vertexDegree, he, Finset.card_empty]

/-- At its own birth the actual new degree increases deterministically,
even when the pre-step population is two. Uniform selection probabilities
therefore apply strictly after birth, not to the birth event itself. -/
theorem birth_step_not_selection_of_newborn :
    ∀ p ∈ (attach initial 1 0).active,
      vertexDegree (attach (attach initial 1 0) 2 p) 2 =
        vertexDegree (attach initial 1 0) 2 + 1 ∧
      (1 : ℝ) ≠ 1 / ((attach initial 1 0).active.card : ℝ) := by
  intro p hp
  have hs : ValidAt 1 (attach initial 1 0) :=
    initial_valid.attach (by simp [initial])
  rw [vertexDegree_attach_new hs hp, vertexDegree_before_birth hs]
  norm_num [attach, initial]

end Freezing1.Forward
