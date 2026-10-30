module

public import Freezing1.ForwardForestCutState

/-! The source's all-star activity convention and its loss of root clocks. -/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

noncomputable def starForest (s : State) (a : ℕ) : State :=
  { forestCut s a with
    active := s.active ∪ cutRoots s a
    frozenAt := fun v => if v ∈ cutRoots s a then none else (forestCut s a).frozenAt v }

theorem starForest_root_active (s : State) (a : ℕ) {v : ℕ} (hv : v ∈ cutRoots s a) :
    v ∈ (starForest s a).active := Finset.mem_union.mpr (Or.inr hv)

theorem starForest_root_clock (s : State) (a : ℕ) {v : ℕ} (hv : v ∈ cutRoots s a) :
    (starForest s a).frozenAt v = none := by simp [starForest, hv]

/-- S17: even on a strictly surviving two-step schedule, root marking
erases a true freeze and increases the displayed active count. It cannot
be identified with the full active/frozen terminal state. -/
theorem star_activity_counterexample :
    let x : SignSequence := fun i => decide (i ≠ 2)
    let s := attach initial 1 0
    let t := freeze s 2 0
    PositiveThrough x 2 ∧ LegalStep x 0 initial s ∧ LegalStep x 1 s t ∧
      (starForest t 1).active.card = 2 ∧ t.active.card = 1 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    interval_cases k <;> norm_num [activeCount, Finset.sum_range_succ]
  · refine ⟨0, ?_, ?_⟩
    · simp [initial]
    · simp [step, initial]
  · refine ⟨0, ?_, ?_⟩
    · simp [attach, initial]
    · simp [step, attach, initial]
  · norm_num [starForest, cutRoots, truncateAt, freeze, attach, initial, Finset.filter_insert, Finset.filter_singleton,
      Function.update_apply]
  · norm_num [freeze, attach, initial]

end Freezing1.Forward
