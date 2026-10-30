module

public import Freezing1.ForwardMaximum
public import Freezing1.ReverseForest
public import Freezing1.SourceChecks

/-!
# A graph-valued counterexample to the printed maximum-height upper bound

The earlier scalar certificate is here combined with the actual one-step tree
law. No simulation or assumed height distribution is used.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory

theorem one_lt_extinctionTime_of_attachment (x : SignSequence) (hx : x 1 = true) :
    (1 : ℕ∞) < extinctionTime x := by
  apply (lt_extinctionTime_iff x 1).mpr
  intro k hk
  have h : k = 0 ∨ k = 1 := by omega
  rcases h with rfl | rfl
  · simp
  · norm_num [activeCount, hx, Finset.sum_range_succ]

theorem forward_treeLaw_one_of_attachment (x : SignSequence) (hx : x 1 = true) :
    Forward.treeLaw x 1 = Measure.dirac (Forward.attach Forward.initial 1 0) := by
  change (Measure.dirac Forward.initial).bind (fun s => Forward.transitionLaw s 1 (x 1)) = _
  rw [Measure.dirac_bind measurable_from_top]
  have h : Forward.initial.active.Nonempty := by simp [Forward.initial]
  have hu : Measure.uniformOfFinset Forward.initial.active = Measure.dirac 0 := by
    simp [Forward.initial, Measure.uniformOfFinset]
  rw [Forward.transitionLaw, ite_eq_left h, hu, Measure.map_dirac' (by fun_prop)]
  simp [Forward.step, Forward.initial, hx]

theorem heightScale_one_of_attachment (x : SignSequence) (hx : x 1 = true) :
    heightScale x 1 = (1 / 2 : ℝ) := by
  change heightScale x (0 + 1) = (1 / 2 : ℝ)
  rw [heightScale_succ]
  norm_num [hx, activeCount_succ]

/-- At the first attachment step, the printed tail event has probability one. -/
theorem forward_printed_height_tail_at_one (x : SignSequence) (hx : x 1 = true) :
    (Forward.treeLaw x 1).real
      {s | (1 / 4 : ℝ) < (Forward.treeHeight s : ℝ) - heightScale x 1} = 1 := by
  rw [forward_treeLaw_one_of_attachment x hx, heightScale_one_of_attachment x hx]
  norm_num [Measure.real, Forward.treeHeight, Forward.attach, Forward.initial]

/-- Proposition `prop:bounds` is false as printed: its proposed upper bound is
strictly smaller than the actual event probability at `n=1`, `t=1/4`. -/
theorem forward_printed_height_upper_bound_counterexample (x : SignSequence) (hx : x 1 = true) :
    Real.exp (-heightScale x 1 * bennettRate ((1 / 4 : ℝ) / heightScale x 1) + Real.log 1) <
      (Forward.treeLaw x 1).real
        {s | (1 / 4 : ℝ) < (Forward.treeHeight s : ℝ) - heightScale x 1} := by
  rw [forward_printed_height_tail_at_one x hx, heightScale_one_of_attachment x hx]
  exact height_upper_bound_rhs_at_one_lt_one

/-- The graph height of a reverse forest, measured from its component roots. -/
def reverseMaximum (F : Reverse.Forest) : ℕ := F.vertices.sup F.depth

theorem isolated_join_reverseMaximum (s : Finset (ℕ ⊕ ℕ)) {a b : ℕ ⊕ ℕ}
    (ha : a ∈ (RootedForest.isolated s).roots)
    (hb : b ∈ (RootedForest.isolated s).roots) (hab : a ≠ b) :
    reverseMaximum ((RootedForest.isolated s).join a b ha hb hab) = 1 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro v hv
    simp only [RootedForest.join_depth, RootedForest.isolated, id_eq, zero_add]
    split_ifs <;> omega
  · have hv := (RootedForest.mem_roots.mp hb).1
    have hle := Finset.le_sup
      (f := ((RootedForest.isolated s).join a b ha hb hab).depth) hv
    simpa [reverseMaximum, RootedForest.join, RootedForest.isolated] using hle

theorem reverse_treeLaw_one_height (x : SignSequence) (hx : x 1 = true) :
    ∀ᵐ F ∂Reverse.treeLaw x 1, reverseMaximum F = 1 := by
  have htwo : 2 ≤ (Reverse.initial x 1).roots.card := by
    rw [(Reverse.initial_valid x 1).roots_card]
    norm_num [activeCount, hx, Finset.sum_range_succ]
  have hlaw : Reverse.treeLaw x 1 = (Reverse.initial x 1).joinLaw := by
    simp [Reverse.treeLaw, Reverse.lawAfter, Reverse.transitionLaw, hx,
      Measure.dirac_bind measurable_from_top]
  rw [hlaw]
  apply RootedForest.joinLaw_ae _ htwo
  intro p hp
  simp only [RootedForest.joinChoice, dite_eq_left hp]
  exact isolated_join_reverseMaximum _ _ _ _

/-- The printed reverse-tree tail event has probability one, independently
of the unproved general equivalence of the forward and reverse constructions. -/
theorem reverse_printed_height_tail_at_one (x : SignSequence) (hx : x 1 = true) :
    (Reverse.treeLaw x 1).real
      {F | (1 / 4 : ℝ) < (reverseMaximum F : ℝ) - heightScale x 1} = 1 := by
  have hprob : (Reverse.treeLaw x 1)
      {F | (1 / 4 : ℝ) < (reverseMaximum F : ℝ) - heightScale x 1} = 1 := by
    apply (ae_iff_prob_eq_one measurable_from_top).mp
    filter_upwards [reverse_treeLaw_one_height x hx] with F hF
    rw [hF, heightScale_one_of_attachment x hx]
    norm_num
  simp only [Measure.real, hprob, ENNReal.toReal_one]

/-- A fully probabilistic counterexample for the reverse tree in `prop:bounds`. -/
theorem printed_height_upper_bound_counterexample (x : SignSequence) (hx : x 1 = true) :
    Real.exp (-heightScale x 1 * bennettRate ((1 / 4 : ℝ) / heightScale x 1) + Real.log 1) <
      (Reverse.treeLaw x 1).real
        {F | (1 / 4 : ℝ) < (reverseMaximum F : ℝ) - heightScale x 1} := by
  rw [reverse_printed_height_tail_at_one x hx, heightScale_one_of_attachment x hx]
  exact height_upper_bound_rhs_at_one_lt_one

/-- There is a schedule satisfying the proposition's survival hypothesis for
which its upper estimate fails. -/
theorem exists_counterexample_printed_height_bound :
    ∃ x : SignSequence, (1 : ℕ∞) < extinctionTime x ∧
      Real.exp (-heightScale x 1 * bennettRate ((1 / 4 : ℝ) / heightScale x 1) + Real.log 1) <
        (Reverse.treeLaw x 1).real
          {F | (1 / 4 : ℝ) < (reverseMaximum F : ℝ) - heightScale x 1} := by
  exact ⟨fun _ => true, one_lt_extinctionTime_of_attachment _ rfl,
    printed_height_upper_bound_counterexample _ rfl⟩

end Freezing1
