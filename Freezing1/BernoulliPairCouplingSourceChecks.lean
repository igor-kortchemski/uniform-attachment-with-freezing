module

public import Freezing1.ReverseCoalescenceTime
public import Freezing1.ReverseHistoryHeight

/-! The current-merge boundary in the source's auxiliary-coin prose. -/

@[expose] public section

namespace Freezing1.BernoulliPairCoupling

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

/-- With two original roots, choosing the first as the attached child
increases its height and merges it with the second. The source condition
`coal ≤ i−1` still holds: here `i=1` and `coal=0`. This event has probability
one half under the actual reverse transition, rather than being impossible. -/
theorem source_current_merge_boundary :
    let x : SignSequence := fun _ => true
    let H := ReverseHistory.initial x 1
    let u : ℕ ⊕ ℕ := .inl 0
    let v : ℕ ⊕ ℕ := .inl 1
    H.current.root u ≠ H.current.root v ∧
      (Reverse.transitionLaw x 0 H.current).real {F' |
        ReverseHistory.heightIncrement u (ReverseHistory.push H F') = 1 ∧
        ReverseHistory.coalescenceTime 1 (ReverseHistory.push H F') u v ≤ 0 ∧
        F'.root u = F'.root v} = (1 / 2 : ℝ) := by
  dsimp only
  let x : SignSequence := fun _ => true
  let H := ReverseHistory.initial x 1
  let u : ℕ ⊕ ℕ := .inl 0
  let v : ℕ ⊕ ℕ := .inl 1
  have hS : activeCount x 1 = 2 := by simp [activeCount_succ, x]
  have hpos : PositiveThrough x 1 := by
    intro i hi
    have he : i = 0 ∨ i = 1 := by omega
    rcases he with rfl | rfl <;> simp [activeCount_succ, x]
  have hτ : (1 : ℕ∞) ≤ extinctionTime x := ((lt_extinctionTime_iff x 1).mpr hpos).le
  have hvalid : Reverse.ValidAt x 1 (0 + 1) H.current := Reverse.initial_valid x 1
  have hu : u ∈ H.current.vertices := by
    simp [H, ReverseHistory.initial, Reverse.initial, RootedForest.isolated,
      hS, u]
  have hv : v ∈ H.current.vertices := by
    simp [H, ReverseHistory.initial, Reverse.initial, RootedForest.isolated,
      hS, v]
  have hne : H.current.root u ≠ H.current.root v := by
    change u ≠ v
    simp [u,v]
  refine ⟨hne, ?_⟩
  have hcoal : ∀ᵐ F' ∂Reverse.transitionLaw x 0 H.current, F'.root u = F'.root v := by
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    apply (ENNReal.toReal_eq_one_iff _).mp
    change (Reverse.transitionLaw x 0 H.current).real {F' | F'.root u = F'.root v} = 1
    rw [Reverse.transitionLaw_coalescence hvalid hu hv hne]
    norm_num [x, hS]
  have htime (F' : Reverse.Forest) : ReverseHistory.coalescenceTime 1 (ReverseHistory.push H F') u v = 0 := by
    have hnot : ¬ReverseHistory.Coalesced (ReverseHistory.push H F') u v 1 := by
      intro hc
      exact hne hc.2.2
    simp only [ReverseHistory.coalescenceTime, Nat.findGreatest_succ, hnot, ite_false, Nat.findGreatest_zero]
  have hD := ReverseHistory.forest_heightIncrement_hasLaw hτ (by omega : 0 < 1) hvalid hu
  have hprob := hD.measureReal_eq (p := fun j => j = 1) (by trivial)
  have hp : (Reverse.attachmentParameter x 1 hτ ⟨0, by omega⟩ : ℝ) = 1 / 2 := by
    rw [Reverse.attachmentParameter_coe]
    norm_num [x,hS]
  have hy : (Reverse.transitionLaw x 0 H.current).real
      {F' | F'.depth u - H.current.depth u = 1} = (1 / 2 : ℝ) := by
    rw [bernoulliMeasure_real_apply_of_mem_of_notMem (x := (1 : ℕ)) (y := 0)
      (s := {j : ℕ | j = 1}) _ (by trivial) (by rfl) (by decide), hp] at hprob
    exact hprob
  calc
    _ = (Reverse.transitionLaw x 0 H.current).real {F' | F'.depth u - H.current.depth u = 1} := by
      apply congrArg ENNReal.toReal
      apply measure_congr
      filter_upwards [hcoal] with F' hc
      change ((F'.depth u - H.current.depth u = 1 ∧
        ReverseHistory.coalescenceTime 1 (ReverseHistory.push H F') u v ≤ 0 ∧
        F'.root u = F'.root v) : Prop) = (F'.depth u - H.current.depth u = 1)
      simp only [htime F', Nat.le_refl, hc, and_true]
    _ = _ := hy

end Freezing1.BernoulliPairCoupling
