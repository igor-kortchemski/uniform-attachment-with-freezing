module

public import Freezing1.ReversePairHeightTails
public import Freezing1.ReverseHistoryContinuation
public import Freezing1.ReverseHistoryBlockCount

/-!
# Joint block-height control on the actual complete history

The Markov decomposition is an equality of the genuine history laws. Root
membership at the top of the block is retained as a random past event, so the
result applies to the random set of component roots used in the second moment.
-/

@[expose] public section

namespace Freezing1.ReverseHistory

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

theorem map_blockHistoryLaw_current (x : SignSequence) (a k : ℕ) (H : History) :
    (blockHistoryLaw x a k H).map History.current = Reverse.blockLaw x a k H.current := by
  induction k generalizing H with
  | zero => exact Measure.map_dirac' measurable_from_top H
  | succ k ih =>
    rw [blockHistoryLaw,
      Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    simp_rw [ih]
    rw [transitionLaw, Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    rfl

theorem blockHistoryLaw_top_stage (x : SignSequence) (a k : ℕ) (H : History) :
    ∀ᵐ H' ∂blockHistoryLaw x a k H, stage H' k = H.current := by
  apply ae_of_ae_map (f := fun H' => stage H' k)
    (p := fun F : Reverse.Forest => F = H.current) measurable_from_top.aemeasurable
  have he := map_blockHistoryLaw_stage x a k H 0
  simp only [Nat.add_zero, stage_zero] at he
  rw [he]
  simp

/-- The conditional pair bound retains the actual random roots of the
starting history. It does not condition on their subsequent noncoalescence. -/
theorem blockHistoryLaw_root_pair_tail_le {x : SignSequence} {n a k : ℕ} {H : History}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hH : Reverse.ValidAt x n (a + k) H.current) {u v : ℕ ⊕ ℕ}
    (huv : u ≠ v) (t : ℝ) :
    (∫ H', (if u ∈ (stage H' k).roots ∧ v ∈ (stage H' k).roots ∧
        t < (H'.current.depth u : ℝ) ∧ t < (H'.current.depth v : ℝ)
      then (1 : ℝ) else 0) ∂blockHistoryLaw x a k H) ≤
      if u ∈ H.current.roots ∧ v ∈ H.current.roots then
        Reverse.blockTailProbability x n hn a k t ^ 2 + Reverse.blockCoalescenceRisk x a k
      else 0 := by
  have he : (fun H' => if u ∈ (stage H' k).roots ∧ v ∈ (stage H' k).roots ∧
        t < (H'.current.depth u : ℝ) ∧ t < (H'.current.depth v : ℝ) then (1 : ℝ) else 0)
      =ᵐ[blockHistoryLaw x a k H]
        fun H' => if u ∈ H.current.roots ∧ v ∈ H.current.roots ∧
          t < (H'.current.depth u : ℝ) ∧ t < (H'.current.depth v : ℝ) then (1 : ℝ) else 0 := by
    filter_upwards [blockHistoryLaw_top_stage x a k H] with H' h
    rw [h]
  rw [integral_congr_ae he]
  by_cases hroot : u ∈ H.current.roots ∧ v ∈ H.current.roots
  · rw [ite_eq_left hroot]
    simp only [hroot.1, hroot.2, true_and]
    have hL : HasLaw History.current (Reverse.blockLaw x a k H.current) (blockHistoryLaw x a k H) :=
      ⟨measurable_from_top.aemeasurable, map_blockHistoryLaw_current x a k H⟩
    have hi := hL.integral_comp
      (show AEStronglyMeasurable (fun F : Reverse.Forest =>
        if t < (F.depth u : ℝ) ∧ t < (F.depth v : ℝ) then (1 : ℝ) else 0)
          (Reverse.blockLaw x a k H.current) from measurable_from_top.aestronglyMeasurable)
    simp only [Function.comp_def] at hi
    rw [hi, integral_ite_indicator _ _ (by trivial)]
    exact Reverse.blockLaw_pair_tail_le hn hk hH hroot.1 hroot.2 huv t
  · rw [ite_eq_right hroot]
    have hz : (fun H' : History => if u ∈ H.current.roots ∧ v ∈ H.current.roots ∧
        t < (H'.current.depth u : ℝ) ∧ t < (H'.current.depth v : ℝ) then (1 : ℝ) else 0) =
        fun _ => 0 := by
      funext H'
      have hh : ¬(u ∈ H.current.roots ∧ v ∈ H.current.roots ∧
          t < (H'.current.depth u : ℝ) ∧ t < (H'.current.depth v : ℝ)) :=
        fun h => hroot ⟨h.1, h.2.1⟩
      exact ite_eq_right hh
    rw [hz, integral_zero]

/-- Integrate the conditional estimate against the actual past law at the
top of the block. The probability of being two roots is kept explicitly. -/
theorem lawAfter_root_pair_tail_le (x : SignSequence) (n a k : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    {u v : ℕ ⊕ ℕ} (huv : u ≠ v) (t : ℝ) :
    (lawAfter x n (n - a)).real
      {H | u ∈ (stage H k).roots ∧ v ∈ (stage H k).roots ∧
        t < (H.current.depth u : ℝ) ∧ t < (H.current.depth v : ℝ)} ≤
      (lawAfter x n (n - (a + k))).real {H | u ∈ H.current.roots ∧ v ∈ H.current.roots} *
        (Reverse.blockTailProbability x n hn a k t ^ 2 + Reverse.blockCoalescenceRisk x a k) := by
  let Q := Reverse.blockTailProbability x n hn a k t ^ 2 + Reverse.blockCoalescenceRisk x a k
  let P : History → Prop := fun H => u ∈ (stage H k).roots ∧ v ∈ (stage H k).roots ∧
    t < (H.current.depth u : ℝ) ∧ t < (H.current.depth v : ℝ)
  let R : History → Prop := fun H => u ∈ H.current.roots ∧ v ∈ H.current.roots
  change (lawAfter x n (n - a)).real {H | P H} ≤ _
  rw [← integral_history_indicator _ P, lawAfter_eq_bind_blockHistoryLaw x n a k hk]
  have hi : Integrable (fun H => if P H then (1 : ℝ) else 0)
      ((lawAfter x n (n - (a + k))).bind (blockHistoryLaw x a k)) := by
    rw [← lawAfter_eq_bind_blockHistoryLaw x n a k hk]
    exact history_indicator_integrable _ P
  rw [integral_bind_of_integrable _ _ measurable_from_top hi]
  have hiInner : Integrable (fun H => ∫ H', (if P H' then (1 : ℝ) else 0)
      ∂blockHistoryLaw x a k H) (lawAfter x n (n - (a + k))) := by
    apply integrable_unitInterval_function _ measurable_from_top
    intro H
    apply integral_unitInterval_bounds _ measurable_from_top
    intro H'
    split_ifs <;> norm_num
  have hiRhs : Integrable (fun H => (if R H then (1 : ℝ) else 0) * Q)
      (lawAfter x n (n - (a + k))) :=
    (history_indicator_integrable _ R).mul_const Q
  calc
    _ ≤ ∫ H, (if R H then (1 : ℝ) else 0) * Q ∂lawAfter x n (n - (a + k)) := by
      apply integral_mono_ae hiInner hiRhs
      filter_upwards [lawAfter_current_valid x n (n - (a + k)) hn (by omega)] with H hH
      have hvalid : Reverse.ValidAt x n (a + k) H.current := by
        simpa only [Nat.sub_sub_self hk] using hH
      have h := blockHistoryLaw_root_pair_tail_le hn hk hvalid huv t
      change (∫ H', (if P H' then (1 : ℝ) else 0) ∂blockHistoryLaw x a k H) ≤
        if R H then Q else 0 at h
      by_cases hr : R H <;> simpa only [hr, ↓reduceIte, one_mul, zero_mul] using h
    _ = _ := by rw [integral_mul_const, integral_history_indicator]

theorem stage_previous_iterate (H : History) (a j : ℕ) :
    stage ((previous^[a]) H) j = stage H (a + j) := by
  induction a generalizing H with
  | zero => simp
  | succ a ih =>
    rw [Function.iterate_succ_apply, ih, stage_previous]
    congr 1
    omega

/-- The second-moment pair estimate on the common full history, weighted by
membership in the actual random root set at phase `b`. -/
theorem fullLaw_root_pair_tail_le (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {a b : ℕ} (hab : a ≤ b) (hbn : b ≤ n)
    {u v : ℕ ⊕ ℕ} (huv : u ≠ v) (t : ℝ) :
    (fullLaw x n).real {H | u ∈ (stage H b).roots ∧ v ∈ (stage H b).roots ∧
      t < ((stage H a).depth u : ℝ) ∧ t < ((stage H a).depth v : ℝ)} ≤
      (fullLaw x n).real {H | u ∈ (stage H b).roots ∧ v ∈ (stage H b).roots} *
        (Reverse.blockTailProbability x n hn a (b - a) t ^ 2 + Reverse.blockCoalescenceRisk x a (b - a)) := by
  have hA : HasLaw (previous^[a]) (lawAfter x n (n - a)) (fullLaw x n) :=
    ⟨measurable_from_top.aemeasurable, map_fullLaw_previous_iterate x n a (hab.trans hbn)⟩
  have hB : HasLaw (previous^[b]) (lawAfter x n (n - b)) (fullLaw x n) :=
    ⟨measurable_from_top.aemeasurable, map_fullLaw_previous_iterate x n b hbn⟩
  have heA := hA.measureReal_eq (p := fun H => u ∈ (stage H (b - a)).roots ∧
    v ∈ (stage H (b - a)).roots ∧ t < (H.current.depth u : ℝ) ∧ t < (H.current.depth v : ℝ))
    (by trivial)
  have heB := hB.measureReal_eq (p := fun H => u ∈ H.current.roots ∧ v ∈ H.current.roots) (by trivial)
  simp only [stage_previous_iterate, Nat.add_sub_of_le hab, current_previous_iterate_eq_stage] at heA heB
  rw [heA, heB]
  simpa only [Nat.add_sub_of_le hab] using lawAfter_root_pair_tail_le x n a (b - a) hn (by omega) huv t

end Freezing1.ReverseHistory
