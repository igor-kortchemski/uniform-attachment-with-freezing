module

public import Freezing1.ReverseForest

/-!
# Coherent finite histories of the reverse construction

The current forest and its entire earlier history are sampled together by
the original transition kernels. Forgetting history gives the existing
reverse marginal exactly. At the terminal time, list position `i` is phase
`i`, so later statements can refer to a genuine common probability space.
-/

@[expose] public section

namespace Freezing1.ReverseHistory

open MeasureTheory
open scoped ENNReal

structure History where
  current : Reverse.Forest
  past : List Reverse.Forest

instance : MeasurableSpace History := ⊤
instance : DiscreteMeasurableSpace History := ⟨fun _ => trivial⟩

def initial (x : SignSequence) (n : ℕ) : History := ⟨Reverse.initial x n, []⟩

def push (H : History) (F : Reverse.Forest) : History := ⟨F, H.current :: H.past⟩

/-- Remove the latest transition. On a pushed history this is its exact
predecessor, containing the whole past rather than just the previous state. -/
def previous (H : History) : History :=
  ⟨H.past.headD (RootedForest.isolated ∅), H.past.tail⟩

@[simp] theorem previous_push (H : History) (F : Reverse.Forest) :
    previous (push H F) = H := rfl

/-- Offset from the most recently sampled phase. The default is used only
outside the recorded history and will be excluded in all phase theorems. -/
def stage (H : History) (j : ℕ) : Reverse.Forest :=
  (H.current :: H.past).getD j (RootedForest.isolated ∅)

@[simp] theorem stage_zero (H : History) : stage H 0 = H.current := rfl

@[simp] theorem stage_push_succ (H : History) (F : Reverse.Forest) (j : ℕ) :
    stage (push H F) (j + 1) = stage H j := by
  simp [stage, push]

noncomputable def transitionLaw (x : SignSequence) (i : ℕ) (H : History) : Measure History :=
  (Reverse.transitionLaw x i H.current).map (push H)

instance transitionLaw_probability (x : SignSequence) (i : ℕ) (H : History) :
    IsProbabilityMeasure (transitionLaw x i H) := by
  unfold transitionLaw
  exact Measure.isProbabilityMeasure_map_iff measurable_from_top.aemeasurable |>.mpr inferInstance

theorem map_transitionLaw_current (x : SignSequence) (i : ℕ) (H : History) :
    (transitionLaw x i H).map History.current = Reverse.transitionLaw x i H.current := by
  rw [transitionLaw, Measure.map_map measurable_from_top measurable_from_top]
  exact Measure.map_id

theorem map_transitionLaw_stage_succ (x : SignSequence) (i : ℕ) (H : History) (j : ℕ) :
    (transitionLaw x i H).map (fun H' => stage H' (j + 1)) =
      Measure.dirac (stage H j) := by
  rw [transitionLaw, Measure.map_map measurable_from_top measurable_from_top]
  simp only [Function.comp_def, stage_push_succ]
  simp

theorem map_transitionLaw_previous (x : SignSequence) (i : ℕ) (H : History) :
    (transitionLaw x i H).map previous = Measure.dirac H := by
  rw [transitionLaw, Measure.map_map measurable_from_top measurable_from_top]
  simp only [Function.comp_def, previous_push]
  simp

theorem transitionLaw_push_ae (x : SignSequence) (i : ℕ) (H : History)
    (P : History → Prop) (hP : ∀ F, P (push H F)) :
    ∀ᵐ H' ∂transitionLaw x i H, P H' := by
  exact (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mpr
    (Filter.Eventually.of_forall hP)

noncomputable def lawAfter (x : SignSequence) (n : ℕ) : ℕ → Measure History
  | 0 => Measure.dirac (initial x n)
  | k + 1 => if k < n then
      (lawAfter x n k).bind (transitionLaw x (n - (k + 1)))
    else lawAfter x n k

instance lawAfter_probability (x : SignSequence) (n k : ℕ) :
    IsProbabilityMeasure (lawAfter x n k) := by
  induction k with
  | zero => change IsProbabilityMeasure (Measure.dirac (initial x n)); infer_instance
  | succ k ih =>
    simp only [lawAfter]
    split_ifs
    · exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
        (Filter.Eventually.of_forall (fun H => transitionLaw_probability x _ H))
    · exact ih

/-- The actual current-state marginal is unchanged by recording the past. -/
theorem map_lawAfter_current (x : SignSequence) (n k : ℕ) :
    (lawAfter x n k).map History.current = Reverse.lawAfter x n k := by
  induction k with
  | zero => exact Measure.map_dirac' measurable_from_top _
  | succ k ih =>
    simp only [lawAfter, Reverse.lawAfter]
    split_ifs with hk
    · rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
      calc
        _ = (lawAfter x n k).bind (fun H => Reverse.transitionLaw x (n - (k + 1)) H.current) := by
          congr 1
          funext H
          exact map_transitionLaw_current x (n - (k + 1)) H
        _ = ((lawAfter x n k).map History.current).bind
            (Reverse.transitionLaw x (n - (k + 1))) :=
          (Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable).symm
        _ = _ := by rw [ih]
    · exact ih

/-- Erasing one step recovers the exact joint law of the preceding history. -/
theorem map_lawAfter_previous (x : SignSequence) (n k : ℕ) (hk : k < n) :
    (lawAfter x n (k + 1)).map previous = lawAfter x n k := by
  rw [lawAfter, ite_eq_left hk,
    Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  simp_rw [map_transitionLaw_previous]
  exact Measure.bind_dirac

/-- Every recorded position has the correct earlier reverse marginal. -/
theorem map_lawAfter_stage (x : SignSequence) (n k j : ℕ) (hk : k ≤ n) (hj : j ≤ k) :
    (lawAfter x n k).map (fun H => stage H j) = Reverse.lawAfter x n (k - j) := by
  induction k generalizing j with
  | zero =>
    have : j = 0 := by omega
    subst j
    exact map_lawAfter_current x n 0
  | succ k ih =>
    cases j with
    | zero => simpa only [stage_zero, Nat.sub_zero] using map_lawAfter_current x n (k + 1)
    | succ j =>
      have hkn : k < n := by omega
      rw [lawAfter, ite_eq_left hkn,
        Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
      simp_rw [map_transitionLaw_stage_succ]
      rw [Measure.bind_dirac_eq_map _ measurable_from_top]
      simpa only [Nat.add_sub_add_right] using ih j (by omega) (by omega)

theorem lawAfter_current_valid (x : SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k ≤ n) :
    ∀ᵐ H ∂lawAfter x n k, Reverse.ValidAt x n (n - k) H.current := by
  apply ae_of_ae_map (f := History.current) measurable_from_top.aemeasurable
  rw [map_lawAfter_current]
  exact Reverse.lawAfter_valid x n k hn hk

/-- There are exactly `k` earlier forests after `k` reverse transitions. -/
theorem lawAfter_past_length (x : SignSequence) (n k : ℕ) (hk : k ≤ n) :
    ∀ᵐ H ∂lawAfter x n k, H.past.length = k := by
  induction k with
  | zero => simp [lawAfter, initial]
  | succ k ih =>
    have hkn : k < n := by omega
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [lawAfter, ite_eq_left hkn, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _H, (1 : ℝ≥0∞) ∂lawAfter x n k := by
        apply lintegral_congr_ae
        filter_upwards [ih (by omega)] with H hH
        apply (ae_iff_prob_eq_one measurable_from_top).mp
        apply transitionLaw_push_ae
        intro F
        simp only [push, List.length_cons, hH]
      _ = 1 := by simp

noncomputable def fullLaw (x : SignSequence) (n : ℕ) : Measure History := lawAfter x n n

instance fullLaw_probability (x : SignSequence) (n : ℕ) :
    IsProbabilityMeasure (fullLaw x n) := lawAfter_probability x n n

/-- In the completed coherent history, position `i` is exactly the paper's
phase `i`, on the same probability space as all other positions. -/
theorem map_fullLaw_phase (x : SignSequence) (n i : ℕ) (hi : i ≤ n) :
    (fullLaw x n).map (fun H => stage H i) = Reverse.lawAfter x n (n - i) :=
  map_lawAfter_stage x n n i le_rfl hi

end Freezing1.ReverseHistory
