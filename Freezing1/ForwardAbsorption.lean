module

public import Freezing1.ForwardLaw

/-!
# Absorption at the first extinction time

The integer schedule walk is not stopped. The constructed tree is: after its
active set becomes empty, every subsequent transition keeps the same tree.
This distinction is preserved in the statements below.
-/

@[expose] public section

namespace Freezing1

theorem activeCount_eq_zero_of_extinctionTime_eq {x : SignSequence} {n : ℕ}
    (hn : extinctionTime x = n) : activeCount x n = 0 := by
  unfold extinctionTime at hn
  split_ifs at hn with h
  · have he : Nat.find h = n := by exact_mod_cast hn
    simpa only [he] using Nat.find_spec h
  · simp at hn

namespace Forward

open MeasureTheory

/-- On each legal deterministic trajectory, absorption is pathwise permanent. -/
theorem run_constant_of_active_empty (x : SignSequence) (choice : ℕ → ℕ) (n : ℕ)
    (hn : (run x choice n).active = ∅) (k : ℕ) :
    run x choice (n + k) = run x choice n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, run, ih]
    exact step_of_active_empty _ _ _ _ hn

/-- Through the first extinction time, zero active count means complete freezing. -/
theorem treeLaw_active_empty_iff (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ s ∂treeLaw x n, s.active = ∅ ↔ activeCount x n = 0 := by
  filter_upwards [treeLaw_counts x n hn] with s hs
  rw [← hs.1]
  simp

theorem treeLaw_active_empty_at_extinction {x : SignSequence} {n : ℕ}
    (hn : extinctionTime x = n) : ∀ᵐ s ∂treeLaw x n, s.active = ∅ := by
  filter_upwards [treeLaw_active_empty_iff x n hn.symm.le] with s hs
  exact hs.mpr (activeCount_eq_zero_of_extinctionTime_eq hn)

/-- The actual forward tree law stays constant at every time after finite extinction. -/
theorem treeLaw_constant_after_extinction {x : SignSequence} {n : ℕ}
    (hn : extinctionTime x = n) (k : ℕ) : treeLaw x (n + k) = treeLaw x n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, treeLaw, ih]
    calc
      _ = (treeLaw x n).bind Measure.dirac := by
        apply Measure.bind_congr_right
        filter_upwards [treeLaw_active_empty_at_extinction hn] with s hs
        exact transitionLaw_eq_dirac_of_empty s _ _ hs
      _ = treeLaw x n := Measure.bind_dirac

end Forward
end Freezing1
