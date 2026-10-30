module

public import Freezing1.IntervalCounts

/-! Both literal attachment/freezing count identities preceding EqProp9. -/

@[expose] public section

namespace Freezing1

open scoped Classical

/-- The actual freezing steps with paper index in `(a,b]`. -/
def intervalMinusCount (x : SignSequence) (a b : ℕ) : ℕ :=
  ((Finset.Ioc a b).filter fun i => x i = false).card

theorem intervalPlusCount_add_intervalMinusCount (x : SignSequence) (a b : ℕ) :
    intervalPlusCount x a b + intervalMinusCount x a b = b - a := by
  simpa only [intervalPlusCount, intervalMinusCount, Bool.not_eq_true, Nat.card_Ioc] using
    Finset.card_filter_add_card_filter_not (s := Finset.Ioc a b) (fun i => x i = true)

theorem intervalPlusCount_sub_intervalMinusCount (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) :
    (intervalPlusCount x a b : ℤ) - intervalMinusCount x a b =
      activeCount x b - activeCount x a := by
  have hs : (intervalPlusCount x a b : ℤ) + intervalMinusCount x a b = (b : ℤ) - a := by
    exact_mod_cast intervalPlusCount_add_intervalMinusCount x a b
  have hp := plusCount_add_intervalPlusCount (x := x) hab
  have hp' : (plusCount x a : ℤ) + intervalPlusCount x a b = plusCount x b := by
    exact_mod_cast hp
  rw [activeCount_eq, activeCount_eq]
  omega

theorem intervalPlusCount_and_intervalMinusCount_identities (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) :
    (intervalPlusCount x a b : ℝ) - intervalMinusCount x a b =
        (activeCount x b : ℝ) - activeCount x a ∧
    (intervalPlusCount x a b : ℝ) + intervalMinusCount x a b = (b : ℝ) - a := by
  constructor
  · exact_mod_cast intervalPlusCount_sub_intervalMinusCount x hab
  · exact_mod_cast intervalPlusCount_add_intervalMinusCount x a b

end Freezing1
