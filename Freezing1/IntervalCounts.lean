module

public import Freezing1.Path
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Attachment counts on an interval

Equation `EqProp9` in the proof of the uniform estimate for the height scale
expresses the number of attachment steps in terms of the endpoint values of
the active-count walk, then bounds it using endpoint errors. These identities
are deterministic and do not require the random-tree construction.
-/

@[expose] public section

namespace Freezing1

/-- Number of attachment steps with paper index in `(a, b]`. -/
def intervalPlusCount (x : SignSequence) (a b : ℕ) : ℕ :=
  ((Finset.Ioc a b).filter fun i => x i = true).card

theorem intervalPlusCount_eq_sum (x : SignSequence) (a b : ℕ) :
    intervalPlusCount x a b =
      ∑ i ∈ Finset.Ico a b, if x (i + 1) then 1 else 0 := by
  rw [Finset.sum_Ico_add' (fun i => if x i then (1 : ℕ) else 0) a b 1,
    Finset.Ico_add_one_add_one_eq_Ioc]
  simp [intervalPlusCount]

theorem plusCount_add_intervalPlusCount {x : SignSequence} {a b : ℕ}
    (hab : a ≤ b) : plusCount x a + intervalPlusCount x a b = plusCount x b := by
  simpa only [plusCount, intervalPlusCount_eq_sum] using
    Finset.sum_range_add_sum_Ico (fun i => if x (i + 1) then (1 : ℕ) else 0) hab

theorem intervalPlusCount_eq_sub {x : SignSequence} {a b : ℕ} (hab : a ≤ b) :
    intervalPlusCount x a b = plusCount x b - plusCount x a := by
  have := plusCount_add_intervalPlusCount (x := x) hab
  omega

/-- The exact counting identity in equation `EqProp9`. -/
theorem intervalPlusCount_eq_activeCount {x : SignSequence} {a b : ℕ}
    (hab : a ≤ b) :
    (intervalPlusCount x a b : ℝ) =
      ((activeCount x b : ℝ) - activeCount x a + b - a) / 2 := by
  have hc : (plusCount x a : ℝ) + intervalPlusCount x a b = plusCount x b := by
    exact_mod_cast plusCount_add_intervalPlusCount (x := x) hab
  have ha : (activeCount x a : ℝ) = 1 + 2 * (plusCount x a : ℝ) - a := by
    exact_mod_cast activeCount_eq x a
  have hb : (activeCount x b : ℝ) = 1 + 2 * (plusCount x b : ℝ) - b := by
    exact_mod_cast activeCount_eq x b
  linarith

/-- Equation `EqProp9`: endpoint ratio estimates control attachment counts.
The source uses the same `η` as a uniform maximum over a larger index set;
only the two resulting endpoint estimates are needed here. -/
theorem intervalPlusCount_bounds {x : SignSequence} {a b : ℕ} {c η : ℝ}
    (ha : 1 ≤ a) (hab : a < b) (hη : 0 ≤ η)
    (haerr : |(activeCount x a : ℝ) / a - c| ≤ η)
    (hberr : |(activeCount x b : ℝ) / b - c| ≤ η) :
    (c + 1) / 2 * ((b : ℝ) - a) - b * η ≤ intervalPlusCount x a b ∧
      (intervalPlusCount x a b : ℝ) ≤
        (c + 1) / 2 * ((b : ℝ) - a) + b * η := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
  have hb' : 0 < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab.le
  obtain ⟨hal, hau⟩ := abs_le.mp haerr
  obtain ⟨hbl, hbu⟩ := abs_le.mp hberr
  have hal' : (c - η) * a ≤ (activeCount x a : ℝ) :=
    (le_div_iff₀ ha').mp (by linarith)
  have hau' : (activeCount x a : ℝ) ≤ (c + η) * a :=
    (div_le_iff₀ ha').mp (by linarith)
  have hbl' : (c - η) * b ≤ (activeCount x b : ℝ) :=
    (le_div_iff₀ hb').mp (by linarith)
  have hbu' : (activeCount x b : ℝ) ≤ (c + η) * b :=
    (div_le_iff₀ hb').mp (by linarith)
  have heta : (a : ℝ) * η ≤ b * η := mul_le_mul_of_nonneg_right hab' hη
  rw [intervalPlusCount_eq_activeCount hab.le]
  constructor <;> nlinarith

end Freezing1
