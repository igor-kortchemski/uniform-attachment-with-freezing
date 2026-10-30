module

public import Freezing1.ForwardSchedulePrefix
public import Freezing1.ForwardComponentContinuation

/-! Source A63: retain a finite schedule and continue with positive steps. -/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

def positiveExtension (x : SignSequence) (b : ℕ) : SignSequence :=
  fun i => if i ≤ b then x i else true

theorem positiveExtension_agrees (x : SignSequence) (b : ℕ) :
    SchedulesAgreeThrough (positiveExtension x b) x b :=
  fun _i _ hi => ite_eq_left hi

theorem activeCount_positiveExtension_prefix (x : SignSequence) (b : ℕ) {i : ℕ} (hi : i ≤ b) :
    activeCount (positiveExtension x b) i = activeCount x i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [activeCount_succ, activeCount_succ, ih (by omega)]
    simp only [positiveExtension, ite_eq_left hi]

theorem activeCount_positiveExtension_tail (x : SignSequence) (b j : ℕ) :
    activeCount (positiveExtension x b) (b + j) = activeCount x b + (j : ℤ) := by
  induction j with
  | zero => simp only [activeCount_positiveExtension_prefix x b le_rfl, Int.natCast_zero, add_zero]
  | succ j ih =>
    rw [show b + (j + 1) = (b + j) + 1 by omega, activeCount_succ, ih]
    simp only [positiveExtension, ite_eq_right (show ¬b + j + 1 ≤ b by omega), ↓reduceIte]
    push_cast
    ring

theorem positiveExtension_positive (x : SignSequence) {b : ℕ} (hb : PositiveThrough x b) (i : ℕ) :
    0 < activeCount (positiveExtension x b) i := by
  by_cases hi : i ≤ b
  · rw [activeCount_positiveExtension_prefix x b hi]
    exact hb i hi
  · have he : i = b + (i - b) := by omega
    rw [he, activeCount_positiveExtension_tail]
    exact add_pos_of_pos_of_nonneg (hb b le_rfl) (Int.natCast_nonneg _)

theorem positiveExtension_extinctionTime (x : SignSequence) {b : ℕ} (hb : PositiveThrough x b) :
    extinctionTime (positiveExtension x b) = ⊤ :=
  (extinctionTime_eq_top_iff _).mpr (positiveExtension_positive x hb)

namespace Forward

theorem treeLaw_positiveExtension (x : SignSequence) (b : ℕ) {i : ℕ} (hi : i ≤ b) :
    treeLaw (positiveExtension x b) i = treeLaw x i :=
  treeLaw_eq_of_schedule_prefix ((positiveExtension_agrees x b).mono hi)

/-- The actual original infinite histories and the positive extension have
identical complete finite path laws through the retained endpoint. -/
theorem fullLaw_prefix_positiveExtension (x : SignSequence) (b : ℕ) :
    (ForwardInfiniteHistory.fullLaw (positiveExtension x b)).map (Preorder.frestrictLe b) =
      (ForwardInfiniteHistory.fullLaw x).map (Preorder.frestrictLe b) :=
  ForwardInfiniteHistory.map_prefix_eq_of_schedule_prefix (positiveExtension_agrees x b)

theorem continuationLaw_positiveExtension (x : SignSequence) (b : ℕ) {a k : ℕ}
    (hend : a + k ≤ b) (s : State) :
    continuationLaw (positiveExtension x b) a k s = continuationLaw x a k s := by
  induction k generalizing a s with
  | zero => rfl
  | succ k ih =>
    rw [continuationLaw, continuationLaw]
    have hsign : positiveExtension x b (a + 1) = x (a + 1) := ite_eq_left (by omega)
    rw [hsign]
    congr 1
    funext t
    exact ih (by omega) t

/-- Genuine active descendants start with one ball. The finite process is
unchanged by the extension; a later-frozen distinguished root remains a
separate possible extra vertex under the source convention. -/
theorem positiveExtension_component_urn {x : SignSequence} {a b : ℕ} {s : State}
    (hd : PhaseData x a s) (hab : a ≤ b) (hb : PositiveThrough x b)
    {r : ℕ} (hr : r ∈ s.active) :
    (continuationLaw (positiveExtension x b) a (b - a) s).map
        (fun t => componentPopulation t a r) =
      SignedUrn.continuationLaw (activeCount x) a (b - a) 1 := by
  rw [continuationLaw_positiveExtension x b (show a + (b - a) ≤ b by omega)]
  apply continuationLaw_componentPopulation_of_root hd _ hr
  have hτ := ((lt_extinctionTime_iff x b).mpr hb).le
  simpa only [Nat.add_sub_of_le hab] using hτ

theorem positiveExtension_marked_root_cap (s : State) (a r : ℕ) :
    (componentPopulationWithRoot s a r : ℤ) ≤ componentPopulation s a r + 1 :=
  componentPopulationWithRoot_le s a r

end Forward
end Freezing1
