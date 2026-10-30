module

public import Freezing1.InterleavedChainKernel

/-!
# The exact extraction times in L06

A coordinate is read at its next selection time. If there is no later
selection, its previous time is retained, exactly as in the source. All
extracted paths are measurable, including on exceptional non-fair histories.
-/

@[expose] public section

namespace Freezing1.InterleavedChain

open MeasureTheory ProbabilityTheory
open scoped Classical

/-- The totalized minimum predicate: the previous time is eligible only
when there is no later selection of the requested side. -/
def NextCandidate (marks : ℕ → Bool) (side : Bool) (a n : ℕ) : Prop :=
  (a < n ∧ marks n = side) ∨ (n = a ∧ ∀ m, a < m → marks m ≠ side)

theorem nextCandidate_exists (marks : ℕ → Bool) (side : Bool) (a : ℕ) :
    ∃ n, NextCandidate marks side a n := by
  by_cases h : ∃ n, a < n ∧ marks n = side
  · obtain ⟨n, hn⟩ := h
    exact ⟨n, Or.inl hn⟩
  · exact ⟨a, Or.inr ⟨rfl, by simpa only [not_exists, not_and] using h⟩⟩

noncomputable def nextTime (marks : ℕ → Bool) (side : Bool) (a : ℕ) : ℕ :=
  Nat.find (nextCandidate_exists marks side a)

theorem nextTime_spec (marks : ℕ → Bool) (side : Bool) (a : ℕ) :
    NextCandidate marks side a (nextTime marks side a) :=
  Nat.find_spec (nextCandidate_exists marks side a)

theorem le_nextTime (marks : ℕ → Bool) (side : Bool) (a : ℕ) :
    a ≤ nextTime marks side a := by
  rcases nextTime_spec marks side a with h | h
  · exact h.1.le
  · exact h.1.ge

theorem nextTime_of_none (marks : ℕ → Bool) (side : Bool) (a : ℕ)
    (h : ∀ m, a < m → marks m ≠ side) : nextTime marks side a = a := by
  apply le_antisymm _ (le_nextTime marks side a)
  exact Nat.find_min' (nextCandidate_exists marks side a) (Or.inr ⟨rfl, h⟩)

theorem nextTime_of_exists (marks : ℕ → Bool) (side : Bool) (a : ℕ)
    (h : ∃ n, a < n ∧ marks n = side) :
    a < nextTime marks side a ∧ marks (nextTime marks side a) = side ∧
      ∀ m, a < m → m < nextTime marks side a → marks m ≠ side := by
  have hs := nextTime_spec marks side a
  have hs' : a < nextTime marks side a ∧ marks (nextTime marks side a) = side := by
    rcases hs with hsel | hnone
    · exact hsel
    · obtain ⟨m, hm, he⟩ := h
      exact (hnone.2 m hm he).elim
  refine ⟨hs'.1, hs'.2, ?_⟩
  intro m hm hmn he
  exact (Nat.find_min (nextCandidate_exists marks side a) hmn) (Or.inl ⟨hm, he⟩)

theorem measurable_nextTime_fixed (side : Bool) (a : ℕ) :
    Measurable (fun marks : ℕ → Bool => nextTime marks side a) := by
  apply measurable_find
  intro n
  have hsel : Measurable (fun marks : ℕ → Bool => a < n ∧ marks n = side) :=
    measurable_const.and ((measurable_pi_apply n).eq measurable_const)
  have hnone : Measurable (fun marks : ℕ → Bool => ∀ m, a < m → marks m ≠ side) := by
    apply Measurable.forall
    intro m
    exact measurable_const.imp (((measurable_pi_apply m).eq measurable_const).not)
  exact (hsel.or (measurable_const.and hnone)).setOf

theorem measurable_nextTime (side : Bool) :
    Measurable (fun p : (ℕ → Bool) × ℕ => nextTime p.1 side p.2) :=
  measurable_from_prod_countable_left (measurable_nextTime_fixed side)

noncomputable def selectedTime (marks : ℕ → Bool) (side : Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => nextTime marks side (selectedTime marks side k)

theorem selectedTime_mono (marks : ℕ → Bool) (side : Bool) :
    Monotone (selectedTime marks side) := by
  apply monotone_nat_of_le_succ
  intro k
  exact le_nextTime marks side _

theorem measurable_selectedTime (side : Bool) (k : ℕ) :
    Measurable (fun marks : ℕ → Bool => selectedTime marks side k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih => exact (measurable_nextTime side).comp (measurable_id.prodMk ih)

variable {E : Type*} [MeasurableSpace E]

/-- The coordinate extracted with the source's exact fallback convention. -/
noncomputable def extracted (H : ℕ → State E) (side : Bool) (k : ℕ) : E :=
  let s := H (selectedTime (fun n => (H n).2.2) side k)
  if side then s.1 else s.2.1

theorem measurable_extracted (side : Bool) :
    Measurable (fun H : ℕ → State E => extracted H side) := by
  apply Measurable.of_eval
  intro k
  have hmarks : Measurable (fun H : ℕ → State E => fun n => (H n).2.2) := by fun_prop
  have ht := (measurable_selectedTime side k).comp hmarks
  have heval : Measurable (fun p : (ℕ → State E) × ℕ => p.1 p.2) :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply n
  have hs := heval.comp (measurable_id.prodMk ht)
  cases side <;> simp only [extracted, Bool.false_eq_true, ite_false, ite_true]
  · exact hs.snd.fst
  · exact hs.fst

omit [MeasurableSpace E] in
@[simp] theorem extracted_zero (H : ℕ → State E) (side : Bool) :
    extracted H side 0 = if side then (H 0).1 else (H 0).2.1 := rfl

end Freezing1.InterleavedChain
