module

public import Freezing1.InterleavedSelectionCounts
public import Freezing1.InterleavedWordResolution
public import Freezing1.InterleavedChainObservations

/-!
# Deterministic resolution of extracted words

Every fixed extracted word is eventually the padded finite observation
word. Fairness forces the padding state to be absorbing whenever the
requested number of actual selections is never reached.
-/

@[expose] public section

namespace Freezing1.InterleavedChain

open MeasureTheory ProbabilityTheory CountableMarkovChain Filter
open scoped ENNReal Classical

/-- This identity includes the case of finitely many selections. -/
theorem padded_collect_eq_selected {D : Type*} (marks : ℕ → Bool) (values : ℕ → D)
    (side : Bool) {r N : ℕ} (h : selectedTime marks side r ≤ N) :
    paddedWord ((collect marks values side N).getLastD (values 0))
      (collect marks values side N) r =
      List.ofFn (fun i : Fin r => values (selectedTime marks side (i.val + 1))) := by
  unfold paddedWord
  apply congrArg List.ofFn
  funext i
  by_cases hi : i.val < selectionCount marks side N
  · rw [collect_eq_ofFn]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi)]
    simp
  · rw [List.getD_eq_default _ _ (by simpa only [length_collect] using Nat.le_of_not_gt hi),
      getLastD_collect]
    have hb : ∀ m, selectionCount marks side m ≤ selectionCount marks side N :=
      (count_ge_or_globally_bounded marks side h).resolve_left (by omega)
    have hrank := selectedTime_rank marks side (k := selectionCount marks side N) (N := N) le_rfl
    have hnext := nextTime_of_count_bounded marks side
      (selectedTime marks side (selectionCount marks side N)) (fun m => by rw [hrank.2]; exact hb m)
    rw [selectedTime_stable marks side rfl hnext (show selectionCount marks side N ≤ i.val + 1 by omega)]

variable {E : Type*}

def coordinate (s : State E) (side : Bool) : E := if side then s.1 else s.2.1

def observedCoordinate (H : ℕ → State E) (side : Bool) (n : ℕ) : List E :=
  if side then (observations H n).1 else (observations H n).2

noncomputable def extractedWord (H : ℕ → State E) (side : Bool) (r : ℕ) : List E :=
  List.ofFn (fun i : Fin r => extracted H side (i.val + 1))

theorem observations_eq_collect (H : ℕ → State E) (n : ℕ) :
    observations H n =
      (collect (fun k => (H k).2.2) (fun k => (H k).1) true n,
       collect (fun k => (H k).2.2) (fun k => (H k).2.1) false n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change updateObservation (observations H n) (H (n + 1)) = _
    rw [ih]
    cases he : (H (n + 1)).2.2 <;> simp [updateObservation, collect, he]

theorem observedCoordinate_eq_collect (H : ℕ → State E) (side : Bool) (n : ℕ) :
    observedCoordinate H side n =
      collect (fun k => (H k).2.2) (fun k => coordinate (H k) side) side n := by
  cases side <;> simp [observedCoordinate, coordinate, observations_eq_collect]

theorem observedCoordinate_last (H : ℕ → State E)
    (h : ∀ n, MovesOnlySelected (H n) (H (n + 1))) (side : Bool) (n : ℕ) :
    (observedCoordinate H side n).getLastD (coordinate (H 0) side) = coordinate (H n) side := by
  have hh := observations_last H h n
  cases side <;> simp only [observedCoordinate, coordinate, Bool.false_eq_true, ite_false, ite_true]
  · exact hh.2
  · exact hh.1

theorem padded_observedCoordinate_eq_extractedWord (H : ℕ → State E) (side : Bool)
    {r N : ℕ} (h : selectedTime (fun k => (H k).2.2) side r ≤ N) :
    paddedWord ((observedCoordinate H side N).getLastD (coordinate (H 0) side))
      (observedCoordinate H side N) r = extractedWord H side r := by
  rw [observedCoordinate_eq_collect]
  simpa only [extractedWord, extracted, coordinate] using
    padded_collect_eq_selected (fun k => (H k).2.2) (fun k => coordinate (H k) side) side h

variable [MeasurableSpace E] [MeasurableSingletonClass E]

/-- The pathwise version of source fairness, to be obtained from the genuine
Markov shift law at every deterministic time. -/
def PathFair (α : Kernel E E) (H : ℕ → State E) : Prop :=
  ∀ side n, ¬Absorbing α (coordinate (H n) side) →
    ∃ m, n < m ∧ (H m).2.2 = side

/-- Completion eventually equals the exact extracted-cylinder indicator.
No assertion of independence is used in this deterministic step. -/
theorem completion_observed_eventually (α : Kernel E E) [IsMarkovKernel α]
    (H : ℕ → State E) (hm : ∀ n, MovesOnlySelected (H n) (H (n + 1)))
    (hf : PathFair α H) (side : Bool) (ys : List E) :
    ∀ᶠ N in atTop, completion α (coordinate (H 0) side) (observedCoordinate H side N) ys =
      if extractedWord H side ys.length = ys then 1 else 0 := by
  filter_upwards [eventually_ge_atTop (selectedTime (fun k => (H k).2.2) side ys.length)] with N hN
  have hresolve : ys.length ≤ (observedCoordinate H side N).length ∨
      Absorbing α ((observedCoordinate H side N).getLastD (coordinate (H 0) side)) := by
    rcases count_ge_or_globally_bounded (fun k => (H k).2.2) side hN with hcount | hcount
    · left
      simpa only [observedCoordinate_eq_collect, length_collect] using hcount
    · right
      rw [observedCoordinate_last H hm]
      by_contra hn
      obtain ⟨m, hNm, hmark⟩ := hf side N hn
      exact (not_lt_of_ge (hcount m))
        (selectionCount_strict_of_marked (fun k => (H k).2.2) side hNm hmark)
  rw [completion_resolved α _ _ _ hresolve,
    padded_observedCoordinate_eq_extractedWord H side hN]

end Freezing1.InterleavedChain
