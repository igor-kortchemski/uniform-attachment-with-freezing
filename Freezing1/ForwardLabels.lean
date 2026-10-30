module

public import Freezing1.ForwardLaw

/-!
# Freezing-time labels in Algorithm 1

The displayed frozen labels are positive past times, with no repetition.
These properties are derived from the transitions, including absorption.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory

structure LabelsValidAt (n : ℕ) (s : State) : Prop where
  bounded : ∀ v ∈ s.vertices, ∀ t, s.frozenAt v = some t → 0 < t ∧ t ≤ n
  injective : ∀ u ∈ s.vertices, ∀ v ∈ s.vertices, ∀ t,
    s.frozenAt u = some t → s.frozenAt v = some t → u = v

theorem initial_labels_valid : LabelsValidAt 0 initial := by
  constructor <;> simp [initial]

theorem LabelsValidAt.mono {n m : ℕ} {s : State} (h : LabelsValidAt n s) (hnm : n ≤ m) :
    LabelsValidAt m s :=
  { h with bounded := fun v hv t ht => ⟨(h.bounded v hv t ht).1,
      (h.bounded v hv t ht).2.trans hnm⟩ }

theorem LabelsValidAt.attach {n : ℕ} {s : State} (h : LabelsValidAt n s)
    (v : ℕ) : LabelsValidAt (n + 1) (attach s (n + 1) v) := by
  constructor
  · intro u hu t ht
    by_cases hue : u = n + 1
    · simp [Forward.attach, hue] at ht
    · have huold : u ∈ s.vertices := (Finset.mem_insert.mp hu).resolve_left hue
      have htold : s.frozenAt u = some t := by simpa [Forward.attach, hue] using ht
      exact ⟨(h.bounded u huold t htold).1, (h.bounded u huold t htold).2.trans (Nat.le_succ n)⟩
  · intro u hu w hw t hut hwt
    have hue : u ≠ n + 1 := by intro he; simp [Forward.attach, he] at hut
    have hwe : w ≠ n + 1 := by intro he; simp [Forward.attach, he] at hwt
    exact h.injective u ((Finset.mem_insert.mp hu).resolve_left hue)
      w ((Finset.mem_insert.mp hw).resolve_left hwe) t
      (by simpa [Forward.attach, hue] using hut) (by simpa [Forward.attach, hwe] using hwt)

theorem LabelsValidAt.freeze {n : ℕ} {s : State} (h : LabelsValidAt n s)
    (v : ℕ) : LabelsValidAt (n + 1) (freeze s (n + 1) v) := by
  constructor
  · intro u hu t ht
    by_cases huv : u = v
    · simp only [Forward.freeze, huv, Function.update_self, Option.some.injEq] at ht
      omega
    · have htold : s.frozenAt u = some t := by simpa [Forward.freeze, huv] using ht
      exact ⟨(h.bounded u hu t htold).1, (h.bounded u hu t htold).2.trans (Nat.le_succ n)⟩
  · intro u hu w hw t hut hwt
    by_cases huv : u = v
    · subst u
      by_cases hwv : w = v
      · exact hwv.symm
      · simp only [Forward.freeze, Function.update_self, Option.some.injEq] at hut
        have htold : s.frozenAt w = some t := by simpa [Forward.freeze, hwv] using hwt
        have := (h.bounded w hw t htold).2
        omega
    · by_cases hwv : w = v
      · subst w
        simp only [Forward.freeze, Function.update_self, Option.some.injEq] at hwt
        have htold : s.frozenAt u = some t := by simpa [Forward.freeze, huv] using hut
        have := (h.bounded u hu t htold).2
        omega
      · exact h.injective u hu w hw t
          (by simpa [Forward.freeze, huv] using hut) (by simpa [Forward.freeze, hwv] using hwt)

theorem LabelsValidAt.step {n : ℕ} {s : State} (h : LabelsValidAt n s)
    (sign : Bool) (v : ℕ) : LabelsValidAt (n + 1) (step s (n + 1) sign v) := by
  unfold Forward.step
  split_ifs
  · exact h.attach v
  · exact h.freeze v
  · exact h.mono (Nat.le_succ n)

theorem run_labels_valid (x : SignSequence) (choice : ℕ → ℕ) (n : ℕ) :
    LabelsValidAt n (run x choice n) := by
  induction n with
  | zero => exact initial_labels_valid
  | succ n ih => exact ih.step _ _

theorem treeLaw_labels_valid (x : SignSequence) (n : ℕ) :
    ∀ᵐ s ∂treeLaw x n, LabelsValidAt n s := by
  apply treeLaw_ae_induction x LabelsValidAt initial_labels_valid
  · intro k s hs _; exact hs.mono (Nat.le_succ k)
  · intro k s hs v _; exact hs.step _ _

end Freezing1.Forward
