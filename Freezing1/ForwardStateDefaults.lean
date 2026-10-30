module

public import Freezing1.ForwardLaw

/-!
# Canonical defaults in forward states

The construction fixes the parent's value at the root and all data outside
the finite vertex set. These facts allow full state equality when comparing
canonical representations, without silently dropping unused function values.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory

structure CanonicalDefaults (s : State) : Prop where
  parent_zero : s.parent 0 = 0
  outside : ∀ v, v ∉ s.vertices → s.parent v = 0 ∧ s.height v = 0 ∧ s.frozenAt v = none

theorem initial_canonical_defaults : CanonicalDefaults initial := by
  constructor <;> simp [initial]

theorem CanonicalDefaults.attach {s : State} (h : CanonicalDefaults s) (n v : ℕ) :
    CanonicalDefaults (attach s (n + 1) v) := by
  constructor
  · simpa [Forward.attach] using h.parent_zero
  · intro u hu
    have hune : u ≠ n + 1 := by
      intro he
      apply hu
      simp [Forward.attach, he]
    have huo : u ∉ s.vertices := fun hmem => hu (Finset.mem_insert_of_mem hmem)
    simpa [Forward.attach, hune] using h.outside u huo

theorem CanonicalDefaults.freeze {s : State} (h : CanonicalDefaults s) (t : ℕ)
    {v : ℕ} (hv : v ∈ s.vertices) : CanonicalDefaults (freeze s t v) := by
  constructor
  · exact h.parent_zero
  · intro u hu
    have huv : u ≠ v := by intro he; exact hu (he ▸ hv)
    simpa [Forward.freeze, huv] using h.outside u hu

theorem CanonicalDefaults.step {n : ℕ} {s : State} (h : CanonicalDefaults s)
    (hs : ValidAt n s) (sign : Bool) (v : ℕ) :
    CanonicalDefaults (step s (n + 1) sign v) := by
  unfold Forward.step
  split_ifs with hv
  · exact h.attach n v
  · exact h.freeze _ (hs.active_subset hv)
  · exact h

/-- Canonical defaults hold for the actual random state at every time, including
after extinction when the state is absorbing. -/
theorem treeLaw_canonical_defaults (x : SignSequence) (n : ℕ) :
    ∀ᵐ s ∂treeLaw x n, CanonicalDefaults s := by
  have h := treeLaw_ae_induction x (fun n s => ValidAt n s ∧ CanonicalDefaults s)
    ⟨initial_valid, initial_canonical_defaults⟩
    (fun k s hs _ => ⟨hs.1.mono (Nat.le_succ k), hs.2⟩)
    (fun k s hs v _ => ⟨hs.1.step _ _, hs.2.step hs.1 _ _⟩) n
  exact h.mono fun _ hs => hs.2

end Freezing1.Forward
