module

public import Freezing1.ForwardCutForest
public import Freezing1.ForwardTree

/-!
# The deterministic evolution of forward cut heights

Old vertices keep their cut height on attachment, a fresh child is one level
above its chosen parent, and freezing leaves all cut heights unchanged.
These are exact properties of the verified forward construction.
-/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

theorem cutHeightAux_attach_old {n : ℕ} {s : State} (hs : ValidAt n s)
    (a m p : ℕ) {v : ℕ} (hv : v ∈ s.vertices) :
    cutHeightAux (attach s (n + 1) p) a m v = cutHeightAux s a m v := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    have hne : v ≠ n + 1 := by have := hs.vertices_le v hv; omega
    change (if v ≤ a then 0 else cutHeightAux (attach s (n + 1) p) a m
      ((attach s (n + 1) p).parent v) + 1) = _
    rw [show (attach s (n + 1) p).parent v = s.parent v by simp [attach, hne]]
    simp only [cutHeightAux, ih (hs.parent_mem v hv)]

theorem cutHeight_attach_old {n : ℕ} {s : State} (hs : ValidAt n s)
    (a p : ℕ) {v : ℕ} (hv : v ∈ s.vertices) :
    cutHeight (attach s (n + 1) p) a v = cutHeight s a v := by
  have hne : v ≠ n + 1 := by have := hs.vertices_le v hv; omega
  unfold cutHeight
  rw [show (attach s (n + 1) p).height v = s.height v by simp [attach, hne]]
  exact cutHeightAux_attach_old hs a _ p hv

theorem cutHeight_attach_new {n : ℕ} {s : State} (hs : ValidAt n s)
    {a p : ℕ} (ha : a ≤ n) (hp : p ∈ s.active) :
    cutHeight (attach s (n + 1) p) a (n + 1) = cutHeight s a p + 1 := by
  have hnot : ¬n + 1 ≤ a := by omega
  unfold cutHeight
  rw [show (attach s (n + 1) p).height (n + 1) = s.height p + 1 by simp [attach]]
  simp only [cutHeightAux, ite_eq_right hnot]
  rw [show (attach s (n + 1) p).parent (n + 1) = p by simp [attach]]
  rw [cutHeightAux_attach_old hs a _ p (hs.active_subset hp)]

theorem cutHeightAux_freeze (s : State) (t p a m v : ℕ) :
    cutHeightAux (freeze s t p) a m v = cutHeightAux s a m v := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    change (if v ≤ a then 0 else cutHeightAux (freeze s t p) a m (s.parent v) + 1) = _
    simp only [cutHeightAux, ih]

theorem cutHeight_freeze (s : State) (t p a v : ℕ) :
    cutHeight (freeze s t p) a v = cutHeight s a v :=
  cutHeightAux_freeze s t p a _ v

end Freezing1.Forward
