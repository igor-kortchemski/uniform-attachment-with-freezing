module

public import Freezing1.ForwardComponentPopulation
public import Freezing1.ForwardCutForest

/-! The cut-height increment is exactly the height of the later cut root. -/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

theorem cutHeight_eq_parent_add {n : ℕ} {s : State} (hs : ValidAt n s)
    {a v : ℕ} (hv : v ∈ s.vertices) (hav : a < v) :
    cutHeight s a v = cutHeight s a (s.parent v) + 1 := by
  have hv0 : v ≠ 0 := by omega
  unfold cutHeight
  rw [hs.height_parent v hv hv0]
  simp only [cutHeightAux, ite_eq_right (Nat.not_le.mpr hav)]

theorem cutAncestor_eq_parent {n : ℕ} {s : State} (hs : ValidAt n s)
    {a v : ℕ} (hv : v ∈ s.vertices) (hav : a < v) :
    cutAncestor s a v = cutAncestor s a (s.parent v) := by
  have hv0 : v ≠ 0 := by omega
  unfold cutAncestor
  rw [hs.height_parent v hv hv0]
  simp only [cutAncestorAux, ite_eq_right (Nat.not_le.mpr hav)]

theorem cutHeight_decompose_at_ancestor {n : ℕ} {s : State} (hs : ValidAt n s)
    {a b : ℕ} (hab : a ≤ b) {v : ℕ} (hv : v ∈ s.vertices) :
    cutHeight s a v = cutHeight s b v + cutHeight s a (cutAncestor s b v) := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
    by_cases hvb : v ≤ b
    · rw [cutAncestor_of_le s b v hvb,
        show cutHeight s b v = 0 from cutHeightAux_eq_zero_of_le s b _ v hvb, zero_add]
    · have hbv : b < v := Nat.lt_of_not_ge hvb
      have hv0 : v ≠ 0 := by omega
      have hp := hs.parent_mem v hv
      have hpl := hs.parent_lt v hv hv0
      rw [cutHeight_eq_parent_add hs hv (hab.trans_lt hbv), cutHeight_eq_parent_add hs hv hbv,
        cutAncestor_eq_parent hs hv hbv, ih _ hpl hp]
      omega

/-- The source's H_{a,b}(v) is the height in the first cut forest of the
root of v's component in the second cut forest. -/
theorem blockHeight_eq_cutHeight_ancestor {n : ℕ} {s : State} (hs : ValidAt n s)
    {a b : ℕ} (hab : a ≤ b) {v : ℕ} (hv : v ∈ s.vertices) :
    blockHeight s a b v = cutHeight s a (cutAncestor s b v) := by
  unfold blockHeight
  rw [cutHeight_decompose_at_ancestor hs hab hv, Nat.add_sub_cancel_left]

end Freezing1.Forward
