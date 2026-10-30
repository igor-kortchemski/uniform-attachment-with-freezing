module

public import Freezing1.ForwardInfiniteHistory
public import Freezing1.ForwardMaximum

/-! The source's height telescoping identity along an arbitrary finite chain. -/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory
open scoped Classical BigOperators ENNReal

theorem treeHeight_chain_telescopes (H : ℕ → State) (R : ℕ → ℕ) (m n : ℕ)
    (hH0 : H 0 = initial) (hR0 : R 0 = 0) (hRm : R m = n) :
    (∑ i ∈ Finset.range m,
      ((treeHeight (H (R (i + 1))) : ℝ) - treeHeight (H (R i)))) = treeHeight (H n) := by
  rw [Finset.sum_range_sub (fun i : ℕ => (treeHeight (H (R i)) : ℝ)), hRm, hR0, hH0]
  simp [treeHeight, initial]

/-- The identity holds simultaneously along every actual forward history
outside its single initial null set. Increasingness is not needed for the
telescoping algebra, so the statement also covers every source chain. -/
theorem fullLaw_treeHeight_chain_telescopes (x : SignSequence) :
    ∀ᵐ H ∂ForwardInfiniteHistory.fullLaw x, ∀ R : ℕ → ℕ, ∀ m n : ℕ,
      R 0 = 0 → R m = n →
      (∑ i ∈ Finset.range m,
        ((treeHeight (H (R (i + 1))) : ℝ) - treeHeight (H (R i)))) = treeHeight (H n) := by
  filter_upwards [ForwardInfiniteHistory.fullLaw_initial x] with H hH
  intro R m n hR0 hRm
  exact treeHeight_chain_telescopes H R m n hH hR0 hRm

end Freezing1.Forward
