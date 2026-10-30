module

public import Freezing1.GeometricChainSourceIndices
public import Freezing1.ForwardTerminalGoodPredicate
public import Freezing1.ForwardGoodGraphAncestorChain

/-! The literal finite source cutoff, including $A_n \le 1$. -/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory
open scoped Classical ENNReal

noncomputable def positiveChainLowerIndex (C : ℕ) (A : ℕ → ℝ) (n : ℕ) : ℕ :=
  max 1 (chainLowerIndex C A n)

theorem mem_positiveChainInterval_iff_source (C : ℕ) (hC : 1 < C)
    (A : ℕ → ℝ) (n k ell : ℕ) (hA : 0 < A n) :
    ell ∈ Finset.Ico (positiveChainLowerIndex C A n) k ↔
      1 ≤ ell ∧ ell < k ∧ A n ≤ ((C ^ ell : ℕ) : ℝ) := by
  rw [Finset.mem_Ico, positiveChainLowerIndex, max_le_iff,
    chainLowerIndex_le_iff C hC A n ell hA]
  tauto

theorem eventually_positiveChainLowerIndex_eq (C : ℕ) (hC : 1 < C)
    (A : ℕ → ℝ) (hA : Tendsto A atTop atTop) :
    ∀ᶠ n in atTop, positiveChainLowerIndex C A n = chainLowerIndex C A n := by
  filter_upwards [(chainLowerIndex_tendsto_atTop C hC hA).eventually_ge_atTop 1] with n hn
  exact max_eq_right hn

namespace Forward

/-- Literal finite source definition: positive indices are imposed even
when the logarithmic ceiling is zero. -/
theorem goodSet_eq_source_filter_positiveCutoff (s : State) (C : ℕ) (hC : 1 < C)
    (A : ℕ → ℝ) (n k : ℕ) (t : ℝ) (hA : 0 < A n) :
    goodSet s C (positiveChainLowerIndex C A n) k t = s.active.filter fun v =>
      ∀ ell : ℕ, 1 ≤ ell → ell < k → A n ≤ ((C ^ ell : ℕ) : ℝ) →
        t < (blockHeight s (C ^ ell) (C ^ (ell + 1)) v : ℝ) := by
  ext v
  simp only [goodSet, Finset.mem_filter]
  apply and_congr_right
  intro _
  constructor
  · intro h ell hlo hhi hpow
    exact h ell ((mem_positiveChainInterval_iff_source C hC A n k ell hA).mpr ⟨hlo, hhi, hpow⟩)
  · intro h ell he
    obtain ⟨hlo, hhi, hpow⟩ := (mem_positiveChainInterval_iff_source C hC A n k ell hA).mp he
    exact h ell hlo hhi hpow

theorem goodSet_truncate_eq_source_filter_positiveCutoff {n : ℕ} {s : State}
    (hs : ValidAt n s) (C : ℕ) (hC : 1 < C) (A : ℕ → ℝ)
    (N k : ℕ) (t : ℝ) (hA : 0 < A N) :
    goodSet (truncateAt s (C ^ k)) C (positiveChainLowerIndex C A N) k t =
      (truncateAt s (C ^ k)).active.filter fun v =>
        ∀ ell : ℕ, 1 ≤ ell → ell < k → A N ≤ ((C ^ ell : ℕ) : ℝ) →
          t < (blockHeight s (C ^ ell) (C ^ (ell + 1)) v : ℝ) := by
  rw [goodSet_eq_source_filter_positiveCutoff _ C hC A N k t hA]
  apply Finset.filter_congr
  intro v hv
  obtain ⟨hvV, hvb, _⟩ := (mem_historical_active s (C ^ k) v).mp hv
  simp only [blockHeight_truncateAt hs _ _ _ hvV hvb]

theorem eventually_goodSet_positiveCutoff_eq (C : ℕ) (hC : 1 < C)
    (A : ℕ → ℝ) (hA : Tendsto A atTop atTop) :
    ∀ᶠ n in atTop, ∀ s k t,
      goodSet s C (positiveChainLowerIndex C A n) k t = goodSet s C (chainLowerIndex C A n) k t := by
  filter_upwards [eventually_positiveChainLowerIndex_eq C hC A hA] with n hn s k t
  rw [hn]

/-- Finite source-window graph-chain extraction, using exactly the source's
positive-index convention even for initial $A_n \le 1$. -/
theorem treeLaw_source_good_graph_chain (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (C : ℕ) (hC : 1 < C) (A : ℕ → ℝ)
    (k : ℕ) (hk : positiveChainLowerIndex C A n ≤ k) (t : ℝ) (hA : 0 < A n) :
    ∀ᵐ s ∂treeLaw x n, ∀ v ∈ (truncateAt s (C ^ k)).active,
      (∀ ell : ℕ, 1 ≤ ell → ell < k → A n ≤ ((C ^ ell : ℕ) : ℝ) →
        t < (blockHeight s (C ^ ell) (C ^ (ell + 1)) v : ℝ)) →
      ∃ V : ℕ → ℕ, V k = v ∧
        (∀ i ∈ Finset.Icc (positiveChainLowerIndex C A n) k,
          V i ∈ (truncateAt s (C ^ i)).active) ∧
        (∀ i ∈ Finset.Ico (positiveChainLowerIndex C A n) k,
          ∃ d : ℕ, (s.parent^[d]) (V (i + 1)) = V i ∧
            t < (s.graph.dist (V i) (V (i + 1)) : ℝ)) ∧
        ((k - positiveChainLowerIndex C A n : ℕ) : ℝ) * t ≤ (s.height v : ℝ) := by
  filter_upwards [treeLaw_good_graph_ancestor_chain x n hn C hC.le
    (positiveChainLowerIndex C A n) k hk t, treeLaw_valid x n] with s hs hvalid v hv htests
  apply hs v
  rw [goodSet_truncate_eq_source_filter_positiveCutoff hvalid C hC A n k t hA]
  exact Finset.mem_filter.mpr ⟨hv, htests⟩

end Forward
end Freezing1
