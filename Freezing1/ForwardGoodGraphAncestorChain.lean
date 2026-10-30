module

public import Freezing1.ForwardCutAncestorPath
public import Freezing1.ForwardTerminalGoodPredicate

/-! Source A49: a good vertex supplies an actual graph-ancestor chain. -/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

/-- Every good endpoint has explicitly quantified historical ancestors.
Successive vertices are related by actual parent iterates, and their
ordinary graph distances exceed the block threshold. -/
theorem HistoryShape.good_graph_ancestor_chain {x : SignSequence} {n : ℕ} {s : State}
    (hs : HistoryShape x n s) (C : ℕ) (hC : 1 ≤ C) (k₀ k : ℕ) (hk : k₀ ≤ k)
    (t : ℝ) {v : ℕ} (hv : v ∈ goodSet (truncateAt s (C ^ k)) C k₀ k t) :
    ∃ V : ℕ → ℕ, V k = v ∧
      (∀ i ∈ Finset.Icc k₀ k, V i ∈ (truncateAt s (C ^ i)).active) ∧
      (∀ i ∈ Finset.Ico k₀ k,
        ∃ d : ℕ, (s.parent^[d]) (V (i + 1)) = V i ∧
          t < (s.graph.dist (V i) (V (i + 1)) : ℝ)) ∧
      ((k - k₀ : ℕ) : ℝ) * t ≤ (s.height v : ℝ) := by
  have hcurrent : ValidAt n s := by
    simpa only [hs.prefix_self] using (hs.prefix_phaseData (Nat.le_refl n)).valid
  have hvActive := goodSet_subset _ _ _ _ _ hv
  obtain ⟨hvV, hvk, _⟩ := (mem_historical_active s (C ^ k) v).mp hvActive
  refine ⟨fun i => cutAncestor s (C ^ i) v, cutAncestor_of_le s (C ^ k) v hvk, ?_, ?_, ?_⟩
  · intro i hi
    have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
    exact hs.cutAncestor_historically_active (pow_le_pow_right₀ hC hik) hvActive
  · intro i hi
    have hib : i + 1 ≤ k := by have := Finset.mem_Ico.mp hi; omega
    have hab : C ^ i ≤ C ^ (i + 1) := pow_le_pow_right₀ hC (Nat.le_succ i)
    have hwV := (hcurrent.cutAncestor_path_data (C ^ (i + 1)) hvV).1
    have hcomp := hcurrent.cutAncestor_comp hab hvV
    obtain ⟨_, _, hiter, _, _⟩ := hcurrent.cutAncestor_path_data (C ^ i) hwV
    refine ⟨cutHeight s (C ^ i) (cutAncestor s (C ^ (i + 1)) v), hiter.trans hcomp, ?_⟩
    have hd := hcurrent.dist_cutAncestor_eq_cutHeight (C ^ i) hwV
    rw [hcomp] at hd
    rw [hd, ← blockHeight_eq_cutHeight_ancestor hcurrent hab hvV]
    have htest := (Finset.mem_filter.mp hv).2 i hi
    rwa [blockHeight_truncateAt hcurrent _ _ _ hvV hvk] at htest
  · have hh := goodSet_height_lower (truncateAt s (C ^ k)) C hC k₀ k hk t hv
    rw [show (truncateAt s (C ^ k)).height v = s.height v by simp [truncateAt, hvk]] at hh
    exact hh

/-- Actual-process graph chain with no additional ancestry or geometric
coupling premise. The chain is read inside one terminal realization. -/
theorem treeLaw_good_graph_ancestor_chain (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (C : ℕ) (hC : 1 ≤ C)
    (k₀ k : ℕ) (hk : k₀ ≤ k) (t : ℝ) :
    ∀ᵐ s ∂treeLaw x n, ∀ v ∈ goodSet (truncateAt s (C ^ k)) C k₀ k t,
      ∃ V : ℕ → ℕ, V k = v ∧
        (∀ i ∈ Finset.Icc k₀ k, V i ∈ (truncateAt s (C ^ i)).active) ∧
        (∀ i ∈ Finset.Ico k₀ k,
          ∃ d : ℕ, (s.parent^[d]) (V (i + 1)) = V i ∧
            t < (s.graph.dist (V i) (V (i + 1)) : ℝ)) ∧
        ((k - k₀ : ℕ) : ℝ) * t ≤ (s.height v : ℝ) := by
  filter_upwards [treeLaw_historyShape x n hn] with s hs v hv
  exact hs.good_graph_ancestor_chain C hC k₀ k hk t hv

end Freezing1.Forward
