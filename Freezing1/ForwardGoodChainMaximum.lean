module

public import Freezing1.ForwardGoodChains
public import Freezing1.ForwardTruncationLaw
public import Freezing1.ForwardMaximum

/-!
# A surviving good chain gives a lower bound for the final maximum

The chain lives in a canonical prefix of the actual terminal state. Its
accumulated block heights bound the terminal tree height. The limiting helper
keeps survival of that real good set as an explicit, still separate input.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory Filter
open scoped Classical Topology

theorem treeHeight_truncate_le (s : State) (a : ℕ) :
    treeHeight (truncateAt s a) ≤ treeHeight s := by
  apply Finset.sup_le
  intro v hv
  change v ∈ s.vertices.filter (fun v => v ≤ a) at hv
  obtain ⟨hv, hva⟩ := Finset.mem_filter.mp hv
  simpa only [truncateAt, ite_eq_left hva] using height_le_treeHeight hv

/-- A vertex good for every block has the accumulated height in the final
state, even though its good-set test uses an earlier canonical prefix. -/
theorem nonempty_goodSet_truncate_height_lower (s : State) (a C k₀ k : ℕ)
    (hC : 1 ≤ C) (hk : k₀ ≤ k) (t : ℝ)
    (hgood : (goodSet (truncateAt s a) C k₀ k t).Nonempty) :
    ((k - k₀ : ℕ) : ℝ) * t ≤ (treeHeight s : ℝ) := by
  obtain ⟨v, hv⟩ := hgood
  have ha := goodSet_subset (truncateAt s a) C k₀ k t hv
  change v ∈ s.vertices.filter (fun v => v ≤ a ∧ ∀ j, s.frozenAt v = some j → a < j) at ha
  obtain ⟨hmem, hbound, _⟩ := Finset.mem_filter.mp ha
  have hh := goodSet_height_lower (truncateAt s a) C hC k₀ k hk t hv
  have he : (truncateAt s a).height v = s.height v := by simp only [truncateAt, ite_eq_left hbound]
  rw [he] at hh
  exact hh.trans (by exact_mod_cast height_le_treeHeight hmem)

theorem treeHeight_lower_tail_le_empty_goodSet (μ : Measure State) [IsFiniteMeasure μ]
    (a C k₀ k : ℕ) (hC : 1 ≤ C) (hk : k₀ ≤ k) (t : ℝ) :
    μ.real {s | (treeHeight s : ℝ) < ((k - k₀ : ℕ) : ℝ) * t} ≤
      μ.real {s | goodSet (truncateAt s a) C k₀ k t = ∅} := by
  apply measureReal_mono _ (measure_ne_top _ _)
  intro s hs
  by_contra hne
  have hh := nonempty_goodSet_truncate_height_lower s a C k₀ k hC hk t
    (Finset.nonempty_iff_ne_empty.mpr hne)
  exact (not_lt_of_ge hh) hs

/-- Once survival of the actual good set is proved, its deterministic
logarithmic span gives the lower maximum-height limit. -/
theorem maximum_lower_tail_of_goodChain_survival
    (x : ℕ → SignSequence) (a k₀ k : ℕ → ℕ) (C : ℕ) (hC : 1 ≤ C)
    (hk : ∀ᶠ n in atTop, k₀ n ≤ k n) (t : ℕ → ℝ) (L : ℝ)
    (hspan : Tendsto (fun n : ℕ => (((k n - k₀ n : ℕ) : ℝ) * t n) / Real.log (n : ℝ))
      atTop (𝓝 L))
    (hsurv : Tendsto (fun n => (treeLaw (x n) n).real
      {s | goodSet (truncateAt s (a n)) C (k₀ n) (k n) (t n) = ∅}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (treeLaw (x n) n).real
      {s | (treeHeight s : ℝ) / Real.log (n : ℝ) < L - ε}) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ hsurv
  filter_upwards [hk, hlog.eventually_gt_atTop 0,
    hspan.eventually (lt_mem_nhds (sub_lt_self L hε))] with n hkn hln hn
  apply measureReal_mono _ (measure_ne_top _ _)
  intro s hs
  by_contra hne
  have hh := nonempty_goodSet_truncate_height_lower s (a n) C (k₀ n) (k n) hC hkn (t n)
    (Finset.nonempty_iff_ne_empty.mpr hne)
  have hdiv := div_le_div_of_nonneg_right hh hln.le
  exact (not_lt_of_ge (hn.le.trans hdiv)) hs

end Freezing1.Forward
