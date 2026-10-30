module

public import Freezing1.ForwardPrefixEvents
public import Freezing1.ForwardGoodChainStep
public import Freezing1.ForwardCutTruncation

/-!
# Joint failure probabilities for the actual sequence of good sets

The two block exceptions are bounded unconditionally. On their complement,
the actual continuation estimate is integrated over the earlier tree. This
avoids a conditioning denominator and does not assume block independence.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem treeLaw_blockTallCount_cdf_prefix (x : SignSequence) {n a b : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hb : b ≤ n) (t r : ℝ) :
    (treeLaw x b).real {s | (blockTallCount s a b t : ℝ) ≤ r} =
      (treeLaw x n).real {s | (blockTallCount s a b t : ℝ) ≤ r} := by
  rw [← treeLaw_prefix_event_real x hn hb (fun s => (blockTallCount s a b t : ℝ) ≤ r)]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [treeLaw_phaseData x n hn] with s hs
  simp only [blockTallCount_truncateAt hs.valid a b t]

/-- The precise joint one-step failure bound needed for a summable chain. -/
theorem treeLaw_goodChain_step_le (x : SignSequence) {n C k₀ k : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hb : C ^ (k + 1) ≤ n) (ha : (3 : ℝ) ≤ (C ^ k : ℕ))
    (t : ℝ) {b M : ℝ} (hbpos : 0 < b) (hM : 0 ≤ M) :
    (treeLaw x n).real {s |
      b ≤ ((goodSet (truncateAt s (C ^ k)) C k₀ k t).card : ℝ) ∧
      ((goodSet (truncateAt s (C ^ (k + 1))) C k₀ (k + 1) t).card : ℝ) < 2 * b} ≤
      (treeLaw x n).real {s |
        (blockTallCount s (C ^ k) (C ^ (k + 1)) t : ℝ) ≤ 4 * (C ^ k : ℕ)} +
      (treeLaw x (C ^ (k + 1))).real {s | M < (componentMaximum s (C ^ k) : ℝ)} +
      3 * M / b := by
  have hab : C ^ k ≤ C ^ (k + 1) := pow_le_pow_right₀ hC (Nat.le_succ k)
  have hτ : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast hb : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ n).trans hn
  let Nbad : Set State := {s |
    (blockTallCount (truncateAt s (C ^ (k + 1))) (C ^ k) (C ^ (k + 1)) t : ℝ) ≤
      4 * (C ^ k : ℕ)}
  let Mbad : Set State := {s |
    M < (componentMaximum (truncateAt s (C ^ (k + 1))) (C ^ k) : ℝ)}
  let P : State → State → Prop := fun s q =>
    b ≤ ((goodSet s C k₀ k t).card : ℝ) ∧
    4 * (C ^ k : ℕ) ≤ (blockTallCount q (C ^ k) (C ^ (k + 1)) t : ℝ) ∧
    (componentMaximum q (C ^ k) : ℝ) ≤ M ∧
    ((goodSet q C k₀ (k + 1) t).card : ℝ) < 2 * b
  have hcond : ∀ s, HasHistory x (C ^ k) s →
      (continuationLaw x (C ^ k) (C ^ (k + 1) - C ^ k) s).real {q | P s q} ≤ 3 * M / b := by
    intro s hs
    by_cases hg : b ≤ ((goodSet s C k₀ k t).card : ℝ)
    · have h := continuationLaw_goodSet_growth_failure_le hs hC hk hτ ha t hbpos hM hg
      simpa only [P, hg, true_and] using h
    · have he : {q | P s q} = ∅ := by ext q; simp [P, hg]
      rw [he, measureReal_empty]
      positivity
  have hP := treeLaw_two_prefix_event_le x hn hab hb P
    (show 0 ≤ 3 * M / b by positivity) hcond
  have hsub : {s | b ≤ ((goodSet (truncateAt s (C ^ k)) C k₀ k t).card : ℝ) ∧
      ((goodSet (truncateAt s (C ^ (k + 1))) C k₀ (k + 1) t).card : ℝ) < 2 * b} ⊆
      (Nbad ∪ Mbad) ∪ {s | P (truncateAt s (C ^ k)) (truncateAt s (C ^ (k + 1)))} := by
    intro s hs
    by_cases hN : s ∈ Nbad
    · exact Or.inl (Or.inl hN)
    by_cases hM' : s ∈ Mbad
    · exact Or.inl (Or.inr hM')
    exact Or.inr ⟨hs.1, (not_le.mp hN).le, not_lt.mp hM', hs.2⟩
  calc
    _ ≤ (treeLaw x n).real ((Nbad ∪ Mbad) ∪
        {s | P (truncateAt s (C ^ k)) (truncateAt s (C ^ (k + 1)))}) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ((treeLaw x n).real Nbad + (treeLaw x n).real Mbad) + 3 * M / b :=
      (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) hP)
    _ = _ := by
      dsimp only [Nbad, Mbad]
      rw [treeLaw_prefix_event_real x hn hb (fun s =>
        (blockTallCount s (C ^ k) (C ^ (k + 1)) t : ℝ) ≤ 4 * (C ^ k : ℕ)),
        treeLaw_prefix_event_real x hn hb (fun s => M < (componentMaximum s (C ^ k) : ℝ)),
        treeLaw_blockTallCount_cdf_prefix x hn hb t]

end Freezing1.Forward
