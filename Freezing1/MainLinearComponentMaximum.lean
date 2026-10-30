module

public import Freezing1.LinearComponentTailBounds
public import Freezing1.ForwardComponentMaximum

/-!
# Lemma Forestjump for the actual forward time-cut forest

Each distinguished component root is counted as active, including when it
has already frozen in the original tree. Its active population is at most
the actual signed-urn population plus one. The finite endpoint moment bound
therefore proves the source's uniform reciprocal-square estimate directly.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory Filter
open scoped ENNReal Topology

/-- The genuine forward component maximum satisfies L11 uniformly over the
whole geometric window above the cutoff. -/
theorem uniform_geometric_componentMaximum_tail
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hA : Tendsto A atTop atTop) (hnear : NearOriginLinear x A c) (hbulk : BulkLowerBound x)
    (hτ : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n)) (C : ℕ) (hC : 1 ≤ C) :
    ∀ᶠ n in atTop, ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) → C ^ k * C ≤ n →
      (Forward.treeLaw (x n) (C ^ k * C)).real
        {s | (k : ℝ) ^ 3 < (Forward.componentMaximum s (C ^ k) : ℝ)} ≤ 1 / (k : ℝ) ^ 2 := by
  filter_upwards [uniform_geometric_urn_tail_union x A hc hA hnear hbulk C hC,
    hA.eventually_gt_atTop 1] with n hn hAn
  intro k hAk hbound
  have hk : 1 ≤ k := by
    by_contra h
    have he : k = 0 := by omega
    simp only [he, pow_zero, Nat.cast_one] at hAk
    linarith
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq : 0 ≤ (k : ℝ) ^ 3 - 1 := sub_nonneg.mpr (one_le_pow₀ hkR)
  have hab : C ^ k ≤ C ^ k * C := Nat.le_mul_of_pos_right _ (by omega)
  have he : C ^ k + (C ^ k * C - C ^ k) = C ^ k * C := Nat.add_sub_of_le hab
  have hcutτ : ((C ^ k + (C ^ k * C - C ^ k) : ℕ) : ℕ∞) ≤ extinctionTime (x n) := by
    rw [he]
    exact (show ((C ^ k * C : ℕ) : ℕ∞) ≤ n by exact_mod_cast hbound).trans (hτ n)
  have hmax := Forward.treeLaw_componentMaximum_tail_le (x n) (C ^ k)
    (C ^ k * C - C ^ k) hcutτ hq
  rw [he, sub_add_cancel] at hmax
  have hevent : {u : ℤ | (k : ℝ) ^ 3 - 1 < (u : ℝ)} =
      {u : ℤ | (k : ℝ) ^ 3 < (u : ℝ) + 1} := by
    ext u
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rw [hevent] at hmax
  exact hmax.trans (hn k hAk hbound)

/-- Literal linear-regime hypotheses and the paper's upper endpoint `n/C`.
The probability is taken under Algorithm 1 at time `C^(k+1)`. -/
theorem linear_geometric_componentMaximum_tail
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x)
    (C : ℕ) (hC : 2 ≤ C) :
    ∀ᶠ n in atTop, ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) →
      ((C ^ k : ℕ) : ℝ) ≤ (n : ℝ) / C →
      (Forward.treeLaw (x n) (C ^ (k + 1))).real
        {s | (k : ℝ) ^ 3 < (Forward.componentMaximum s (C ^ k) : ℝ)} ≤ 1 / (k : ℝ) ^ 2 := by
  have hs : ∀ n, PositiveThrough (x n) n := fun n =>
    (lt_extinctionTime_iff (x n) n).mp (hτ n)
  have hn := (nearOriginLimsup_iff x A hA hc.le hc1 hs).mp hnear
  have hb := (bulkLiminf_iff x hs).mp hbulk
  filter_upwards [uniform_geometric_componentMaximum_tail x A hc hAinf hn hb
    (fun n => (hτ n).le) C (by omega)] with n hn
  intro k hAk hupper
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hbn : C ^ k * C ≤ n := by
    have hh := (le_div_iff₀ hC0).mp hupper
    exact_mod_cast hh
  simpa only [pow_succ] using hn k hAk hbn

end Freezing1
