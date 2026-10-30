module

public import Freezing1.LinearBlockLowerTail
public import Freezing1.ReverseHistoryBlockCount

/-!
# The reverse-history counterpart of Lemma 12

The root set at the upper endpoint is random. Its exact first-moment identity
is proved from independence of the whole block from the earlier history.
The analytic estimate then gives the paper's constant on the original
geometric window, with the strict-tail rounding repaired.

The source defines its count through Algorithm 1 and time-cut forests. The
identification of that count with this reverse-history count is a separate
timestamp-preserving reconstruction obligation; it is not asserted here.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators Classical

/-- The actual expected number of tall roots in geometric blocks is at least
`5*C^k`. The upper cutoff is exactly the paper's `C^k ≤ ε*n/C`. -/
theorem exists_geometricBlock_tallRoot_expectation_lower
    (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : LinearRegimeParameter)
    (hn : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n))
    (hA : Tendsto A atTop atTop) (hnear : NearOriginLinear x A (c : ℝ))
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℕ, 1 < C ∧
      (((c : ℝ) + 1) / (2 * (c : ℝ))) * (linearHeightFactor c - η) ≤ Real.log (C : ℝ) ∧
      ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
        ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) →
          ((C ^ k : ℕ) : ℝ) ≤ ε * n / C →
          5 * ((C ^ k : ℕ) : ℝ) ≤
            ∫ H, (ReverseHistory.blockTallRootCount (C ^ k) (C ^ (k + 1))
              ((linearPoissonRate c C : ℝ) * (linearHeightFactor c - η)) H : ℝ)
              ∂ReverseHistory.fullLaw (x n) n := by
  obtain ⟨C, hC, hsize, _hrate, ε, hε, hε1, he⟩ :=
    exists_uniform_geometricBlock_weighted_tail_lower x A c hn hA hnear hη
  refine ⟨C, hC, hsize, ε, hε, hε1, ?_⟩
  filter_upwards [he] with n hen
  intro k hAk hupper
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hbε : ((C ^ (k + 1) : ℕ) : ℝ) ≤ ε * n := by
    rw [pow_succ, Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_right hupper hC0.le).trans_eq
      (div_mul_cancel₀ _ hC0.ne')
  have hb : C ^ (k + 1) ≤ n := by
    rw [pow_succ]
    exact geometricBlock_le_horizon hε1.le (by simpa only [pow_succ] using hbε)
  have hab : C ^ k ≤ C ^ (k + 1) := by
    rw [pow_succ]
    calc
      C ^ k = C ^ k * 1 := by simp
      _ ≤ C ^ k * C := Nat.mul_le_mul_left _ (by omega)
  have hbn : C ^ k * C ≤ n := by simpa only [pow_succ] using hb
  have hab' : C ^ k ≤ C ^ k * C := by simpa only [pow_succ] using hab
  rw [pow_succ, ReverseHistory.integral_blockTallRootCount (x n) n (hn n) hab' hbn]
  have hbound := hen (C ^ k) hbn hAk (by simpa only [pow_succ] using hbε)
  have hp : blockAttachmentParameter (x n) n (hn n) (C ^ k * C) hbn =
      (fun i : Fin (C ^ k * C) => Reverse.attachmentParameter (x n) n (hn n)
        ⟨i.val, i.isLt.trans_le hbn⟩) := by
    funext i
    apply Subtype.ext
    simp only [blockAttachmentParameter_coe, Reverse.attachmentParameter_coe]
  rw [hp] at hbound
  dsimp only [blockAttachmentIndices] at hbound
  exact hbound

/-- Reverse-history counterpart of source Lemma `lem:minoration`, with its
literal near-origin nested-limit hypothesis. Its bulk and sublogarithmic
cutoff assumptions are not needed for this local block estimate. The transfer
to the forward time-cut count remains a separate reconstruction theorem. -/
theorem linear_geometricBlock_tallRoot_expectation_lower
    (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : LinearRegimeParameter)
    (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A (c : ℝ))
    {η : ℝ} (hη : 0 < η) (_hη1 : η < 1) :
    ∃ C : ℕ, 1 < C ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
      ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) →
        ((C ^ k : ℕ) : ℝ) ≤ ε * n / C →
        5 * ((C ^ k : ℕ) : ℝ) ≤
          ∫ H, (ReverseHistory.blockTallRootCount (C ^ k) (C ^ (k + 1))
            ((((c : ℝ) + 1) / (2 * (c : ℝ))) * Real.log (C : ℝ) *
              (linearHeightFactor c - η)) H : ℝ)
            ∂ReverseHistory.fullLaw (x n) n := by
  have hs : ∀ n, PositiveThrough (x n) n :=
    fun n => (lt_extinctionTime_iff (x n) n).mp (hτ n)
  have hp := (nearOriginLimsup_iff x A hA c.property.1.le c.property.2 hs).mp hnear
  obtain ⟨C, hC, _hsize, ε, hε, hε1, he⟩ :=
    exists_geometricBlock_tallRoot_expectation_lower x A c (fun n => (hτ n).le) hAinf hp hη
  exact ⟨C, hC, ε, hε, hε1, he⟩

end Freezing1
