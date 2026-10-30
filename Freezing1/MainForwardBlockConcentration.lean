module

public import Freezing1.ForwardBlockCountLaw
public import Freezing1.MainLinearBlockConcentration

/-!
# The source forward block-count estimates

The forward count uses the actual terminal tree, its time-cut forests and
their graph heights. Equality in law with the coherent reverse count transfers
the first-moment estimate and Lemma Forestier without an extra hypothesis.
The covariance proof uses killed kernel products instead of the source's
auxiliary coupling; the subsequent grafting argument is separate.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical Topology

theorem forward_blockTallCount_identDistrib (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n)
    (t : ℝ) :
    IdentDistrib (fun s => (Forward.blockTallCount s a b t : ℝ))
      (fun H => (ReverseHistory.blockTallRootCount a b t H : ℝ))
      (Forward.treeLaw x n) (ReverseHistory.fullLaw x n) := by
  have h : IdentDistrib (fun s => Forward.blockTallCount s a b t)
      (ReverseHistory.blockTallRootCount a b t)
      (Forward.treeLaw x n) (ReverseHistory.fullLaw x n) :=
    ⟨measurable_from_top.aemeasurable, measurable_from_top.aemeasurable,
      ReverseStampedHistory.forward_blockTallCount_law x n hn hab hb t⟩
  exact h.comp (show Measurable (fun j : ℕ => (j : ℝ)) from measurable_from_top)

theorem integral_forward_blockTallCount (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n)
    (t : ℝ) :
    (∫ s, (Forward.blockTallCount s a b t : ℝ) ∂Forward.treeLaw x n) =
      ∫ H, (ReverseHistory.blockTallRootCount a b t H : ℝ)
        ∂ReverseHistory.fullLaw x n :=
  (forward_blockTallCount_identDistrib x n hn hab hb t).integral_eq

theorem forward_blockTallCount_cdf_eq (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n)
    (t r : ℝ) :
    (Forward.treeLaw x n).real {s | (Forward.blockTallCount s a b t : ℝ) ≤ r} =
      (ReverseHistory.fullLaw x n).real
        {H | (ReverseHistory.blockTallRootCount a b t H : ℝ) ≤ r} := by
  exact congrArg ENNReal.toReal
    ((forward_blockTallCount_identDistrib x n hn hab hb t).measure_mem_eq measurableSet_Iic)

theorem geometricBlock_window_bounds {C k n : ℕ} (hC : 1 < C) {ε : ℝ}
    (hε : ε ≤ 1) (hupper : ((C ^ k : ℕ) : ℝ) ≤ ε * n / C) :
    C ^ k ≤ C ^ (k + 1) ∧ C ^ (k + 1) ≤ n := by
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hbε : ((C ^ k * C : ℕ) : ℝ) ≤ ε * n := by
    rw [Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_right hupper hC0.le).trans_eq
      (div_mul_cancel₀ _ hC0.ne')
  constructor
  · rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ (by omega)
  · simpa only [pow_succ] using geometricBlock_le_horizon hε hbε

/-- Lemma 12 for the actual forward time-cut forest, retaining the size
condition on the geometric ratio needed by the later chaining argument. -/
theorem exists_forward_geometricBlock_expectation_lower
    (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : LinearRegimeParameter)
    (hn : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n))
    (hA : Tendsto A atTop atTop) (hnear : NearOriginLinear x A (c : ℝ))
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℕ, 1 < C ∧
      (((c : ℝ) + 1) / (2 * (c : ℝ))) * (linearHeightFactor c - η) ≤ Real.log (C : ℝ) ∧
      ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
        ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) → ((C ^ k : ℕ) : ℝ) ≤ ε * n / C →
          5 * ((C ^ k : ℕ) : ℝ) ≤
            ∫ s, (Forward.blockTallCount s (C ^ k) (C ^ (k + 1))
              ((linearPoissonRate c C : ℝ) * (linearHeightFactor c - η)) : ℝ)
              ∂Forward.treeLaw (x n) n := by
  obtain ⟨C, hC, hsize, ε, hε, hε1, he⟩ :=
    exists_geometricBlock_tallRoot_expectation_lower x A c hn hA hnear hη
  refine ⟨C, hC, hsize, ε, hε, hε1, ?_⟩
  filter_upwards [he] with n hen
  intro k hAk hupper
  obtain ⟨hab, hb⟩ := geometricBlock_window_bounds hC hε1.le hupper
  rw [integral_forward_blockTallCount (x n) n (hn n) hab hb]
  exact hen k hAk hupper

/-- Lemma Forestier for the actual forward time-cut forest. -/
theorem exists_forward_geometricBlock_fewTallRoots_probability
    (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : LinearRegimeParameter)
    (hn : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n))
    (hA : Tendsto A atTop atTop) (hnear : NearOriginLinear x A (c : ℝ))
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℕ, 1 < C ∧
      (((c : ℝ) + 1) / (2 * (c : ℝ))) * (linearHeightFactor c - η) ≤ Real.log (C : ℝ) ∧
      ∃ L : ℝ, 0 < L ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
        ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) → ((C ^ k : ℕ) : ℝ) ≤ ε * n / C →
          (Forward.treeLaw (x n) n).real
            {s | (Forward.blockTallCount s (C ^ k) (C ^ (k + 1))
              ((linearPoissonRate c C : ℝ) * (linearHeightFactor c - η)) : ℝ) ≤
                4 * ((C ^ k : ℕ) : ℝ)} ≤ L / ((C ^ k : ℕ) : ℝ) := by
  obtain ⟨C, hC, hsize, L, hL, ε, hε, hε1, he⟩ :=
    exists_geometricBlock_fewTallRoots_probability x A c hn hA hnear hη
  refine ⟨C, hC, hsize, L, hL, ε, hε, hε1, ?_⟩
  filter_upwards [he] with n hen
  intro k hAk hupper
  obtain ⟨hab, hb⟩ := geometricBlock_window_bounds hC hε1.le hupper
  rw [forward_blockTallCount_cdf_eq (x n) n (hn n) hab hb]
  exact hen k hAk hupper

/-- Source near-origin hypothesis and literal forward count in Lemma 12. -/
theorem linear_forward_geometricBlock_expectation_lower
    (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : LinearRegimeParameter)
    (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A (c : ℝ)) {η : ℝ} (hη : 0 < η) (_hη1 : η < 1) :
    ∃ C : ℕ, 1 < C ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
      ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) → ((C ^ k : ℕ) : ℝ) ≤ ε * n / C →
        5 * ((C ^ k : ℕ) : ℝ) ≤
          ∫ s, (Forward.blockTallCount s (C ^ k) (C ^ (k + 1))
            ((((c : ℝ) + 1) / (2 * (c : ℝ))) * Real.log (C : ℝ) *
              (linearHeightFactor c - η)) : ℝ) ∂Forward.treeLaw (x n) n := by
  have hs : ∀ n, PositiveThrough (x n) n :=
    fun n => (lt_extinctionTime_iff (x n) n).mp (hτ n)
  have hp := (nearOriginLimsup_iff x A hA c.property.1.le c.property.2 hs).mp hnear
  obtain ⟨C, hC, _hsize, ε, hε, hε1, he⟩ :=
    exists_forward_geometricBlock_expectation_lower x A c (fun n => (hτ n).le) hAinf hp hη
  exact ⟨C, hC, ε, hε, hε1, he⟩

/-- Source near-origin hypothesis and literal forward count in Lemma Forestier. -/
theorem linear_forward_geometricBlock_fewTallRoots_probability
    (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : LinearRegimeParameter)
    (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A (c : ℝ)) {η : ℝ} (hη : 0 < η) (_hη1 : η < 1) :
    ∃ C : ℕ, 1 < C ∧ ∃ L : ℝ, 0 < L ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
      ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) → ((C ^ k : ℕ) : ℝ) ≤ ε * n / C →
        (Forward.treeLaw (x n) n).real
          {s | (Forward.blockTallCount s (C ^ k) (C ^ (k + 1))
            ((((c : ℝ) + 1) / (2 * (c : ℝ))) * Real.log (C : ℝ) *
              (linearHeightFactor c - η)) : ℝ) ≤ 4 * ((C ^ k : ℕ) : ℝ)} ≤
            L / ((C ^ k : ℕ) : ℝ) := by
  have hs : ∀ n, PositiveThrough (x n) n :=
    fun n => (lt_extinctionTime_iff (x n) n).mp (hτ n)
  have hp := (nearOriginLimsup_iff x A hA c.property.1.le c.property.2 hs).mp hnear
  obtain ⟨C, hC, _hsize, L, hL, ε, hε, hε1, he⟩ :=
    exists_forward_geometricBlock_fewTallRoots_probability x A c
      (fun n => (hτ n).le) hAinf hp hη
  exact ⟨C, hC, L, hL, ε, hε, hε1, he⟩

end Freezing1
