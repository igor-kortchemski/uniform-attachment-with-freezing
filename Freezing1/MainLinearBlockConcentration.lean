module

public import Freezing1.LinearBlockVariance
public import Freezing1.MainLinearBlockCount

/-!
# Reverse-history counterpart of Lemma Forestier

The mean lower bound and variance upper bound both concern the same actual
random root count on the coherent reverse history. Chebyshev then gives the
source's reciprocal-block failure probability. The forward time-cut count is
identified separately by the timestamp-preserving history reconstruction.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical Topology

/-- The source's constants 5 and 4 leave a full block-size deviation. -/
theorem probability_below_four_le_of_mean_variance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {a L : ℝ} (ha : 0 < a) (hmean : 5 * a ≤ ∫ ω, X ω ∂μ)
    (hvar : variance X μ ≤ L * a) :
    μ.real {ω | X ω ≤ 4 * a} ≤ L / a := by
  have hcheb := meas_ge_le_variance_div_sq hX ha
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg X μ) (sq_nonneg a))] at hreal
  calc
    _ ≤ μ.real {ω | a ≤ |X ω - ∫ ω', X ω' ∂μ|} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      change X ω ≤ 4 * a at hω
      have hh : a ≤ -(X ω - ∫ ω', X ω' ∂μ) := by linarith
      exact hh.trans (neg_le_abs _)
    _ ≤ variance X μ / a ^ 2 := hreal
    _ ≤ (L * a) / a ^ 2 := div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ = _ := by field_simp [ha.ne']

/-- Actual reverse count, the source geometric window, and its `L/C^k`
failure probability. The extra size condition on C is retained for chaining. -/
theorem exists_geometricBlock_fewTallRoots_probability
    (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : LinearRegimeParameter)
    (hn : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n))
    (hA : Tendsto A atTop atTop) (hnear : NearOriginLinear x A (c : ℝ))
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℕ, 1 < C ∧
      (((c : ℝ) + 1) / (2 * (c : ℝ))) * (linearHeightFactor c - η) ≤ Real.log (C : ℝ) ∧
      ∃ L : ℝ, 0 < L ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
        ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) → ((C ^ k : ℕ) : ℝ) ≤ ε * n / C →
          (ReverseHistory.fullLaw (x n) n).real
            {H | (ReverseHistory.blockTallRootCount (C ^ k) (C ^ (k + 1))
              ((linearPoissonRate c C : ℝ) * (linearHeightFactor c - η)) H : ℝ) ≤
                4 * ((C ^ k : ℕ) : ℝ)} ≤ L / ((C ^ k : ℕ) : ℝ) := by
  obtain ⟨C, hC, hsize, εE, hεE, hεE1, hmean⟩ :=
    exists_geometricBlock_tallRoot_expectation_lower x A c hn hA hnear hη
  obtain ⟨L, hL, εV, hεV, hεV1, hvar⟩ :=
    uniform_geometricBlock_variance_le x A c.property.1 hn hA hnear C hC.le
  let ε := min εE εV
  have hε : 0 < ε := lt_min hεE hεV
  have hε1 : ε < 1 := (min_le_left _ _).trans_lt hεE1
  refine ⟨C, hC, hsize, L, hL, ε, hε, hε1, ?_⟩
  filter_upwards [hmean, hvar] with n hmeann hvarn
  intro k hAk hupper
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hpow : (0 : ℝ) < (C ^ k : ℕ) := by exact_mod_cast pow_pos (show 0 < C by omega) k
  have hupperE : ((C ^ k : ℕ) : ℝ) ≤ εE * n / C := hupper.trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n)) hC0.le)
  have hupperV : ((C ^ k * C : ℕ) : ℝ) ≤ εV * n := by
    rw [Nat.cast_mul]
    calc
      ((C ^ k : ℕ) : ℝ) * C ≤ (ε * n / C) * C :=
        mul_le_mul_of_nonneg_right hupper hC0.le
      _ = ε * n := div_mul_cancel₀ _ hC0.ne'
      _ ≤ εV * n := mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg n)
  have hbn : C ^ k * C ≤ n := geometricBlock_le_horizon hεV1.le hupperV
  have hbn' : C ^ (k + 1) ≤ n := by simpa only [pow_succ] using hbn
  have hvar' : variance
      (fun H => (ReverseHistory.blockTallRootCount (C ^ k) (C ^ (k + 1))
        ((linearPoissonRate c C : ℝ) * (linearHeightFactor c - η)) H : ℝ))
      (ReverseHistory.fullLaw (x n) n) ≤ L * ((C ^ k : ℕ) : ℝ) := by
    rw [pow_succ]
    exact hvarn (C ^ k) hbn hAk hupperV _
  exact probability_below_four_le_of_mean_variance
    (ReverseHistory.blockTallRootCount_memLp (x n) n (hn n) hbn' _ 2)
    hpow (hmeann k hAk hupperE) hvar'

/-- Literal near-origin assumption for Lemma Forestier, on the actual reverse
history. Other global linear-regime assumptions are not needed locally. -/
theorem linear_geometricBlock_fewTallRoots_probability
    (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : LinearRegimeParameter)
    (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A (c : ℝ)) {η : ℝ} (hη : 0 < η) (_hη1 : η < 1) :
    ∃ C : ℕ, 1 < C ∧ ∃ L : ℝ, 0 < L ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
      ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) → ((C ^ k : ℕ) : ℝ) ≤ ε * n / C →
        (ReverseHistory.fullLaw (x n) n).real
          {H | (ReverseHistory.blockTallRootCount (C ^ k) (C ^ (k + 1))
            ((((c : ℝ) + 1) / (2 * (c : ℝ))) * Real.log (C : ℝ) *
              (linearHeightFactor c - η)) H : ℝ) ≤ 4 * ((C ^ k : ℕ) : ℝ)} ≤
            L / ((C ^ k : ℕ) : ℝ) := by
  have hs : ∀ n, PositiveThrough (x n) n :=
    fun n => (lt_extinctionTime_iff (x n) n).mp (hτ n)
  have hp := (nearOriginLimsup_iff x A hA c.property.1.le c.property.2 hs).mp hnear
  obtain ⟨C, hC, _hsize, L, hL, ε, hε, hε1, he⟩ :=
    exists_geometricBlock_fewTallRoots_probability x A c (fun n => (hτ n).le) hAinf hp hη
  exact ⟨C, hC, L, hL, ε, hε, hε1, he⟩

end Freezing1
