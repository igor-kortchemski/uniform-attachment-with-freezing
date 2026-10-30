module

public import Freezing1.UniformBirthBernoulli
public import Freezing1.HeightScaleBounds

/-! Exact uniform birth probabilities and negligible sublinear early births. -/

@[expose] public section

namespace Freezing1.UniformBirth

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

theorem birthLaw_lt (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    {m : ℕ} (hmn : m ≤ n) :
    (birthLaw x n).real {b | b < m} =
      ((m : ℝ) + 1 - activeCount x m) / ((n : ℝ) + 1 + activeCount x n) := by
  rw [birthLaw, Measure.real, Measure.map_apply (measurable_of_countable _) (by measurability)]
  exact uniform_birthTime_lt (le_of_lt (h n le_rfl)) hmn

theorem birthLaw_lt_le_div (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    (hn : 1 ≤ n) {m : ℕ} (hmn : m ≤ n) :
    (birthLaw x n).real {b | b < m} ≤ (m : ℝ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hSm : (1 : ℝ) ≤ activeCount x m := by
    have hh : (1 : ℤ) ≤ activeCount x m := by have := h m hmn; omega
    exact_mod_cast hh
  have hSn : (0 : ℝ) < activeCount x n := by exact_mod_cast h n le_rfl
  have hden : (0 : ℝ) < (n : ℝ) + 1 + activeCount x n := by positivity
  rw [birthLaw_lt x n h hmn]
  calc
    _ ≤ (m : ℝ) / ((n : ℝ) + 1 + activeCount x n) :=
      div_le_div_of_nonneg_right (by linarith) hden.le
    _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg m) hnR (by linarith)

theorem birthLaw_sublinear_cutoff_tendsto (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) (cutoff : ℕ → ℕ)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (nhds 0)) :
    Tendsto (fun n => (birthLaw (rows n) n).real {b | b < cutoff n}) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) ?_ hsmall
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hsmall.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with n hn hc
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcut : cutoff n ≤ n := by
    have hh := (div_lt_one hnR).mp hc
    exact_mod_cast hh.le
  exact birthLaw_lt_le_div (rows n) n (hrows n) hn hcut

theorem auxiliary_sublinear_birth_tendsto (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) (cutoff : ℕ → ℕ)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (nhds 0)) :
    Tendsto (fun n => (auxiliaryLaw (rows n) n (hrows n)).real {z | z.1 < cutoff n}) atTop (nhds 0) := by
  have hh := birthLaw_sublinear_cutoff_tendsto rows hrows cutoff hsmall
  convert hh using 1
  funext n
  exact (auxiliary_birth_hasLaw (rows n) n (hrows n)).measureReal_eq
    (p := fun b : ℕ => b < cutoff n) (by measurability)

/-- The source's high-probability birth beyond a sublogarithmic real cutoff,
with its integer rounding supplied explicitly. -/
theorem auxiliary_birth_below_sublog_tendsto (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) (A : ℕ → ℝ)
    (hA : ∀ᶠ n in atTop, 0 ≤ A n)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (nhds 0)) :
    Tendsto (fun n => (auxiliaryLaw (rows n) n (hrows n)).real {z | (z.1 : ℝ) < A n})
      atTop (nhds 0) := by
  have hh := auxiliary_sublinear_birth_tendsto rows hrows (fun n => ⌈A n⌉₊)
    (tendsto_natCutoff_div_nat_zero_of_sublog (tendsto_ceil_div_log_zero hA hsmall))
  simpa only [Nat.lt_ceil] using hh

end Freezing1.UniformBirth
