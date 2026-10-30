module

public import Freezing1.SIRSusceptibleConcentration
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uniform relative noise after a diverging early cutoff

The bound holds at every later integer time, without a fluid horizon or an
assumption on the infection rate. Summing the actual exponential tails gives
one geometric series, which is small whenever the cutoff tends to infinity.
-/

@[expose] public section

namespace Freezing1.SIR.Susceptible

open Filter Set MeasureTheory
open scoped ENNReal NNReal Topology Classical

noncomputable def relativeNoiseRatio (eps : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-eps ^ 2 / 2))

theorem relativeNoiseRatio_lt_one {eps : ℝ} (heps : 0 < eps) :
    relativeNoiseRatio eps < 1 := by
  rw [relativeNoiseRatio, ENNReal.ofReal_lt_one, Real.exp_lt_one_iff]
  nlinarith [sq_pos_of_pos heps]

theorem noise_relative_tail (rate : ℝ≥0) (n L : ℕ) {eps : ℝ} (heps : 0 < eps) :
    fullLaw rate n {H | ∃ k ≥ L, eps * (k : ℝ) ≤ |noise rate n H k|} ≤
      2 * relativeNoiseRatio eps ^ L * (1 - relativeNoiseRatio eps)⁻¹ := by
  have htail (k : ℕ) :
      fullLaw rate n {H | eps * (k : ℝ) ≤ |noise rate n H k|} ≤
        2 * relativeNoiseRatio eps ^ k := by
    have hh := noise_abs_tail rate n k heps (eps * (k : ℝ))
    convert hh using 1
    congr 1
    rw [relativeNoiseRatio, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 1
    ring_nf
  have he : {H : ℕ → ℕ | ∃ k ≥ L, eps * (k : ℝ) ≤ |noise rate n H k|} =
      ⋃ j : ℕ, {H | eps * ((L + j : ℕ) : ℝ) ≤ |noise rate n H (L + j)|} := by
    ext H
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨k, hk, hh⟩
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      exact ⟨j, hh⟩
    · rintro ⟨j, hh⟩
      exact ⟨L + j, by omega, hh⟩
  rw [he]
  calc
    _ ≤ ∑' j : ℕ, fullLaw rate n
        {H | eps * ((L + j : ℕ) : ℝ) ≤ |noise rate n H (L + j)|} := measure_iUnion_le _
    _ ≤ ∑' j : ℕ, 2 * relativeNoiseRatio eps ^ (L + j) :=
      ENNReal.tsum_le_tsum fun j => htail (L + j)
    _ = _ := by
      simp_rw [pow_add, ← mul_assoc]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

theorem noise_relative_tendsto (rate : ℕ → ℝ≥0) (cutoff : ℕ → ℕ)
    (hcutoff : Tendsto cutoff atTop atTop) {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n : ℕ => fullLaw (rate n) n
      {H | ∃ k ≥ cutoff n, eps * (k : ℝ) ≤ |noise (rate n) n H k|}) atTop (𝓝 0) := by
  have hratio := relativeNoiseRatio_lt_one heps
  have hden : (1 - relativeNoiseRatio eps)⁻¹ ≠ (∞ : ℝ≥0∞) := by
    exact ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr hratio))
  have hp := (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hratio).comp hcutoff
  have ht := (ENNReal.Tendsto.const_mul hp (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ∞)))
  have hh := ENNReal.Tendsto.mul_const ht (Or.inr hden)
  have hb : Tendsto (fun n : ℕ => 2 * relativeNoiseRatio eps ^ cutoff n *
      (1 - relativeNoiseRatio eps)⁻¹) atTop (𝓝 0) := by simpa using hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ => bot_le) (fun n => noise_relative_tail (rate n) n (cutoff n) heps)

end Freezing1.SIR.Susceptible
