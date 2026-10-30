module

public import Freezing1.SignedUrnPositiveExtensionMaximal
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Scalar conversion of the source infinite-urn maximal bound. The
quadratic exponential rate and cubic marked-root threshold are explicit. -/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory
open scoped Topology BigOperators Classical

set_option backward.isDefEq.respectTransparency false

theorem source_urn_exponent_lower {a s D E K k : ℝ}
    (ha : 1 ≤ a) (hs : 0 < s) (hsa : s ≤ a + 1) (hK : 0 < K)
    (hD : 0 < D) (hDK : D ≤ K / a) (hEK : E ≤ K / a) (hk : 1 ≤ k) :
    k ^ 2 / (16 * K) ≤ ((k ^ 4 / 4) * s⁻¹) / (D + k ^ 2 * max D E) := by
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a + 1 := by linarith
  have hk0 : 0 < k := by linarith
  have hkp : 0 < 1 + k ^ 2 := by positivity
  have hmax0 : 0 < max D E := hD.trans_le (le_max_left _ _)
  have hden : 0 < D + k ^ 2 * max D E := by positivity
  have hmax : max D E ≤ K / a := max_le hDK hEK
  have hdenup : D + k ^ 2 * max D E ≤ (K / a) * (1 + k ^ 2) := by
    have hh := mul_le_mul_of_nonneg_left hmax (sq_nonneg k)
    nlinarith
  have hi : 1 / (a + 1) ≤ 1 / s := one_div_le_one_div_of_le hs hsa
  have hnum : (k ^ 4 / 4) * (1 / (a + 1)) ≤ (k ^ 4 / 4) * s⁻¹ := by
    simpa only [one_div] using mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ k ^ 4 / 4)
  have hgeom : k ^ 2 * (1 + k ^ 2) * (a + 1) ≤ 4 * a * k ^ 4 := by
    have hk2 : 1 + k ^ 2 ≤ 2 * k ^ 2 := by nlinarith
    have ha2 : a + 1 ≤ 2 * a := by linarith
    have hh := mul_le_mul hk2 ha2 (by positivity : 0 ≤ a + 1) (by positivity : 0 ≤ 2 * k ^ 2)
    have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg k)
    convert hh' using 1 <;> ring
  have hfrac : k ^ 2 / (16 * K) ≤
      (k ^ 4 / 4 * (1 / (a + 1))) / ((K / a) * (1 + k ^ 2)) := by
    have he : (k ^ 4 / 4 * (1 / (a + 1))) / ((K / a) * (1 + k ^ 2)) =
        (a * k ^ 4) / (4 * (a + 1) * K * (1 + k ^ 2)) := by field_simp
    rw [he]
    apply (div_le_div_iff₀ (by positivity : 0 < 16 * K)
      (by positivity : 0 < 4 * (a + 1) * K * (1 + k ^ 2))).mpr
    have hh := mul_le_mul_of_nonneg_left hgeom (by positivity : 0 ≤ 4 * K)
    convert hh using 1 <;> ring
  exact hfrac.trans ((div_le_div_of_nonneg_left (by positivity) hden hdenup).trans
    (div_le_div_of_nonneg_right hnum hden.le))

theorem eventually_cubic_ge_marked_threshold (R : ℝ) :
    ∀ᶠ k : ℕ in atTop, 1 ≤ k ∧ 1 + (1 + (k : ℝ) ^ 2) * R ≤ (k : ℝ) ^ 3 := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (max 1 (R + 1))] with k hk
  have hk1 : (1 : ℝ) ≤ k := (le_max_left _ _).trans hk
  have hR : R ≤ (k : ℝ) - 1 := by have hh := (le_max_right _ _).trans hk; linarith
  have hm := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 1 + (k : ℝ) ^ 2)
  refine ⟨by exact_mod_cast hk1, ?_⟩
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ k by positivity) (by linarith : 0 ≤ (k : ℝ) - 1)]

/-- The source geometric number of components is absorbed by the genuine
quadratic exponential rate from its maximal urn inequality. -/
theorem eventually_geometric_exp_square_le_inv_sq (C : ℕ) (hC : 1 ≤ C)
    {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ k : ℕ in atTop,
      (((C ^ k : ℕ) : ℝ) + 1) * (2 * Real.exp (-β * (k : ℝ) ^ 2)) ≤ 1 / (k : ℝ) ^ 2 := by
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hlin : Tendsto (fun k : ℕ => β * (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hβ
  have hsmall : Tendsto (fun k : ℕ => 4 * ((k : ℝ) ^ 2 * Real.exp (-(k : ℝ))))
      atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp tendsto_natCast_atTop_atTop).const_mul 4
  filter_upwards [eventually_ge_atTop 1, hlin.eventually_ge_atTop (Real.log C + 1),
    hsmall.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with k hk hlinK hsmallK
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hCpow : (1 : ℝ) ≤ (C : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hC)
  have hpoweq : (C : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log C) := by
    rw [Real.exp_nat_mul, Real.exp_log hC0]
  have hexponent : (k : ℝ) * Real.log C - β * (k : ℝ) ^ 2 ≤ -(k : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hlinK hk0.le
    nlinarith
  calc
    _ ≤ 4 * ((C : ℝ) ^ k * Real.exp (-β * (k : ℝ) ^ 2)) := by
      rw [Nat.cast_pow]
      nlinarith [Real.exp_pos (-β * (k : ℝ) ^ 2)]
    _ = 4 * Real.exp ((k : ℝ) * Real.log C - β * (k : ℝ) ^ 2) := by
      rw [hpoweq, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 4 * Real.exp (-(k : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num)
    _ ≤ 1 / (k : ℝ) ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hk0)).mpr
      nlinarith

namespace SignedUrn

theorem positiveExtension_square_budget_pos (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : PositiveThrough x b) :
    0 < infiniteSquareBudget (positiveExtensionPopulation x a b) := by
  have hs := positiveExtension_square_summable x hab hb
  apply hs.tsum_pos (fun _ => sq_nonneg _) 0
  have hz : 0 < (positiveExtensionPopulation x a b 1 : ℝ) := by
    exact_mod_cast positiveExtensionPopulation_positive x (a := a) hb 1
  exact sq_pos_of_pos (inv_pos.mpr hz)

end SignedUrn
end Freezing1
