module

public import Freezing1.SignedUrnConcentration
public import Freezing1.CoalescenceLogScale
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform endpoint tails for components in a linear population schedule

A fixed positive exponential moment of the actual signed urn is bounded
uniformly over geometric blocks. The extra root convention is retained as
`U+1`. This finite endpoint argument does not claim the running supremum in L13.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators

noncomputable def linearUrnBudget (d : ℝ) : ℝ := 1 + d⁻¹ + (d ^ 2)⁻¹
noncomputable def linearUrnExponent (d C : ℝ) : ℝ := 1 / (4 * linearUrnBudget d * (C + 1))
noncomputable def linearUrnMoment (d : ℝ) : ℝ := 5 / (16 * linearUrnBudget d * d)

theorem linearUrnBudget_pos {d : ℝ} (hd : 0 < d) : 0 < linearUrnBudget d := by
  unfold linearUrnBudget
  positivity

theorem linearUrnExponent_pos {d C : ℝ} (hd : 0 < d) (hC : 0 ≤ C) :
    0 < linearUrnExponent d C := by
  unfold linearUrnExponent
  have := linearUrnBudget_pos hd
  positivity

theorem squareBudget_le_of_linear_lower (Z : ℕ → ℤ) {a k : ℕ}
    (ha : 0 < a) {d : ℝ} (hd : 0 < d)
    (hwalk : ∀ i ∈ Finset.Ioc a (a + k), d * i ≤ (Z i : ℝ)) :
    SignedUrn.squareBudget Z a k ≤ (d ^ 2)⁻¹ / a := by
  calc
    _ ≤ ∑ i ∈ Finset.Ioc a (a + k), (d ^ 2)⁻¹ * ((i : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro i hi
      have hi0 : (0 : ℝ) < i := by exact_mod_cast (ha.trans (Finset.mem_Ioc.mp hi).1)
      have hZi := (mul_pos hd hi0).trans_le (hwalk i hi)
      have hinv := one_div_le_one_div_of_le (mul_pos hd hi0) (hwalk i hi)
      simp only [one_div] at hinv
      calc
        _ ≤ ((d * (i : ℝ))⁻¹) ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr hZi.le) hinv 2
        _ = _ := by simp only [mul_inv, mul_pow, inv_pow]
    _ = (d ^ 2)⁻¹ * ∑ i ∈ Finset.Ioc a (a + k), ((i : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (d ^ 2)⁻¹ * ((a : ℝ)⁻¹ - ((a + k : ℕ) : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub ha.ne' (Nat.le_add_right a k)) (by positivity)
    _ ≤ (d ^ 2)⁻¹ * (a : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity)
    _ = _ := by rw [div_eq_mul_inv]

/-- A genuine positive exponential moment of the endpoint marked population.
Only linear lower bounds along the finite block and its final size are used. -/
theorem continuationLaw_exp_le_of_linear_lower (Z : ℕ → ℤ) {a k : ℕ}
    (ha : 0 < a) {d C : ℝ} (hd : 0 < d) (hC : 0 ≤ C)
    (hwalk : ∀ i ∈ Finset.Icc a (a + k), d * i ≤ (Z i : ℝ))
    (hz : ∀ i ∈ Finset.Ico a (a + k), Z (i + 1) - Z i = 1 ∨ Z (i + 1) - Z i = -1)
    (hend : (Z (a + k) : ℝ) ≤ (C + 1) * a) :
    (∫ v, Real.exp (linearUrnExponent d C * (v : ℝ))
      ∂SignedUrn.continuationLaw Z a k 1) ≤ Real.exp (linearUrnMoment d) := by
  let Q := linearUrnBudget d
  let θ : ℝ := a / (4 * Q)
  have hQ : 0 < Q := linearUrnBudget_pos hd
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hθ : 0 < θ := div_pos haR (by positivity)
  have hQ1 : d⁻¹ ≤ Q := by
    dsimp [Q, linearUrnBudget]
    linarith [inv_nonneg.mpr (sq_nonneg d)]
  have hQ2 : (d ^ 2)⁻¹ ≤ Q := by
    dsimp [Q, linearUrnBudget]
    linarith [inv_nonneg.mpr hd.le]
  have hZ : ∀ i ∈ Finset.Icc a (a + k), 0 < Z i := by
    intro i hi
    have hi0 : (0 : ℝ) < i := haR.trans_le (by exact_mod_cast (Finset.mem_Icc.mp hi).1)
    exact_mod_cast (mul_pos hd hi0).trans_le (hwalk i hi)
  have hZa : (0 : ℝ) < Z a := by exact_mod_cast hZ a (by simp)
  have hZb : (0 : ℝ) < Z (a + k) := by exact_mod_cast hZ (a + k) (by simp)
  have huZ : (1 : ℤ) ≤ Z a := hZ a (by simp)
  have hratio (i : ℕ) (hi : i ∈ Finset.Icc a (a + k)) :
      θ / (Z i : ℝ) ≤ 1 / (4 * Q * d) := by
    calc
      _ ≤ θ / (d * a) := div_le_div_of_nonneg_left hθ.le (mul_pos hd haR)
        ((mul_le_mul_of_nonneg_left (by exact_mod_cast (Finset.mem_Icc.mp hi).1) hd.le).trans (hwalk i hi))
      _ = _ := by dsimp [θ]; field_simp
  have hquarter : 1 / (4 * Q * d) ≤ 1 / 4 := by
    have hmul := mul_le_mul_of_nonneg_right hQ1 hd.le
    have hcancel : d⁻¹ * d = 1 := inv_mul_cancel₀ hd.ne'
    rw [hcancel] at hmul
    apply (div_le_iff₀ (by positivity : 0 < 4 * Q * d)).mpr
    nlinarith
  have hbudget : |θ| * SignedUrn.squareBudget Z a k ≤ 1 / 4 := by
    rw [abs_of_pos hθ]
    calc
      _ ≤ θ * ((d ^ 2)⁻¹ / a) := mul_le_mul_of_nonneg_left
        (squareBudget_le_of_linear_lower Z ha hd (fun i hi => hwalk i
          (Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp hi).1.le, (Finset.mem_Ioc.mp hi).2⟩))) hθ.le
      _ = (d ^ 2)⁻¹ / (4 * Q) := by dsimp [θ]; field_simp
      _ ≤ 1 / 4 := by apply (div_le_iff₀ (by positivity : 0 < 4 * Q)).mpr; linarith
  have hinc : ∀ i ∈ Finset.Ioc a (a + k), |θ / (Z i : ℝ)| ≤ 1 / 4 := by
    intro i hi
    have hic : i ∈ Finset.Icc a (a + k) :=
      Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp hi).1.le, (Finset.mem_Ioc.mp hi).2⟩
    rw [abs_of_nonneg (div_nonneg hθ.le (by exact_mod_cast (hZ i hic).le))]
    exact (hratio i hic).trans hquarter
  have hβ : linearUrnExponent d C ≤ θ / (Z (a + k) : ℝ) := by
    calc
      _ = θ / ((C + 1) * a) := by
        unfold linearUrnExponent
        dsimp [θ, Q]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_left hθ.le hZb hend
  have hB : θ * SignedUrn.squareBudget Z a k ≤ 1 / 4 := by
    simpa only [abs_of_pos hθ] using hbudget
  calc
    _ ≤ ∫ v, Real.exp (θ * ((v : ℝ) / Z (a + k)))
        ∂SignedUrn.continuationLaw Z a k 1 := by
      apply integral_mono_ae (SignedUrn.continuationLaw_integrable Z a k 1 _)
        (SignedUrn.continuationLaw_integrable Z a k 1 _)
      filter_upwards [SignedUrn.continuationLaw_valid Z hZ hz (by norm_num) huZ] with v hv
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hβ (show (0 : ℝ) ≤ v by exact_mod_cast hv.1)
      convert hh using 1
      ring
    _ ≤ Real.exp ((θ * (1 + θ * SignedUrn.squareBudget Z a k)) * ((1 : ℤ) / (Z a : ℝ))) :=
      SignedUrn.continuationLaw_exponential_le Z hZ hz (by norm_num) huZ hbudget hinc
    _ ≤ Real.exp (linearUrnMoment d) := by
      apply Real.exp_le_exp.mpr
      have hr := hratio a (by simp)
      have hnonneg : 0 ≤ 1 + θ * SignedUrn.squareBudget Z a k := by
        have := SignedUrn.squareBudget_nonneg Z a k
        positivity
      calc
        _ = (θ / (Z a : ℝ)) * (1 + θ * SignedUrn.squareBudget Z a k) := by push_cast; ring
        _ ≤ (1 / (4 * Q * d)) * (5 / 4) :=
          mul_le_mul hr (by linarith) hnonneg (by positivity)
        _ = _ := by unfold linearUrnMoment; dsimp [Q]; ring

end Freezing1
