module

public import Freezing1.BernoulliLimits
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Normalized Bernoulli moments under an arbitrary positive lower mean

The constants may depend on a fixed positive lower bound for the mean.
The closed deviation bound retains the exact Bennett rate at its threshold.
-/

@[expose] public section

namespace Freezing1

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem bernoulli_normalized_closed_deviation_le
    {Y : ι → Ω → ℝ} {p : ι → unitInterval}
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (s : Finset ι) (hm : 0 < ∑ i ∈ s, (p i : ℝ)) {eps : ℝ} (heps : 0 < eps) :
    μ.real {ω | eps ≤ |(∑ i ∈ s, Y i ω) / (∑ i ∈ s, (p i : ℝ)) - 1|} ≤
      2 * Real.exp (-(∑ i ∈ s, (p i : ℝ)) * bennettRate eps) := by
  let e : ℕ → ℝ := fun j => eps - eps / ((j : ℝ) + 2)
  have hepos (j : ℕ) : 0 < e j := by
    dsimp [e]
    apply sub_pos.mpr
    apply (div_lt_iff₀ (by positivity : 0 < (j : ℝ) + 2)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have heless (j : ℕ) : e j < eps := sub_lt_self _ (div_pos heps (by positivity))
  have ht : Tendsto e atTop (nhds eps) := by
    have hh := (tendsto_const_nhds (x := eps)).div_atTop
      (tendsto_atTop_add_const_right atTop 2 (tendsto_natCast_atTop_atTop (R := ℝ)))
    have hdiff := (tendsto_const_nhds (x := eps)).sub hh
    simpa only [sub_zero] using hdiff
  have hc : ContinuousAt bennettRate eps := by
    unfold bennettRate
    fun_prop (disch := linarith)
  have hlim := (Real.continuous_exp.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := -(∑ i ∈ s, (p i : ℝ)))).mul (hc.tendsto.comp ht))).const_mul 2
  apply ge_of_tendsto' hlim
  intro j
  exact (measureReal_mono (fun ω hω => (heless j).trans_le hω) (measure_ne_top _ _)).trans
    (bernoulli_normalized_strict_deviation_le hY hind hLaw s hm (hepos j))

omit [IsProbabilityMeasure μ] in
theorem bernoulli_lower_mean_exp_integral_le
    {Y : ι → Ω → ℝ} {p : ι → unitInterval}
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (s : Finset ι) {a : ℝ} (ha : 0 < a) (hm : a ≤ ∑ i ∈ s, (p i : ℝ))
    {theta : ℝ} (htheta : theta ≤ a) :
    (∫ ω, Real.exp (theta * ((∑ i ∈ s, Y i ω) / (∑ i ∈ s, (p i : ℝ)))) ∂μ) ≤
      Real.exp (a * (Real.exp 1 - 1)) := by
  let m : ℝ := ∑ i ∈ s, (p i : ℝ)
  have hmpos : 0 < m := ha.trans_le hm
  have ht0 : 0 ≤ a / m := div_nonneg ha.le hmpos.le
  have ht1 : a / m ≤ 1 := (div_le_one hmpos).mpr hm
  have hc := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
    (sub_nonneg.mpr ht1) ht0 (sub_add_cancel 1 (a / m))
  have he : Real.exp (a / m) ≤ 1 + a / m * (Real.exp 1 - 1) := by
    have hh : Real.exp (a / m) ≤ (1 - a / m) * 1 + (a / m) * Real.exp 1 := by
      simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] using hc
    nlinarith
  calc
    _ = mgf (∑ i ∈ s, Y i) μ (theta / m) := by
      simp only [mgf, Finset.sum_apply, div_mul_eq_mul_div, mul_div_assoc, m]
    _ ≤ Real.exp (m * (Real.exp (theta / m) - 1)) := mgf_sum_bernoulli_le hY hind hLaw s _
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hmono := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right htheta hmpos.le)
      have hh : Real.exp (theta / m) - 1 ≤ a / m * (Real.exp 1 - 1) := by linarith
      have hmul := mul_le_mul_of_nonneg_left hh hmpos.le
      have heq : m * (a / m * (Real.exp 1 - 1)) = a * (Real.exp 1 - 1) := by field_simp
      exact hmul.trans_eq heq

theorem bernoulli_centered_exp_integrable
    {Y : ι → Ω → ℝ} {p : ι → unitInterval}
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (s : Finset ι) (theta : ℝ) :
    Integrable (fun ω => Real.exp (theta *
      ((∑ i ∈ s, Y i ω) / (∑ i ∈ s, (p i : ℝ)) - 1))) μ := by
  have hh := (bernoulli_normalized_exp_integrable hY hind hLaw s theta).const_mul (Real.exp (-theta))
  have he (ω : Ω) : Real.exp (theta * ((∑ i ∈ s, Y i ω) / (∑ i ∈ s, (p i : ℝ)) - 1)) =
      Real.exp (-theta) * Real.exp (theta * ((∑ i ∈ s, Y i ω) / (∑ i ∈ s, (p i : ℝ)))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [he] using hh

theorem bernoulli_centered_lower_mean_moment_le
    {Y : ι → Ω → ℝ} {p : ι → unitInterval}
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (s : Finset ι) {a : ℝ} (ha : 0 < a) (hm : a ≤ ∑ i ∈ s, (p i : ℝ))
    {q : ℝ} (hq : 0 ≤ q) :
    (∫ ω, |(∑ i ∈ s, Y i ω) / (∑ i ∈ s, (p i : ℝ)) - 1| ^ q ∂μ) ≤
      2 * (q / a) ^ q * Real.exp (a * Real.exp 1) := by
  let Z : Ω → ℝ := fun ω => (∑ i ∈ s, Y i ω) / (∑ i ∈ s, (p i : ℝ)) - 1
  have hpos : Integrable (fun ω => Real.exp (a * Z ω)) μ :=
    bernoulli_centered_exp_integrable hY hind hLaw s a
  have hneg : Integrable (fun ω => Real.exp (-a * Z ω)) μ :=
    bernoulli_centered_exp_integrable hY hind hLaw s (-a)
  have hpow : Integrable (fun ω => |Z ω| ^ q) μ :=
    integrable_rpow_abs_of_integrable_exp_mul ha.ne' hpos hneg hq
  have hbound : ∀ ω, |Z ω| ^ q ≤ (q / a) ^ q *
      (Real.exp (a * Z ω) + Real.exp (-a * Z ω)) := by
    intro ω
    exact (rpow_abs_le_mul_max_exp_of_pos (Z ω) hq ha).trans
      (mul_le_mul_of_nonneg_left
        (max_le (le_add_of_nonneg_right (Real.exp_pos _).le) (le_add_of_nonneg_left (Real.exp_pos _).le))
        (Real.rpow_nonneg (div_nonneg hq ha.le) _))
  have hexp {theta : ℝ} (ht1 : theta ≤ a) (ht2 : -theta ≤ a) :
      (∫ ω, Real.exp (theta * Z ω) ∂μ) ≤ Real.exp (a * Real.exp 1) := by
    have he (ω : Ω) : Real.exp (theta * Z ω) = Real.exp (-theta) *
        Real.exp (theta * ((∑ i ∈ s, Y i ω) / (∑ i ∈ s, (p i : ℝ)))) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [Z]
      ring
    simp_rw [he]
    rw [integral_const_mul]
    calc
      _ ≤ Real.exp (-theta) * Real.exp (a * (Real.exp 1 - 1)) :=
        mul_le_mul_of_nonneg_left (bernoulli_lower_mean_exp_integral_le hY hind hLaw s ha hm ht1)
          (Real.exp_pos _).le
      _ ≤ Real.exp a * Real.exp (a * (Real.exp 1 - 1)) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ht2) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hu := hexp le_rfl (by linarith : -a ≤ a)
  have hd := hexp (by linarith : -a ≤ a) (by simp)
  calc
    _ ≤ ∫ ω, (q / a) ^ q * (Real.exp (a * Z ω) + Real.exp (-a * Z ω)) ∂μ :=
      integral_mono hpow ((hpos.add hneg).const_mul _) hbound
    _ = (q / a) ^ q * ((∫ ω, Real.exp (a * Z ω) ∂μ) + ∫ ω, Real.exp (-a * Z ω) ∂μ) := by
      rw [integral_const_mul, integral_add hpos hneg]
    _ ≤ _ := by nlinarith [Real.rpow_nonneg (div_nonneg hq ha.le) q]

end Freezing1
