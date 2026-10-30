module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

/-!
# Infection probabilities in the embedded SIR chain

The rate is allowed to depend arbitrarily on the population size. The
finite-prefix estimates retain this dependence instead of replacing it by
an asymptotically equivalent rate inside an exact drift identity.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false

noncomputable def infectionFraction (x : ℝ) : ℝ := x / (1 + x)

theorem infectionFraction_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ infectionFraction x := by
  exact div_nonneg hx (by linarith)

theorem infectionFraction_le_one {x : ℝ} (hx : 0 ≤ x) : infectionFraction x ≤ 1 := by
  apply (div_le_one₀ (by linarith : 0 < 1 + x)).mpr
  linarith

theorem infectionFraction_lt_one {x : ℝ} (hx : 0 ≤ x) : infectionFraction x < 1 := by
  apply (div_lt_one (by linarith : 0 < 1 + x)).mpr
  linarith

theorem infectionFraction_complement {x : ℝ} (hx : 0 ≤ x) :
    1 - infectionFraction x = 1 / (1 + x) := by
  unfold infectionFraction
  field_simp
  ring

theorem infectionFraction_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    infectionFraction x ≤ infectionFraction y := by
  have hy : 0 ≤ y := hx.trans hxy
  apply (div_le_div_iff₀ (by linarith : 0 < 1 + x) (by linarith : 0 < 1 + y)).mpr
  nlinarith

theorem infectionFraction_sub {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    infectionFraction x - infectionFraction y = (x - y) / ((1 + x) * (1 + y)) := by
  unfold infectionFraction
  field_simp
  ring

/-- The scalar function used in the SIR drift is 1-Lipschitz on nonnegative reals. -/
theorem infectionFraction_abs_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |infectionFraction x - infectionFraction y| ≤ |x - y| := by
  rw [infectionFraction_sub hx hy, abs_div, abs_of_pos (by positivity : 0 < (1+x)*(1+y))]
  have hd : 1 ≤ (1 + x) * (1 + y) := by nlinarith
  exact div_le_self (abs_nonneg _) hd

noncomputable def infectionProbability (rate : NNReal) (u : ℕ) : unitInterval :=
  ⟨infectionFraction ((rate : ℝ) * u),
    infectionFraction_nonneg (by positivity), infectionFraction_le_one (by positivity)⟩

theorem infectionProbability_coe (rate : NNReal) (u : ℕ) :
    (infectionProbability rate u : ℝ) = (rate : ℝ) * u / (1 + (rate : ℝ) * u) := rfl

theorem infectionProbability_complement (rate : NNReal) (u : ℕ) :
    1 - (infectionProbability rate u : ℝ) = 1 / (1 + (rate : ℝ) * u) :=
  infectionFraction_complement (by positivity)

@[simp] theorem infectionProbability_zero_susceptible (rate : NNReal) :
    infectionProbability rate 0 = 0 := by
  apply Subtype.ext
  simp [infectionProbability, infectionFraction]

@[simp] theorem infectionProbability_zero_rate (u : ℕ) :
    infectionProbability 0 u = 0 := by
  apply Subtype.ext
  simp [infectionProbability, infectionFraction]

theorem infectionProbability_lt_one (rate : NNReal) (u : ℕ) :
    (infectionProbability rate u : ℝ) < 1 := infectionFraction_lt_one (by positivity)

theorem infectionProbability_pos {rate : NNReal} {u : ℕ}
    (hr : 0 < rate) (hu : 0 < u) : 0 < (infectionProbability rate u : ℝ) := by
  rw [infectionProbability_coe]
  apply div_pos
  · exact mul_pos (by exact_mod_cast hr) (by exact_mod_cast hu)
  · positivity

theorem infectionProbability_mono_susceptible (rate : NNReal) {u v : ℕ} (huv : u ≤ v) :
    infectionProbability rate u ≤ infectionProbability rate v := by
  apply infectionFraction_mono (by positivity)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast huv) rate.property

theorem infectionProbability_mono_rate {r s : NNReal} (hrs : r ≤ s) (u : ℕ) :
    infectionProbability r u ≤ infectionProbability s u := by
  apply infectionFraction_mono (by positivity)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hrs) (Nat.cast_nonneg _)

theorem infectionProbability_le_rate_mul (rate : NNReal) (u : ℕ) :
    (infectionProbability rate u : ℝ) ≤ (rate : ℝ) * u := by
  apply div_le_self (by positivity)
  have : 0 ≤ (rate : ℝ) * u := by positivity
  linarith

theorem infectionProbability_abs_sub_le (rate : NNReal) {u n : ℕ} (hu : u ≤ n) :
    |(infectionProbability rate u : ℝ) - infectionProbability rate n| ≤
      (rate : ℝ) * (n - u : ℕ) := by
  have h := infectionFraction_abs_sub_le
    (x := (rate : ℝ) * u) (y := (rate : ℝ) * n) (by positivity) (by positivity)
  apply h.trans_eq
  have hsub : (rate : ℝ) * u - (rate : ℝ) * n ≤ 0 := by
    have hcast : (u : ℝ) ≤ n := by exact_mod_cast hu
    nlinarith [rate.property]
  rw [abs_of_nonpos hsub, Nat.cast_sub hu]
  ring

theorem infectionProbability_sandwich (rate : NNReal) {n k u : ℕ}
    (hlo : n - k ≤ u) (hhi : u ≤ n) :
    infectionProbability rate (n-k) ≤ infectionProbability rate u ∧
      infectionProbability rate u ≤ infectionProbability rate n :=
  ⟨infectionProbability_mono_susceptible rate hlo,
    infectionProbability_mono_susceptible rate hhi⟩

theorem infectionProbability_prefix_lower_bound (rate : NNReal) {n k u : ℕ}
    (hlo : n-k ≤ u) (hhi : u ≤ n) :
    (rate : ℝ) * (n-k : ℕ) / (1 + (rate : ℝ) * n) ≤ infectionProbability rate u := by
  rw [infectionProbability_coe]
  have hnum : (rate : ℝ) * (n-k : ℕ) ≤ (rate : ℝ) * u :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hlo) rate.property
  have hden : 1 + (rate : ℝ) * u ≤ 1 + (rate : ℝ) * n := by
    have := mul_le_mul_of_nonneg_left (show (u : ℝ) ≤ n by exact_mod_cast hhi) rate.property
    exact add_le_add (le_refl (1 : ℝ)) this
  exact (div_le_div_of_nonneg_right hnum (by positivity)).trans
    (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)

theorem rate_tendsto_zero_of_scaled_tendsto (rate : ℕ → NNReal) {l : ℝ}
    (hl : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 l)) :
    Tendsto (fun n => (rate n : ℝ)) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh := hl.mul hi
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem infectionProbability_full_tendsto (rate : ℕ → NNReal) {l : ℝ} (hl0 : 0 ≤ l)
    (hl : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 l)) :
    Tendsto (fun n => (infectionProbability (rate n) n : ℝ)) atTop
      (𝓝 (l / (1 + l))) := by
  have hh := hl.div (tendsto_const_nhds.add hl) (by linarith : 1 + l ≠ 0)
  convert hh using 1
  funext n
  simp only [infectionProbability_coe, Pi.div_apply]
  ring

/-- Uniform convergence on every fixed early prefix of the population chain. -/
theorem infectionProbability_prefix_tendsto (rate : ℕ → NNReal) {l : ℝ} (hl0 : 0 ≤ l)
    (hl : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 l))
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ u : ℕ, n-k ≤ u → u ≤ n →
      |(infectionProbability (rate n) u : ℝ) - l / (1 + l)| < ε := by
  have hp := infectionProbability_full_tendsto rate hl0 hl
  have hr := (rate_tendsto_zero_of_scaled_tendsto rate hl).mul_const (k : ℝ)
  simp only [zero_mul] at hr
  have hep := (Metric.tendsto_nhds.mp hp) (ε/2) (half_pos hε)
  have her := (tendsto_order.mp hr).2 (ε/2) (half_pos hε)
  filter_upwards [hep, her] with n hn hrate
  intro u hlo hhi
  have hnk : n-u ≤ k := by omega
  have hbound := infectionProbability_abs_sub_le (rate n) hhi
  have hsmall : |(infectionProbability (rate n) u : ℝ) - infectionProbability (rate n) n| < ε/2 :=
    hbound.trans_lt ((mul_le_mul_of_nonneg_left (by exact_mod_cast hnk)
      (rate n).property).trans_lt hrate)
  rw [Real.dist_eq] at hn
  have ht := abs_sub_le (infectionProbability (rate n) u : ℝ)
    (infectionProbability (rate n) n : ℝ) (l/(1+l))
  linarith

/-- The same early-prefix statement when infection dominates recovery. -/
theorem infectionProbability_prefix_tendsto_one (rate : ℕ → NNReal)
    (hl : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ u : ℕ, n-k ≤ u → u ≤ n →
      |(infectionProbability (rate n) u : ℝ) - 1| < ε := by
  have hh : Tendsto (fun n : ℕ => ((n : ℝ) * rate n) * (1/2 : ℝ)) atTop atTop :=
    hl.atTop_mul_const (by norm_num)
  have hd : Tendsto (fun n : ℕ => 1 + (n : ℝ) * rate n / 2) atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) hh
    linarith
  have hz : Tendsto (fun n : ℕ => 1 / (1 + (n : ℝ) * rate n / 2)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hd
  have he := (tendsto_order.mp hz).2 ε hε
  filter_upwards [he, eventually_ge_atTop (2*k)] with n hn hnk
  intro u hlo hhi
  have hhalf : (n : ℝ) / 2 ≤ u := by
    have : n ≤ 2*u := by omega
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    simpa only [mul_comm] using (show (n : ℝ) ≤ 2 * (u : ℝ) by exact_mod_cast this)
  have hm : (n : ℝ) * rate n / 2 ≤ (rate n : ℝ) * u := by
    have := mul_le_mul_of_nonneg_left hhalf (rate n).property
    nlinarith
  have hcomp := infectionProbability_complement (rate n) u
  have hp1 := (infectionProbability (rate n) u).property.2
  rw [abs_of_nonpos (by linarith), neg_sub, hcomp]
  apply lt_of_le_of_lt ?_ hn
  apply one_div_le_one_div_of_le (by positivity)
  linarith

end Freezing1.SIR
