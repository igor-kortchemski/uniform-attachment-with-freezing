module

public import Freezing1.MainMaximum
public import Freezing1.MainLinearHeightScale

/-!
# The upper maximum-height bound in the linear regime

The actual forward tree law satisfies the upper half of Theorem `thm:lineaire`
(III) once its deterministic height scale has the limit in part (I).
The finite bound keeps the `n+1` factor and the one-edge shift; both disappear
only in the proved asymptotic passage. The lower bound is a separate obligation.
-/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory
open scoped Topology ENNReal

set_option backward.isDefEq.respectTransparency false

theorem tendsto_atTop_of_div_log_pos {h : ℕ → ℝ} {K : ℝ} (hK : 0 < K)
    (hh : Tendsto (fun n : ℕ => h n / Real.log (n : ℝ)) atTop (𝓝 K)) :
    Tendsto h atTop atTop := by
  have hl : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply (hh.pos_mul_atTop hK hl).congr'
  filter_upwards [hl.eventually_gt_atTop 0] with n hn
  exact div_mul_cancel₀ _ hn.ne'

/-- A rate strictly above the logarithmic union threshold dominates `n+1`. -/
theorem tendsto_nat_succ_mul_exp_neg_of_linear_scale {h : ℕ → ℝ} {K a : ℝ}
    (_hK : 0 < K)
    (hh : Tendsto (fun n : ℕ => h n / Real.log (n : ℝ)) atTop (𝓝 K))
    (ha : 1 < K * a) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.exp (-h n * a)) atTop (𝓝 0) := by
  let b : ℝ := (K * a + 1) / 2
  have hb : 1 < b := by dsimp [b]; linarith
  have hba : b < K * a := by dsimp [b]; linarith
  have hl : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun n : ℕ => 2 * Real.exp (-(b - 1) * Real.log (n : ℝ)))
      atTop (𝓝 0) := by
    have hx := Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (hl.const_mul_atTop (by linarith : 0 < b - 1)))
    change Tendsto (fun n : ℕ => Real.exp (-((b - 1) * Real.log (n : ℝ))))
      atTop (𝓝 0) at hx
    simpa only [neg_mul, mul_zero] using hx.const_mul 2
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ he
  filter_upwards [eventually_ge_atTop 2,
    (hh.mul_const a).eventually (lt_mem_nhds hba)] with n hn hlarge
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hbound : b * Real.log (n : ℝ) ≤ h n * a := by
    rw [div_mul_eq_mul_div] at hlarge
    exact ((lt_div_iff₀ hlog).mp hlarge).le
  calc
    ((n : ℝ) + 1) * Real.exp (-h n * a) ≤
        (2 * n) * Real.exp (-h n * a) := by gcongr; linarith
    _ = 2 * Real.exp (Real.log (n : ℝ) - h n * a) := by
      rw [Real.exp_sub, Real.exp_log hn0, neg_mul, Real.exp_neg]
      ring
    _ ≤ 2 * Real.exp (-(b - 1) * Real.log (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      nlinarith

/-- A fixed positive margin absorbs the one-edge shift in the finite tail. -/
theorem tendsto_shifted_bennett_upper_of_linear_scale {h : ℕ → ℝ} {K u ε : ℝ}
    (hK : 0 < K)
    (hh : Tendsto (fun n : ℕ => h n / Real.log (n : ℝ)) atTop (𝓝 K))
    (hu : 0 ≤ u) (hε : 0 < ε)
    (hrate : 1 < K * bennettRate (u + ε / 2)) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      Real.exp (-h n * bennettRate (u + ε - 1 / h n))) atTop (𝓝 0) := by
  have hd := tendsto_atTop_of_div_log_pos hK hh
  have hb := tendsto_nat_succ_mul_exp_neg_of_linear_scale hK hh hrate
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hb
  filter_upwards [hd.eventually_gt_atTop 0, hd.eventually_ge_atTop (2 / ε)] with n hn hne
  have hs : 1 / h n ≤ ε / 2 := by
    apply (div_le_iff₀ hn).mpr
    have hm := (div_le_iff₀ hε).mp hne
    nlinarith
  have hle : u + ε / 2 ≤ u + ε - 1 / h n := by linarith
  have hg := strictMonoOn_bennettRate.monotoneOn
    (by linarith : 0 ≤ u + ε / 2) (by linarith : 0 ≤ u + ε - 1 / h n) hle
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The actual maximum divided by the height scale is asymptotically no larger
than the uniquely specified linear-regime factor. -/
theorem linear_maximum_over_scale_upper_tendsto_zero (c : LinearRegimeParameter)
    (x : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hscale : Tendsto (fun n : ℕ => heightScale (x n) n / Real.log (n : ℝ))
      atTop (𝓝 (((c : ℝ) + 1) / (2 * (c : ℝ))))) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Forward.treeLaw (x n) n).real
      {s | linearHeightFactor c + ε < (Forward.treeHeight s : ℝ) / heightScale (x n) n})
      atTop (𝓝 0) := by
  let K : ℝ := ((c : ℝ) + 1) / (2 * (c : ℝ))
  have hc : 0 < (c : ℝ) := c.property.1
  have hK : 0 < K := by dsimp [K]; positivity
  have hf := one_lt_linearHeightFactor c
  have hrate : 1 < K * bennettRate (linearHeightFactor c - 1 + ε / 2) := by
    have hb := mul_lt_mul_of_pos_left (bennettRate_linearHeightFactor_add c (half_pos hε)) hK
    have hid : K * (2 * (c : ℝ) / ((c : ℝ) + 1)) = 1 := by dsimp [K]; field_simp
    rwa [hid] at hb
  have hd := tendsto_atTop_of_div_log_pos hK hscale
  have hlim := tendsto_shifted_bennett_upper_of_linear_scale hK hscale
    (show 0 ≤ linearHeightFactor c - 1 by linarith) hε hrate
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ hlim
  have hp : 0 < linearHeightFactor c - 1 + ε := by linarith
  filter_upwards [eventually_ge_atTop 1,
    hd.eventually_gt_atTop (1 / (linearHeightFactor c - 1 + ε))] with n hn hlarge
  have ht : 0 < (linearHeightFactor c - 1 + ε) * heightScale (x n) n - 1 := by
    have hh := (div_lt_iff₀ hp).mp hlarge
    nlinarith
  have hb := normalized_treeHeight_upper_tail (x n) n hn (hτ n) ht
  simpa only [show 1 + (linearHeightFactor c - 1 + ε) = linearHeightFactor c + ε by ring] using hb

/-- The upper half of Theorem `thm:lineaire` (III), for the actual forward tree.
Only the deterministic limit from part (I) is required in addition to survival. -/
theorem linear_maximum_over_log_upper_tendsto_zero (c : LinearRegimeParameter)
    (x : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hscale : Tendsto (fun n : ℕ => heightScale (x n) n / Real.log (n : ℝ))
      atTop (𝓝 (((c : ℝ) + 1) / (2 * (c : ℝ))))) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => (Forward.treeLaw (x n) n).real
      {s | (((c : ℝ) + 1) / (2 * (c : ℝ))) * linearHeightFactor c + η <
        (Forward.treeHeight s : ℝ) / Real.log (n : ℝ)}) atTop (𝓝 0) := by
  let K : ℝ := ((c : ℝ) + 1) / (2 * (c : ℝ))
  let ε : ℝ := η / (2 * K)
  have hc : 0 < (c : ℝ) := c.property.1
  have hK : 0 < K := by dsimp [K]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hr : K * (linearHeightFactor c + ε) < K * linearHeightFactor c + η := by
    dsimp [ε]
    field_simp
    nlinarith
  have he := (hscale.mul_const (linearHeightFactor c + ε)).eventually (gt_mem_nhds hr)
  have hd := tendsto_atTop_of_div_log_pos hK hscale
  have hb := linear_maximum_over_scale_upper_tendsto_zero c x hτ hscale hε
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ hb
  filter_upwards [he, hd.eventually_gt_atTop 0, eventually_ge_atTop 2] with n hn hhn hn2
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro s hs
  change K * linearHeightFactor c + η < (Forward.treeHeight s : ℝ) / Real.log (n : ℝ) at hs
  change linearHeightFactor c + ε < (Forward.treeHeight s : ℝ) / heightScale (x n) n
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  rw [div_mul_eq_mul_div] at hn
  have h1 := (div_lt_iff₀ hlog).mp hn
  have h2 := (lt_div_iff₀ hlog).mp hs
  apply (lt_div_iff₀ hhn).mpr
  nlinarith

/-- The exact upper-tail conclusion under the Introduction's original
linear-regime assumptions, with part (I) discharged by its proved theorem. -/
theorem linear_maximum_upper_tendsto_zero (c : LinearRegimeParameter)
    (x : ℕ → SignSequence) (A : ℕ → ℝ)
    (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A (c : ℝ)) (hbulk : BulkLiminf x)
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => (Forward.treeLaw (x n) n).real
      {s | (((c : ℝ) + 1) / (2 * (c : ℝ))) * linearHeightFactor c + η <
        (Forward.treeHeight s : ℝ) / Real.log (n : ℝ)}) atTop (𝓝 0) := by
  exact linear_maximum_over_log_upper_tendsto_zero c x hτ
    (linear_heightScale_tendsto x A c.property.1 c.property.2 hA hAinf hsmall hτ hnear hbulk) hη

end Freezing1
