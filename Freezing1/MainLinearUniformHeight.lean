module

public import Freezing1.ForwardUniformHeightTails
public import Freezing1.MainLinearHeightScale
public import Freezing1.CenteredMGFLimits

/-!
# The height of a uniform vertex in the linear regime

The sampling law includes frozen vertices. The proof uses the forward mixture
over birth times: early births have small mass, while a fixed late fraction
has the same logarithmic height scale. This bypasses the reverse birth-law
argument, which remains a separate source obligation.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

theorem tendsto_atTop_of_div_log_tendsto_pos {m : ℕ → ℝ} {K : ℝ}
    (hK : 0 < K) (hm : Tendsto (fun n : ℕ => m n / Real.log (n : ℝ)) atTop (𝓝 K)) :
    Tendsto m atTop atTop := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh := hm.pos_mul_atTop hK hlog
  apply hh.congr'
  filter_upwards [hlog.eventually_gt_atTop 0] with n hn
  field_simp

theorem tendsto_heightScale_floor_div_log {x : ℕ → SignSequence} {K ε : ℝ}
    (hscale : Tendsto (fun n : ℕ => heightScale (x n) n / Real.log (n : ℝ)) atTop (𝓝 K))
    (hbulk : BulkLowerBound x) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => heightScale (x n) (Nat.floor (ε * n)) / Real.log (n : ℝ))
      atTop (𝓝 K) := by
  have hh := hscale.sub (tendsto_bulkLate_heightScale_div_log_zero hbulk hε hε1)
  simp only [sub_zero] at hh
  convert hh using 1
  funext n
  have hi := heightScale_add_heightScaleOn_Ioc (x := x n) (floor_mul_le_self hε1.le n)
  rw [← sub_div]
  congr 1
  linarith

theorem tendsto_exp_neg_mul_bennett {m : ℕ → ℝ} (hm : Tendsto m atTop atTop)
    {α : ℝ} (hα : 0 < α) :
    Tendsto (fun n => Real.exp (-m n * bennettRate α)) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  have hh := tendsto_neg_atTop_atBot.comp (hm.atTop_mul_const (bennettRate_pos hα))
  change Tendsto (fun n => -(m n * bennettRate α)) atTop atBot at hh
  simpa only [neg_mul] using hh

/-- Positive exponential moments of the actual all-vertex law give a Bennett
upper tail, retaining the one edge added at birth. -/
theorem uniform_height_upper_tail (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) < extinctionTime x) (hm : 0 < heightScale x n)
    {t : ℝ} (ht : 0 < t) :
    (Forward.uniformHeightLaw x n).real
      {k | heightScale x n + 1 + t < (k : ℝ)} ≤
      Real.exp (-heightScale x n * bennettRate (t / heightScale x n)) := by
  let m : ℝ := heightScale x n
  let θ : ℝ := Real.log (1 + t / m)
  have hθ : 0 ≤ θ := Real.log_nonneg (by have := div_pos ht hm; dsimp [m] at *; linarith)
  calc
    _ ≤ (Forward.uniformHeightLaw x n).real {k | m + 1 + t ≤ (k : ℝ)} :=
      measureReal_mono (by
        intro k hk
        change m + 1 + t < (k : ℝ) at hk
        change m + 1 + t ≤ (k : ℝ)
        exact hk.le) (measure_ne_top _ _)
    _ ≤ Real.exp (-θ * (m + 1 + t)) *
        mgf (fun k : ℕ => (k : ℝ)) (Forward.uniformHeightLaw x n) θ :=
      measure_ge_le_exp_mul_mgf _ hθ (Forward.uniformHeightLaw_integrable x n _)
    _ ≤ Real.exp (-θ * (m + 1 + t)) * (Real.exp θ * Real.exp (m * (Real.exp θ - 1))) :=
      mul_le_mul_of_nonneg_left (Forward.uniformHeightLaw_mgf_upper x n hτ hθ) (Real.exp_pos _).le
    _ = Real.exp (-θ * (m + t) + m * (Real.exp θ - 1)) := by
      rw [← mul_assoc, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (-m * bennettRate (t / m)) := by
      congr 1
      exact bennett_exponent_identity hm ht

/-- A uniform vertex has an asymptotically negligible upper tail above the
linear-regime constant, using only the deterministic height-scale limit. -/
theorem linear_uniform_height_upper_probability {x : ℕ → SignSequence} {K : ℝ}
    (hK : 0 < K) (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hscale : Tendsto (fun n : ℕ => heightScale (x n) n / Real.log (n : ℝ)) atTop (𝓝 K))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => (Forward.uniformHeightLaw (x n) n).real
      {k | K + δ < (k : ℝ) / Real.log (n : ℝ)}) atTop (𝓝 0) := by
  let α : ℝ := δ / (2 * K)
  have hα : 0 < α := div_pos hδ (by positivity)
  have hm := tendsto_atTop_of_div_log_tendsto_pos hK hscale
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hthresh : Tendsto (fun n : ℕ =>
      (heightScale (x n) n + 1 + α * heightScale (x n) n) / Real.log (n : ℝ))
      atTop (𝓝 (K + δ / 2)) := by
    have hh := (hscale.add ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hlog)).add
      (hscale.const_mul α)
    convert hh using 1
    · funext n
      ring
    · dsimp [α]
      field_simp
      congr 1
      ring
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_
    (tendsto_exp_neg_mul_bennett hm hα)
  filter_upwards [hm.eventually_gt_atTop 0, hlog.eventually_gt_atTop 0,
    hthresh.eventually (gt_mem_nhds (by linarith : K + δ / 2 < K + δ))]
    with n hmn hln hth
  have hb := uniform_height_upper_tail (x n) n (hτ n) hmn (mul_pos hα hmn)
  have heq : α * heightScale (x n) n / heightScale (x n) n = α := by field_simp
  rw [heq] at hb
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hb
  intro k hk
  change K + δ < (k : ℝ) / Real.log (n : ℝ) at hk
  exact (div_lt_div_iff_of_pos_right hln).mp (hth.trans hk)

theorem early_vertex_fraction_le {x : SignSequence} {n l : ℕ}
    (hn : 1 ≤ n) (hs : PositiveThrough x n) :
    ((l : ℝ) + 1) / (plusCount x n + 1 : ℕ) ≤ 2 * ((l : ℝ) + 1) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc : (n : ℝ) ≤ 2 * (plusCount x n : ℝ) := by exact_mod_cast le_two_mul_plusCount hs
  calc
    _ ≤ ((l : ℝ) + 1) / ((n : ℝ) / 2) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      push_cast
      linarith
    _ = _ := by field_simp

/-- The lower tail is controlled by discarding a small initial fraction of
births and comparing all later births to the active law at that cutoff. -/
theorem linear_uniform_height_lower_probability {x : ℕ → SignSequence} {K : ℝ}
    (hK : 0 < K) (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hscale : Tendsto (fun n : ℕ => heightScale (x n) n / Real.log (n : ℝ)) atTop (𝓝 K))
    (hbulk : BulkLowerBound x) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => (Forward.uniformHeightLaw (x n) n).real
      {k | (k : ℝ) / Real.log (n : ℝ) < K - δ}) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  let ε : ℝ := min (1 / 2) (η / 16)
  let α : ℝ := δ / (2 * K)
  let l : ℕ → ℕ := fun n => Nat.floor (ε * n)
  let m : ℕ → ℝ := fun n => heightScale (x n) (l n)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hα : 0 < α := div_pos hδ (by positivity)
  have hcutscale : Tendsto (fun n : ℕ => m n / Real.log (n : ℝ)) atTop (𝓝 K) :=
    tendsto_heightScale_floor_div_log hscale hbulk hε hε1
  have hm := tendsto_atTop_of_div_log_tendsto_pos hK hcutscale
  have he := tendsto_exp_neg_mul_bennett hm hα
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hthresh : Tendsto (fun n : ℕ => (m n - α * m n) / Real.log (n : ℝ))
      atTop (𝓝 (K - δ / 2)) := by
    have hh := hcutscale.sub (hcutscale.const_mul α)
    convert hh using 1
    · funext n
      ring
    · dsimp [α]
      field_simp
  have hfrac : Tendsto (fun n : ℕ => 2 * ((l n : ℝ) + 1) / n) atTop (𝓝 (2 * ε)) := by
    have hh := ((tendsto_floor_mul_div_nat hε.le).add
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))).const_mul 2
    simp only [add_zero] at hh
    convert hh using 1
    funext n
    dsimp [l]
    ring
  have hεη : 2 * ε < η / 4 := by
    have hbound : ε ≤ η / 16 := min_le_right _ _
    linarith
  filter_upwards [eventually_ge_atTop 1, hm.eventually_gt_atTop 0,
    hlog.eventually_gt_atTop 0,
    hthresh.eventually (lt_mem_nhds (by linarith : K - δ < K - δ / 2)),
    hfrac.eventually (gt_mem_nhds hεη),
    he.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η / 4))]
    with n hn hmn hln hth hfr hen
  have hlnn : l n ≤ n := floor_mul_le_self hε1.le n
  have hlτ : (l n : ℕ∞) < extinctionTime (x n) :=
    lt_of_le_of_lt (by exact_mod_cast hlnn) (hτ n)
  have hactive := (bennett_tails_of_mgf_bound
    (Forward.uniformActiveHeightLaw_integrable_exp (x n) (l n))
    (Forward.uniformActiveHeightLaw_mgf_le (x n) (l n) hlτ)
    hmn (mul_pos hα hmn)).2
  have heq : α * m n / m n = α := by field_simp
  change (Forward.uniformActiveHeightLaw (x n) (l n)).real
    {k | (k : ℝ) < m n - α * m n} ≤
      Real.exp (-m n * bennettRate (α * m n / m n)) at hactive
  rw [heq] at hactive
  have hbefore : (K - δ) * Real.log (n : ℝ) < m n - α * m n :=
    (lt_div_iff₀ hln).mp hth
  have hbound : (Forward.uniformHeightLaw (x n) n).real
      {k | (k : ℝ) / Real.log (n : ℝ) < K - δ} ≤
      2 * ((l n : ℝ) + 1) / n + Real.exp (-m n * bennettRate α) := by
    calc
      _ ≤ (Forward.uniformHeightLaw (x n) n).real
          {k | (k : ℝ) ≤ (K - δ) * Real.log (n : ℝ)} :=
        measureReal_mono (fun k hk => ((div_lt_iff₀ hln).mp hk).le) (measure_ne_top _ _)
      _ ≤ ((l n : ℝ) + 1) / (plusCount (x n) n + 1 : ℕ) +
          (Forward.uniformActiveHeightLaw (x n) (l n)).real
            {k | (k : ℝ) ≤ (K - δ) * Real.log (n : ℝ)} :=
        Forward.uniformHeightLaw_lower_tail_le (x n) n (hτ n) hlnn _
      _ ≤ 2 * ((l n : ℝ) + 1) / n + Real.exp (-m n * bennettRate α) := by
        apply add_le_add (early_vertex_fraction_le hn ((lt_extinctionTime_iff (x n) n).mp (hτ n)))
        exact (measureReal_mono (fun _ hk => hk.trans_lt hbefore) (measure_ne_top _ _)).trans hactive
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  linarith

/-- Convergence in probability for a conditionally uniform vertex of the full tree. -/
theorem linear_uniform_height_deviation_tendsto_zero {x : ℕ → SignSequence} {K : ℝ}
    (hK : 0 < K) (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hscale : Tendsto (fun n : ℕ => heightScale (x n) n / Real.log (n : ℝ)) atTop (𝓝 K))
    (hbulk : BulkLowerBound x) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => (Forward.uniformHeightLaw (x n) n)
      {k | δ ≤ |(k : ℝ) / Real.log (n : ℝ) - K|}) atTop (𝓝 0) := by
  apply (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).mp
  have hh := (linear_uniform_height_lower_probability hK hτ hscale hbulk (half_pos hδ)).add
    (linear_uniform_height_upper_probability hK hτ hscale (half_pos hδ))
  simp only [add_zero] at hh
  apply squeeze_zero (fun _ => measureReal_nonneg) ?_ hh
  intro n
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (measureReal_union_le _ _)
  intro k hk
  change δ ≤ |(k : ℝ) / Real.log (n : ℝ) - K| at hk
  change (k : ℝ) / Real.log (n : ℝ) < K - δ / 2 ∨
    K + δ / 2 < (k : ℝ) / Real.log (n : ℝ)
  rcases le_abs.mp hk with hp | hp
  · right; linarith
  · left; linarith

/-- Every real `Lp` limit for the actual uniform all-vertex height, given the
deterministic logarithmic scale and the bulk population lower bound. -/
theorem linear_uniform_height_tendsto_Lp_of_scale {x : ℕ → SignSequence} {K : ℝ}
    (hK : 0 < K) (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hscale : Tendsto (fun n : ℕ => heightScale (x n) n / Real.log (n : ℝ)) atTop (𝓝 K))
    (hbulk : BulkLowerBound x) {r : ℝ} (hr : 1 ≤ r) :
    Tendsto (fun n : ℕ => eLpNorm (fun k : ℕ => (k : ℝ) / Real.log (n : ℝ) - K)
      (ENNReal.ofReal r) (Forward.uniformHeightLaw (x n) n)) atTop (𝓝 0) := by
  let B : ℝ := (Real.exp 1 - 1) * (K + 1) + 1
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply centered_tendsto_Lp_of_eventual_exp_bound
    (B := B) (fun _ => measurable_of_countable _)
    (fun n _ => Forward.uniformHeightLaw_integrable (x n) n _)
    (fun _ => Eventually.of_forall fun k => Nat.cast_nonneg k) ?_ hlog
    (fun _ hδ => linear_uniform_height_deviation_tendsto_zero hK hτ hscale hbulk hδ) hr
  filter_upwards [hlog.eventually_ge_atTop 1,
    hscale.eventually (gt_mem_nhds (lt_add_one K))] with n hln hrat
  have hln0 : 0 < Real.log (n : ℝ) := by linarith
  have hm : heightScale (x n) n ≤ (K + 1) * Real.log (n : ℝ) :=
    (div_le_iff₀ hln0).mp hrat.le
  have he : 0 ≤ Real.exp 1 - 1 := sub_nonneg.mpr (Real.one_le_exp zero_le_one)
  have hmul := mul_le_mul_of_nonneg_right hm he
  calc
    _ ≤ Real.exp 1 * Real.exp (heightScale (x n) n * (Real.exp 1 - 1)) :=
      Forward.uniformHeightLaw_mgf_upper (x n) n (hτ n) zero_le_one
    _ = Real.exp (1 + heightScale (x n) n * (Real.exp 1 - 1)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (B * Real.log (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      dsimp [B]
      nlinarith

/-- The height assertion of Theorem `thm:lineaire` (II), for a vertex sampled
conditionally uniformly from all vertices of the actual forward tree. -/
theorem linear_uniform_height_tendsto_Lp
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x)
    {r : ℝ} (hr : 1 ≤ r) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun k : ℕ => (k : ℝ) / Real.log (n : ℝ) - (c + 1) / (2 * c))
      (ENNReal.ofReal r) (Forward.uniformHeightLaw (x n) n)) atTop (𝓝 0) := by
  have hs : ∀ n, PositiveThrough (x n) n :=
    fun n => (lt_extinctionTime_iff (x n) n).mp (hτ n)
  exact linear_uniform_height_tendsto_Lp_of_scale (by positivity) hτ
    (linear_heightScale_tendsto x A hc hc1 hA hAinf hsmall hτ hnear hbulk)
    ((bulkLiminf_iff x hs).mp hbulk) hr

end Freezing1
